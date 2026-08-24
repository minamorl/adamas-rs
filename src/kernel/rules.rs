//! The gates and the ten primitive rules. Ported from `lib/adamas/theory.rb`.
//!
//! This module is a child of `kernel`, so it can reach [`Thm`]'s private
//! fields through [`Kernel::sequent`]. Nothing outside `kernel` can.

use std::collections::BTreeMap;

use super::term::TermNode;
use super::{Error, Kernel, Result, TheoryId, Thm, TypeDefinition};
use super::{Term, Ty};

impl Kernel {
    // --- using and declaring constants -------------------------------------

    /// The constant `name` at `instance`, or at its declared type if `instance`
    /// is `None`. A constant may only be used at an instance of the type it was
    /// declared with — otherwise `=` could be used at `A → B → bool` and stop
    /// meaning equality.
    pub fn constant(&mut self, theory: TheoryId, name: &str, instance: Option<Ty>) -> Result<Term> {
        let declared = *self.theories[theory.0 as usize]
            .constants
            .get(name)
            .ok_or_else(|| Error::Theory(format!("no such constant: {name}")))?;
        let Some(instance) = instance else {
            return self.const_raw(name, declared);
        };
        if self.ty_match(declared, instance, BTreeMap::new()).is_none() {
            return Err(Error::Theory(format!(
                "{name} is declared at {}; {} is not an instance",
                self.ty_to_string(declared),
                self.ty_to_string(instance)
            )));
        }
        self.const_raw(name, instance)
    }

    pub fn has_constant(&self, theory: TheoryId, name: &str) -> bool {
        self.theories[theory.0 as usize]
            .constants
            .contains_key(name)
    }

    // --- the gates: ways to make a theorem out of nothing -------------------
    //
    // Everything else here derives a theorem from theorems. These gates do not,
    // which is exactly why they are gated and why they are so short: each one is
    // a place where a mistake becomes a false theorem rather than a failed
    // proof.

    /// Declare a constant with no defining property. Sound, but it grows the
    /// signature; `new_basic_definition` is nearly always what you want.
    pub fn new_constant(&mut self, theory: TheoryId, name: &str, ty: Ty) -> Result<Term> {
        if self.has_constant(theory, name) {
            return Err(Error::Theory(format!(
                "constant {name} is already declared"
            )));
        }
        self.theories[theory.0 as usize]
            .constants
            .insert(name.to_string(), ty);
        self.const_raw(name, ty)
    }

    /// Assert `term` without proof. The one operation in the library that can
    /// make a theory inconsistent.
    pub fn new_axiom(&mut self, theory: TheoryId, term: Term) -> Result<Thm> {
        if !self.is_proposition(term) {
            return Err(Error::Theory(format!(
                "an axiom must be a closed proposition: {}",
                self.term_to_string(term)
            )));
        }
        let thm = self.sequent(theory, Vec::new(), term)?;
        self.theories[theory.0 as usize].axioms.push(thm.clone());
        Ok(thm)
    }

    /// From `c = r`, with `c` a *variable* standing for the constant to be
    /// introduced, declare `c` and return `⊢ c = r`.
    ///
    /// Conservative, but only because of the two conditions below. If `r` had a
    /// free variable, the "definition" would constrain that variable. If `r`
    /// mentioned a type variable absent from `c`'s type, one constant would be
    /// defined differently at different types, which is a genuine new
    /// assumption.
    pub fn new_basic_definition(&mut self, theory: TheoryId, term: Term) -> Result<Thm> {
        let Some((lhs, rhs)) = self.dest_eq(term) else {
            return Err(Error::Theory(format!(
                "a definition must be an equation, got {}",
                self.term_to_string(term)
            )));
        };
        let TermNode::Var { name, ty } = self.term_node(lhs).clone() else {
            return Err(Error::Theory(format!(
                "the left side must be a variable, got {}",
                self.term_to_string(lhs)
            )));
        };
        if !self.frees(rhs).is_empty() {
            return Err(Error::Theory(format!(
                "the right side must be closed, got {}",
                self.term_to_string(rhs)
            )));
        }
        let reflected = self.ty_vars(ty).to_vec();
        if !self
            .term_type_vars(rhs)
            .iter()
            .all(|v| reflected.contains(v))
        {
            return Err(Error::Theory(format!(
                "{} has type variables that {} does not reflect",
                self.term_to_string(rhs),
                self.ty_to_string(ty)
            )));
        }
        let c = self.new_constant(theory, &name, ty)?;
        let eq = self.term_eq(c, rhs)?;
        let thm = self.sequent(theory, Vec::new(), eq)?;
        self.theories[theory.0 as usize]
            .definitions
            .push(thm.clone());
        Ok(thm)
    }

    /// From `⊢ P x` — the witness that `P` carves a non-empty part out of `x`'s
    /// type — declare a new type constructor isomorphic to that part, with
    /// `abs`/`rep` as the bijection. Returns
    ///
    /// ```text
    /// ⊢ abs (rep a) = a
    /// ⊢ P r = (rep (abs r) = r)
    /// ```
    ///
    /// The type's arguments are `P`'s type variables sorted by *name* — never
    /// by rank, which is process-local and would make the same definition mean
    /// different types in different processes.
    pub fn new_basic_type_definition(
        &mut self,
        theory: TheoryId,
        type_name: &str,
        abs_name: &str,
        rep_name: &str,
        witness: &Thm,
    ) -> Result<(Thm, Thm)> {
        self.own(theory, witness)?;
        if !witness.hyps().is_empty() {
            return Err(Error::Theory(format!(
                "the witness must have no hypotheses: {}",
                self.thm_to_string(witness)
            )));
        }
        let TermNode::Comb {
            rator: predicate,
            rand: representative,
        } = self.term_node(witness.concl()).clone()
        else {
            return Err(Error::Theory(format!(
                "the witness must conclude P x, got {}",
                self.term_to_string(witness.concl())
            )));
        };
        if !self.frees(predicate).is_empty() {
            return Err(Error::Theory(format!(
                "the predicate must be closed, got {}",
                self.term_to_string(predicate)
            )));
        }
        if abs_name == rep_name {
            return Err(Error::Theory(format!(
                "abs and rep must be distinct constants, both are {abs_name}"
            )));
        }
        for n in [abs_name, rep_name] {
            if self.has_constant(theory, n) {
                return Err(Error::Theory(format!("constant {n} is already declared")));
            }
        }

        // Checks are done; the registry write comes first because it is the one
        // mutation that can refuse, and nothing fallible may follow a mutation.
        let mut arguments = self.term_type_vars(predicate);
        arguments.sort_by_key(|t| self.ty_to_string(*t));
        self.new_type(type_name, arguments.len())?;
        let carved = self.ty_con(type_name, &arguments)?;
        let rep_type = self.type_of(representative);
        let abs_ty = self.ty_fun(rep_type, carved)?;
        let rep_ty = self.ty_fun(carved, rep_type)?;
        let abs = self.new_constant(theory, abs_name, abs_ty)?;
        let rep = self.new_constant(theory, rep_name, rep_ty)?;

        // `a` and `r` are free variables, as in `fusion.ml` — callers
        // instantiate them with INST.
        let a = self.term_var("a", carved)?;
        let r = self.term_var("r", rep_type)?;
        let rep_a = self.term_comb(rep, a)?;
        let abs_rep_a = self.term_comb(abs, rep_a)?;
        let abs_rep_concl = self.term_eq(abs_rep_a, a)?;
        let abs_rep = self.sequent(theory, Vec::new(), abs_rep_concl)?;

        let p_r = self.term_comb(predicate, r)?;
        let abs_r = self.term_comb(abs, r)?;
        let rep_abs_r = self.term_comb(rep, abs_r)?;
        let inner = self.term_eq(rep_abs_r, r)?;
        let rep_abs_concl = self.term_eq(p_r, inner)?;
        let rep_abs = self.sequent(theory, Vec::new(), rep_abs_concl)?;

        self.theories[theory.0 as usize]
            .type_definitions
            .push(TypeDefinition {
                type_name: type_name.to_string(),
                abs_rep: abs_rep.clone(),
                rep_abs: rep_abs.clone(),
            });
        Ok((abs_rep, rep_abs))
    }

    // --- the ten primitive rules -------------------------------------------

    /// `⊢ t = t`
    pub fn refl(&mut self, theory: TheoryId, term: Term) -> Result<Thm> {
        let term = match self.closed(term) {
            true => term,
            false => {
                return Err(Error::Rule(format!(
                    "REFL: term has a dangling de Bruijn index: {}",
                    self.term_to_string(term)
                )))
            }
        };
        let eq = self.term_eq(term, term)?;
        self.sequent(theory, Vec::new(), eq)
    }

    /// ```text
    /// Γ ⊢ l = m    Δ ⊢ m = r
    /// ──────────────────────
    ///     Γ ∪ Δ ⊢ l = r
    /// ```
    pub fn trans(&mut self, theory: TheoryId, left: &Thm, right: &Thm) -> Result<Thm> {
        let (lhs, mid) = self.dest_equation(theory, left, "TRANS")?;
        let (mid_again, rhs) = self.dest_equation(theory, right, "TRANS")?;
        if mid != mid_again {
            return Err(Error::Rule(format!(
                "TRANS: {} and {} are not the same term",
                self.term_to_string(mid),
                self.term_to_string(mid_again)
            )));
        }
        let concl = self.term_eq(lhs, rhs)?;
        let hyps = union(left, right);
        self.sequent(theory, hyps, concl)
    }

    /// ```text
    /// Γ ⊢ f = g    Δ ⊢ x = y
    /// ──────────────────────
    ///   Γ ∪ Δ ⊢ f x = g y
    /// ```
    pub fn mk_comb(&mut self, theory: TheoryId, fun_thm: &Thm, arg_thm: &Thm) -> Result<Thm> {
        let (f, g) = self.dest_equation(theory, fun_thm, "MK_COMB")?;
        let (x, y) = self.dest_equation(theory, arg_thm, "MK_COMB")?;
        let left = self.term_comb(f, x)?;
        let right = self.term_comb(g, y)?;
        let concl = self.term_eq(left, right)?;
        let hyps = union(fun_thm, arg_thm);
        self.sequent(theory, hyps, concl)
    }

    /// ```text
    ///       Γ ⊢ s = t                (v not free in Γ)
    /// ────────────────────────
    /// Γ ⊢ (λv. s) = (λv. t)
    /// ```
    ///
    /// The side condition is the whole content of the rule: without it, one
    /// could generalise over a variable the hypotheses have already pinned
    /// down.
    pub fn abs(&mut self, theory: TheoryId, var: Term, thm: &Thm) -> Result<Thm> {
        if !self.is_var(var) {
            return Err(Error::Rule(format!(
                "ABS: {} is not a variable",
                self.term_to_string(var)
            )));
        }
        let (lhs, rhs) = self.dest_equation(theory, thm, "ABS")?;
        if thm.hyps().iter().any(|h| self.free_in(var, *h)) {
            return Err(Error::Rule(format!(
                "ABS: {} is free in a hypothesis",
                self.term_to_string(var)
            )));
        }
        let left = self.term_abs(var, lhs)?;
        let right = self.term_abs(var, rhs)?;
        let concl = self.term_eq(left, right)?;
        self.sequent(theory, thm.hyps().to_vec(), concl)
    }

    /// `⊢ (λv. t) v = t`
    ///
    /// Only the trivial redex, as in `fusion.ml` — the argument must be a
    /// variable of the binder's type. Since a de Bruijn binder has no name of
    /// its own, "the same variable as the binder" is any variable at its type.
    pub fn beta(&mut self, theory: TheoryId, term: Term) -> Result<Thm> {
        let refusal = || {
            Error::Rule(format!(
                "BETA: not a trivial beta-redex: {}",
                self.term_to_string(term)
            ))
        };
        let TermNode::Comb { rator, rand } = self.term_node(term).clone() else {
            return Err(refusal());
        };
        let TermNode::Abs { binder_type, .. } = self.term_node(rator).clone() else {
            return Err(refusal());
        };
        if !self.is_var(rand) || binder_type != self.type_of(rand) {
            return Err(refusal());
        }
        let opened = self.open_abs(rator, rand)?;
        let concl = self.term_eq(term, opened)?;
        self.sequent(theory, Vec::new(), concl)
    }

    /// `p ⊢ p`
    pub fn assume(&mut self, theory: TheoryId, term: Term) -> Result<Thm> {
        if !self.is_proposition(term) {
            return Err(Error::Rule(format!(
                "ASSUME: {} is not a closed proposition",
                self.term_to_string(term)
            )));
        }
        self.sequent(theory, vec![term], term)
    }

    /// ```text
    /// Γ ⊢ p = q    Δ ⊢ p
    /// ──────────────────
    ///     Γ ∪ Δ ⊢ q
    /// ```
    pub fn eq_mp(&mut self, theory: TheoryId, eq_thm: &Thm, thm: &Thm) -> Result<Thm> {
        let (lhs, rhs) = self.dest_equation(theory, eq_thm, "EQ_MP")?;
        self.own(theory, thm)?;
        if lhs != thm.concl() {
            return Err(Error::Rule(format!(
                "EQ_MP: {} is not {}",
                self.term_to_string(thm.concl()),
                self.term_to_string(lhs)
            )));
        }
        let hyps = union(eq_thm, thm);
        self.sequent(theory, hyps, rhs)
    }

    /// ```text
    ///     Γ ⊢ p         Δ ⊢ q
    /// ────────────────────────────
    /// (Γ - q) ∪ (Δ - p) ⊢ p = q
    /// ```
    ///
    /// Two propositions that entail each other are equal. This is where
    /// hypotheses get discharged, and so where implication is eventually built.
    pub fn deduct_antisym_rule(
        &mut self,
        theory: TheoryId,
        left: &Thm,
        right: &Thm,
    ) -> Result<Thm> {
        self.own(theory, left)?;
        self.own(theory, right)?;
        let mut hyps: Vec<Term> = left
            .hyps()
            .iter()
            .copied()
            .filter(|h| *h != right.concl())
            .collect();
        hyps.extend(right.hyps().iter().copied().filter(|h| *h != left.concl()));
        let concl = self.term_eq(left.concl(), right.concl())?;
        self.sequent(theory, hyps, concl)
    }

    /// ```text
    /// Γ ⊢ p
    /// ─────────────  (θ maps variables to terms of their type)
    /// θΓ ⊢ θp
    /// ```
    pub fn inst(
        &mut self,
        theory: TheoryId,
        theta: &BTreeMap<Term, Term>,
        thm: &Thm,
    ) -> Result<Thm> {
        self.check_subst(theta)?;
        self.own(theory, thm)?;
        let mut hyps = Vec::with_capacity(thm.hyps().len());
        for h in thm.hyps() {
            hyps.push(self.subst(theta, *h)?);
        }
        let concl = self.subst(theta, thm.concl())?;
        self.sequent(theory, hyps, concl)
    }

    /// ```text
    /// Γ ⊢ p
    /// ─────────────  (θ maps type variables to types)
    /// θΓ ⊢ θp
    /// ```
    pub fn inst_type(
        &mut self,
        theory: TheoryId,
        theta: &BTreeMap<Ty, Ty>,
        thm: &Thm,
    ) -> Result<Thm> {
        self.check_ty_subst(theta)?;
        self.own(theory, thm)?;
        let mut hyps = Vec::with_capacity(thm.hyps().len());
        for h in thm.hyps() {
            hyps.push(self.inst_type_term(theta, *h)?);
        }
        let concl = self.inst_type_term(theta, thm.concl())?;
        self.sequent(theory, hyps, concl)
    }

    // --- helpers -----------------------------------------------------------

    fn dest_equation(&mut self, theory: TheoryId, thm: &Thm, rule: &str) -> Result<(Term, Term)> {
        self.own(theory, thm)?;
        self.dest_eq(thm.concl()).ok_or_else(|| {
            Error::Rule(format!(
                "{rule}: {} is not an equation",
                self.term_to_string(thm.concl())
            ))
        })
    }
}

fn union(left: &Thm, right: &Thm) -> Vec<Term> {
    let mut hyps = left.hyps().to_vec();
    hyps.extend_from_slice(right.hyps());
    hyps
}
