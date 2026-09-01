//! Rules derived from the ten. Ported from `lib/adamas/derived.rb`.
//!
//! Nothing here is trusted. Every function is a composition of the primitives,
//! so a mistake in this file is a failed proof, never a false theorem — and
//! because it lives outside `kernel`, the compiler enforces that: these
//! functions cannot reach `Thm`'s fields any more than a stranger's code can.

use crate::kernel::Term;
use crate::kernel::{Error, Kernel, Result, TermNode, TheoryId, Thm};

impl Kernel {
    /// `Γ ⊢ b = a` from `Γ ⊢ a = b`.
    pub fn sym(&mut self, theory: TheoryId, thm: &Thm) -> Result<Thm> {
        let Some((lhs, _)) = self.dest_eq(thm.concl()) else {
            return Err(Error::Rule(format!(
                "SYM: {} is not an equation",
                self.term_to_string(thm.concl())
            )));
        };
        // The `=` at the operand type, dug out of the conclusion itself.
        let TermNode::Comb { rator: inner, .. } = self.term_node(thm.concl()).clone() else {
            return Err(Error::Rule("SYM: malformed equation".into()));
        };
        let TermNode::Comb {
            rator: equality, ..
        } = self.term_node(inner).clone()
        else {
            return Err(Error::Rule("SYM: malformed equation".into()));
        };
        let reflexive = self.refl(theory, lhs)?;
        let eq_refl = self.refl(theory, equality)?;
        let half = self.mk_comb(theory, &eq_refl, thm)?;
        let congruence = self.mk_comb(theory, &half, &reflexive)?;
        self.eq_mp(theory, &congruence, &reflexive)
    }

    /// `Γ ⊢ f x = f y` from `Γ ⊢ x = y`.
    pub fn ap_term(&mut self, theory: TheoryId, func: Term, thm: &Thm) -> Result<Thm> {
        let r = self.refl(theory, func)?;
        self.mk_comb(theory, &r, thm)
    }

    /// `Γ ⊢ f x = g x` from `Γ ⊢ f = g`.
    pub fn ap_thm(&mut self, theory: TheoryId, thm: &Thm, arg: Term) -> Result<Thm> {
        let r = self.refl(theory, arg)?;
        self.mk_comb(theory, thm, &r)
    }

    /// Discharge `p` from `Δ ⊢ q` given `Γ ⊢ p`: `Γ ∪ (Δ - p) ⊢ q`.
    pub fn prove_hyp(&mut self, theory: TheoryId, proof: &Thm, consequence: &Thm) -> Result<Thm> {
        let deduced = self.deduct_antisym_rule(theory, proof, consequence)?;
        self.eq_mp(theory, &deduced, proof)
    }

    /// `Γ ⊢ p = T` ⟹ `Γ ⊢ p`.
    pub fn eqt_elim(&mut self, theory: TheoryId, truth: &Thm, thm: &Thm) -> Result<Thm> {
        let symmetric = self.sym(theory, thm)?;
        self.eq_mp(theory, &symmetric, truth)
    }

    /// True when `term` is a beta-redex, `(λx. t) s`.
    pub fn is_beta_redex(&self, term: Term) -> bool {
        todo!("port Derived.beta_redex?")
    }

    /// Beta for an arbitrary argument: `⊢ (λx. t) s = t[x := s]`.
    ///
    /// The kernel's [`Kernel::beta`] only relates `(λx. t) v` to `t` for a
    /// variable `v`, just as `fusion.ml` does. The general case is this:
    /// beta-reduce against a fresh variable, then instantiate that variable to
    /// the real argument.
    pub fn beta_conv(&mut self, theory: TheoryId, term: Term) -> Result<Thm> {
        todo!("port Derived.beta_conv")
    }

    /// `⊢ t = t'` where `t'` is `t` with every beta-redex reduced, outermost
    /// first. Built by congruence out of [`Kernel::beta_conv`], so it is a
    /// proof, not a rewrite someone has to be trusted about.
    pub fn beta_reduce(&mut self, theory: TheoryId, term: Term) -> Result<Thm> {
        todo!("port Derived.beta_reduce")
    }

    /// `Γ ⊢ p` ⟹ `Γ ⊢ p'`, where `p'` is the beta-normal form of `p`.
    pub fn beta_rule(&mut self, theory: TheoryId, thm: &Thm) -> Result<Thm> {
        todo!("port Derived.beta_rule")
    }

    /// `Γ ⊢ p` ⟹ `Γ ⊢ p = T`, using an instance of `⊢ (p = T) = p`.
    pub fn eqt_intro(&mut self, theory: TheoryId, true_right: &Thm, thm: &Thm) -> Result<Thm> {
        todo!("port Derived.eqt_intro")
    }

    /// `⊢ t = t` refined by reducing inside `t`.
    fn congruence(&mut self, theory: TheoryId, term: Term) -> Result<Thm> {
        todo!("port Derived.congruence")
    }
}
