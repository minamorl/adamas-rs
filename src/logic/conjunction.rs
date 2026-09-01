//! Conjunction, defined over the frozen kernel.
//!
//! Ported from adamas's `lib/adamas/logic/conjunction.rb`. `∧` is HOL Light's
//! encoding: `p ∧ q` says that the pair-selector `λf. f p q` is the selector
//! `λf. f T T`, so the two projections fall out of applying it to `λx y. x`
//! and `λx y. y`.

use crate::kernel::{Error, Kernel, Result, Term, TheoryId, Thm, Ty};

impl Kernel {
    /// `⊢ ∧ = (λp q. (λf. f p q) = (λf. f T T))`.
    pub fn define_conjunction(&mut self, theory: TheoryId, truth: &Thm) -> Result<Thm> {
        let ty = self.conjunction_type()?;
        let lhs = self.term_var("∧", ty)?;
        let rhs = self.conjunction_rhs(truth.concl())?;
        let equation = self.term_eq(lhs, rhs)?;
        self.new_basic_definition(theory, equation)
    }

    /// `Γ ⊢ p` and `Δ ⊢ q` give `Γ ∪ Δ ⊢ p ∧ q`.
    pub fn conj(
        &mut self,
        theory: TheoryId,
        definition: &Thm,
        true_right: &Thm,
        left: &Thm,
        right: &Thm,
    ) -> Result<Thm> {
        let left_eq_truth = self.eqt_intro(theory, true_right, left)?;
        let right_eq_truth = self.eqt_intro(theory, true_right, right)?;

        let mut avoid = self.frees(left.concl()).to_vec();
        avoid.extend_from_slice(self.frees(right.concl()));
        for hyp in left.hyps().iter().chain(right.hyps()) {
            avoid.extend_from_slice(self.frees(*hyp));
        }
        let ty = self.conjunction_type()?;
        let witness = self.variant(&avoid, "f", ty)?;

        let seed = self.refl(theory, witness)?;
        let half = self.mk_comb(theory, &seed, &left_eq_truth)?;
        let whole = self.mk_comb(theory, &half, &right_eq_truth)?;
        let encoded = self.abs(theory, witness, &whole)?;

        let unfolded =
            self.conjunction_unfolded(theory, definition, left.concl(), right.concl())?;
        let backwards = self.sym(theory, &unfolded)?;
        self.eq_mp(theory, &backwards, &encoded)
    }

    /// `Γ ⊢ p ∧ q` gives `Γ ⊢ p`.
    pub fn conjunct1(
        &mut self,
        theory: TheoryId,
        definition: &Thm,
        truth: &Thm,
        thm: &Thm,
    ) -> Result<Thm> {
        let selector = self.selector(true)?;
        self.project(theory, definition, truth, thm, selector)
    }

    /// `Γ ⊢ p ∧ q` gives `Γ ⊢ q`.
    pub fn conjunct2(
        &mut self,
        theory: TheoryId,
        definition: &Thm,
        truth: &Thm,
        thm: &Thm,
    ) -> Result<Thm> {
        let selector = self.selector(false)?;
        self.project(theory, definition, truth, thm, selector)
    }

    // --- the encoding ------------------------------------------------------

    fn conjunction_type(&mut self) -> Result<Ty> {
        let bool_ty = self.bool_ty();
        let inner = self.ty_fun(bool_ty, bool_ty)?;
        self.ty_fun(bool_ty, inner)
    }

    fn conjunction_rhs(&mut self, true_const: Term) -> Result<Term> {
        let bool_ty = self.bool_ty();
        let ty = self.conjunction_type()?;
        let p = self.term_var("p", bool_ty)?;
        let q = self.term_var("q", bool_ty)?;
        let f = self.term_var("f", ty)?;

        let applied = self.applied_selector(f, p, q)?;
        let constant = self.applied_selector(f, true_const, true_const)?;
        let left = self.term_abs(f, applied)?;
        let right = self.term_abs(f, constant)?;
        let body = self.term_eq(left, right)?;
        let inner = self.term_abs(q, body)?;
        self.term_abs(p, inner)
    }

    /// `f a b`.
    fn applied_selector(&mut self, f: Term, a: Term, b: Term) -> Result<Term> {
        let half = self.term_comb(f, a)?;
        self.term_comb(half, b)
    }

    /// `λx y. x` when `first`, `λx y. y` otherwise.
    fn selector(&mut self, first: bool) -> Result<Term> {
        let bool_ty = self.bool_ty();
        let x = self.term_var("x", bool_ty)?;
        let y = self.term_var("y", bool_ty)?;
        let body = if first { x } else { y };
        let inner = self.term_abs(y, body)?;
        self.term_abs(x, inner)
    }

    /// `⊢ p ∧ q = ((λf. f p q) = (λf. f T T))`, the definition applied to both
    /// sides and beta-reduced.
    fn conjunction_unfolded(
        &mut self,
        theory: TheoryId,
        definition: &Thm,
        left: Term,
        right: Term,
    ) -> Result<Thm> {
        let half = self.ap_thm(theory, definition, left)?;
        let half = self.normalise(theory, half)?;
        let whole = self.ap_thm(theory, &half, right)?;
        self.normalise(theory, whole)
    }

    fn project(
        &mut self,
        theory: TheoryId,
        definition: &Thm,
        truth: &Thm,
        thm: &Thm,
        selector: Term,
    ) -> Result<Thm> {
        let Some((left, right)) = self.dest_conj(thm.concl()) else {
            return Err(Error::Rule(format!(
                "CONJUNCT: {} is not a conjunction",
                self.term_to_string(thm.concl())
            )));
        };
        let unfolded = self.conjunction_unfolded(theory, definition, left, right)?;
        let encoded = self.eq_mp(theory, &unfolded, thm)?;
        let applied = self.ap_thm(theory, &encoded, selector)?;
        let selected = self.normalise(theory, applied)?;
        self.eqt_elim(theory, truth, &selected)
    }

    /// Beta-reduce to a fixed point. One `beta_rule` reduces the outermost
    /// redexes; applying a definition twice leaves more underneath.
    pub(crate) fn normalise(&mut self, theory: TheoryId, mut thm: Thm) -> Result<Thm> {
        loop {
            let reduced = self.beta_rule(theory, &thm)?;
            if reduced.concl() == thm.concl() {
                return Ok(thm);
            }
            thm = reduced;
        }
    }
}
