//! The constant `T`, the theorem `⊢ T`, and three equations about equality —
//! every one of them derived from the ten rules, with no axiom anywhere.
//!
//! Ported from adamas's `lib/adamas/booleans.rb`. Nothing here is trusted: it
//! calls the public rules on a [`Kernel`] and nothing else, so a mistake in
//! this file is a failed proof, never a false theorem.

use crate::kernel::{Kernel, Result, Term, TheoryId, Thm};

/// What [`Kernel::install_booleans`] leaves in a theory.
#[derive(Clone)]
pub struct Booleans {
    /// `⊢ T = ((λp. p) = (λp. p))`, the defining equation.
    pub definition: Thm,
    /// The constant `T`.
    pub true_const: Term,
    /// `⊢ T`.
    pub truth: Thm,
    /// `⊢ (x = x) = T`, at the type variable `A`.
    pub refl_is_true: Thm,
    /// `⊢ (T = p) = p`.
    pub true_left: Thm,
    /// `⊢ (p = T) = p`.
    pub true_right: Thm,
}

impl Kernel {
    /// Declare `T` in `theory`, prove what can be proved about it, and return
    /// the lot.
    ///
    /// HOL Light's own first definition: truth is the proposition that the
    /// identity function on booleans is itself.
    pub fn install_booleans(&mut self, theory: TheoryId) -> Result<Booleans> {
        let bool_ty = self.bool_ty();

        let proposition = self.term_var("p", bool_ty)?;
        let identity = self.term_abs(proposition, proposition)?;

        // HOL Light's own first definition: truth is the proposition that the
        // identity function on booleans is itself.
        let t_var = self.term_var("T", bool_ty)?;
        let identity_eq = self.term_eq(identity, identity)?;
        let definition_term = self.term_eq(t_var, identity_eq)?;
        let definition = self.new_basic_definition(theory, definition_term)?;
        let true_const = self.constant(theory, "T", None)?;

        // ⊢ T, by reading the definition backwards against `⊢ (λp. p) = (λp. p)`.
        let sym_def = self.sym(theory, &definition)?;
        let refl_identity = self.refl(theory, identity)?;
        let truth = self.eq_mp(theory, &sym_def, &refl_identity)?;

        let refl_is_true = self.reflexive_is_true(theory, &truth)?;
        let true_left = self.true_on_the_left(theory, &truth, true_const, proposition)?;
        let true_right = self.true_on_the_right(theory, &truth, true_const, proposition)?;

        Ok(Booleans {
            definition,
            true_const,
            truth,
            refl_is_true,
            true_left,
            true_right,
        })
    }

    /// `⊢ (x = x) = T`. Two theorems with no hypotheses entail each other for
    /// free, so DEDUCT_ANTISYM_RULE turns them straight into an equation.
    fn reflexive_is_true(&mut self, theory: TheoryId, truth: &Thm) -> Result<Thm> {
        let a = self.ty_var("A")?;
        let x = self.term_var("x", a)?;
        let reflexivity = self.refl(theory, x)?;
        self.deduct_antisym_rule(theory, &reflexivity, truth)
    }

    /// `⊢ (T = p) = p`.
    ///
    ///   T = p ⊢ p      from the assumption and ⊢ T, by EQ_MP
    ///   p ⊢ T = p      from the assumption and ⊢ T, by DEDUCT and SYM
    ///   ⊢ p = (T = p)  each discharges the other's conclusion
    fn true_on_the_left(
        &mut self,
        theory: TheoryId,
        truth: &Thm,
        true_const: Term,
        proposition: Term,
    ) -> Result<Thm> {
        let t_eq_p = self.term_eq(true_const, proposition)?;
        let assumed_t_eq_p = self.assume(theory, t_eq_p)?;
        let forwards = self.eq_mp(theory, &assumed_t_eq_p, truth)?;
        let assumed_prop = self.assume(theory, proposition)?;
        let ded_t = self.deduct_antisym_rule(theory, &assumed_prop, truth)?;
        let backwards = self.sym(theory, &ded_t)?;
        let ded = self.deduct_antisym_rule(theory, &forwards, &backwards)?;
        self.sym(theory, &ded)
    }

    /// `⊢ (p = T) = p`, the same argument with the assumption turned around.
    fn true_on_the_right(
        &mut self,
        theory: TheoryId,
        truth: &Thm,
        true_const: Term,
        proposition: Term,
    ) -> Result<Thm> {
        let p_eq_t = self.term_eq(proposition, true_const)?;
        let assumed_p_eq_t = self.assume(theory, p_eq_t)?;
        let sym_assumed = self.sym(theory, &assumed_p_eq_t)?;
        let forwards = self.eq_mp(theory, &sym_assumed, truth)?;
        let assumed_prop = self.assume(theory, proposition)?;
        let backwards = self.deduct_antisym_rule(theory, &assumed_prop, truth)?;
        let ded = self.deduct_antisym_rule(theory, &forwards, &backwards)?;
        self.sym(theory, &ded)
    }
}
