//! Falsity, defined through universal quantification.
//!
//! This is a direct port of adamas's `lib/adamas/logic/falsity.rb`: `F` is
//! `∀p. p`, and contradiction elimination is ordinary specialisation.

use crate::kernel::{Kernel, Result, Term, TheoryId, Thm};

/// The theorems used by falsity elimination.
#[derive(Clone)]
pub struct FalsityRules {
    /// `⊢ F = (∀p. p)`.
    pub definition: Thm,
    /// The definition of `∀`.
    pub universal_definition: Thm,
    /// `⊢ T`.
    pub truth: Thm,
}

impl Kernel {
    /// Define `F` as `∀p. p` using `new_basic_definition`.
    pub fn define_falsity(&mut self, theory: TheoryId) -> Result<Thm> {
        let bool_ty = self.bool_ty();
        let lhs = self.term_var("F", bool_ty)?;
        let p = self.term_var("p", bool_ty)?;
        let rhs = self.mk_forall(theory, p, p)?;
        let equation = self.term_eq(lhs, rhs)?;
        self.new_basic_definition(theory, equation)
    }

    /// `Γ ⊢ F` gives `Γ ⊢ proposition`.
    pub fn contr(
        &mut self,
        theory: TheoryId,
        rules: &FalsityRules,
        thm: &Thm,
        proposition: Term,
    ) -> Result<Thm> {
        let universal = self.eq_mp(theory, &rules.definition, thm)?;
        self.spec(
            theory,
            &rules.universal_definition,
            &rules.truth,
            &universal,
            proposition,
        )
    }
}
