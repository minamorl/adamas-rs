//! Universal quantification, defined over the frozen kernel.
//!
//! Ported from adamas's `lib/adamas/logic/universal.rb`. `∀P` says that `P` is
//! the constantly-true predicate, so specialisation is application and
//! generalisation is abstraction — with `eqt_intro` and `eqt_elim` doing the
//! translation between `p` and `p = T` at each end.

use crate::kernel::{Kernel, Result, Term, TheoryId, Thm};

impl Kernel {
    /// `⊢ ∀ = (λP. P = (λx. T))`, at the type variable `A`.
    pub fn define_universal(&mut self, theory: TheoryId, truth: &Thm) -> Result<Thm> {
        todo!("port Universal.define")
    }

    /// `Γ ⊢ ∀x. p[x]` gives `Γ ⊢ p[t]`.
    pub fn spec(
        &mut self,
        theory: TheoryId,
        definition: &Thm,
        truth: &Thm,
        thm: &Thm,
        term: Term,
    ) -> Result<Thm> {
        todo!("port Universal.spec")
    }

    /// `Γ ⊢ p[x]` gives `Γ ⊢ ∀x. p[x]`, provided `x` is free in no hypothesis.
    pub fn gen(
        &mut self,
        theory: TheoryId,
        definition: &Thm,
        true_right: &Thm,
        var: Term,
        thm: &Thm,
    ) -> Result<Thm> {
        todo!("port Universal.gen")
    }
}
