//! Conjunction, defined over the frozen kernel.
//!
//! Ported from adamas's `lib/adamas/logic/conjunction.rb`. `∧` is HOL Light's
//! encoding: `p ∧ q` says that the pair-selector `λf. f p q` is the selector
//! `λf. f T T`, so the two projections fall out of applying it to `λx y. x`
//! and `λx y. y`.

use crate::kernel::{Kernel, Result, Term, TheoryId, Thm};

impl Kernel {
    /// `⊢ ∧ = (λp q. (λf. f p q) = (λf. f T T))`.
    pub fn define_conjunction(&mut self, theory: TheoryId, truth: &Thm) -> Result<Thm> {
        todo!("port Conjunction.define")
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
        todo!("port Conjunction.conj")
    }

    /// `Γ ⊢ p ∧ q` gives `Γ ⊢ p`.
    pub fn conjunct1(
        &mut self,
        theory: TheoryId,
        definition: &Thm,
        truth: &Thm,
        thm: &Thm,
    ) -> Result<Thm> {
        todo!("port Conjunction.conjunct1")
    }

    /// `Γ ⊢ p ∧ q` gives `Γ ⊢ q`.
    pub fn conjunct2(
        &mut self,
        theory: TheoryId,
        definition: &Thm,
        truth: &Thm,
        thm: &Thm,
    ) -> Result<Thm> {
        todo!("port Conjunction.conjunct2")
    }
}
