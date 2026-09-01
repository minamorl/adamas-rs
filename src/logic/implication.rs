//! Implication, defined over conjunction.
//!
//! Ported from adamas's `lib/adamas/logic/implication.rb`. `p ⇒ q` says that
//! `p ∧ q` is `p` — so modus ponens is a projection, and discharging an
//! assumption is `DEDUCT_ANTISYM_RULE` between the two halves of that equation.

use crate::kernel::{Kernel, Result, Term, TheoryId, Thm};

/// The theorems `⇒`'s rules reach for. Ruby carries these in a `Data` bundle;
/// here they are a struct so the signatures stay short.
pub struct ImplicationRules {
    /// `⊢ ⇒ = (λp q. p ∧ q = p)`.
    pub definition: Thm,
    /// `⊢ ∧ = (λp q. (λf. f p q) = (λf. f T T))`.
    pub conjunction_definition: Thm,
    /// `⊢ T`.
    pub truth: Thm,
    /// `⊢ (p = T) = p`.
    pub true_right: Thm,
}

impl Kernel {
    /// `⊢ ⇒ = (λp q. p ∧ q = p)`.
    pub fn define_implication(&mut self, theory: TheoryId) -> Result<Thm> {
        todo!("port Implication.define")
    }

    /// `Γ ⊢ p ⇒ q` and `Δ ⊢ p` give `Γ ∪ Δ ⊢ q`.
    pub fn mp(
        &mut self,
        theory: TheoryId,
        rules: &ImplicationRules,
        implication: &Thm,
        antecedent: &Thm,
    ) -> Result<Thm> {
        todo!("port Implication.mp")
    }

    /// `Γ ⊢ q` gives `Γ - p ⊢ p ⇒ q`.
    pub fn disch(
        &mut self,
        theory: TheoryId,
        rules: &ImplicationRules,
        antecedent: Term,
        thm: &Thm,
    ) -> Result<Thm> {
        todo!("port Implication.disch")
    }

    /// `Γ ⊢ p ⇒ q` gives `Γ ∪ {p} ⊢ q`.
    pub fn undisch(
        &mut self,
        theory: TheoryId,
        rules: &ImplicationRules,
        thm: &Thm,
    ) -> Result<Thm> {
        todo!("port Implication.undisch")
    }

    /// Discharge every hypothesis, innermost last.
    pub fn disch_all(
        &mut self,
        theory: TheoryId,
        rules: &ImplicationRules,
        thm: &Thm,
    ) -> Result<Thm> {
        todo!("port Implication.disch_all")
    }

    /// `Γ ⊢ p = q` gives `Γ ⊢ p ⇒ q` and `Γ ⊢ q ⇒ p`.
    pub fn eq_imp_rule(
        &mut self,
        theory: TheoryId,
        rules: &ImplicationRules,
        thm: &Thm,
    ) -> Result<(Thm, Thm)> {
        todo!("port Implication.eq_imp_rule")
    }

    /// `Γ ⊢ p ⇒ q` and `Δ ⊢ q ⇒ p` give `Γ ∪ Δ ⊢ p = q`.
    pub fn imp_antisym_rule(
        &mut self,
        theory: TheoryId,
        rules: &ImplicationRules,
        left: &Thm,
        right: &Thm,
    ) -> Result<Thm> {
        todo!("port Implication.imp_antisym_rule")
    }

    /// `Γ ⊢ p ⇒ q` and `Δ ⊢ q ⇒ r` give `Γ ∪ Δ ⊢ p ⇒ r`.
    pub fn imp_trans(
        &mut self,
        theory: TheoryId,
        rules: &ImplicationRules,
        left: &Thm,
        right: &Thm,
    ) -> Result<Thm> {
        todo!("port Implication.imp_trans")
    }
}
