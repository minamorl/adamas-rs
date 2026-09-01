//! The constant `T`, the theorem `⊢ T`, and three equations about equality —
//! every one of them derived from the ten rules, with no axiom anywhere.
//!
//! Ported from adamas's `lib/adamas/booleans.rb`. Nothing here is trusted: it
//! calls the public rules on a [`Kernel`] and nothing else, so a mistake in
//! this file is a failed proof, never a false theorem.

use crate::kernel::{Kernel, Result, Term, TheoryId, Thm};

/// What [`Kernel::install_booleans`] leaves in a theory.
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
        todo!("port lib/adamas/booleans.rb")
    }
}
