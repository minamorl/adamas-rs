//! adamas — an LCF-style proof kernel. Theorems you cannot forge, terms you
//! cannot mistype.
//!
//! A Rust port of the trusted core of [adamas](https://github.com/minamorl/adamas),
//! whose Ruby original states plainly, under *What the kernel does not
//! guarantee*, that **Ruby has no real privacy** — `send`, `Marshal` and
//! `ObjectSpace` defeat any scheme, and `test/forgery_test.rb` carries a case
//! that survives every invariant and is stopped only by that porous privacy.
//!
//! Here [`Thm`]'s fields are private to the `kernel` module. There is no
//! constructor outside it and no reflective back door, so the headline claim is
//! true rather than aspirational.
//!
//! ```
//! use adamas::{Kernel, Result};
//!
//! # fn main() -> Result<()> {
//! let mut k = Kernel::new();
//! let th = k.new_theory("demo");
//! let bool_ty = k.bool_ty();
//! let p = k.term_var("p", bool_ty)?;
//!
//! // p ⊢ p, and ⊢ p = p
//! let assumed = k.assume(th, p)?;
//! assert_eq!(k.thm_to_string(&assumed), "p ⊢ p");
//! let refl = k.refl(th, p)?;
//! assert_eq!(k.thm_to_string(&refl), "⊢ p = p");
//! # Ok(())
//! # }
//! ```

pub mod certificate;
mod derived;
mod intern;
mod kernel;
pub mod path;
mod replay;

pub use certificate::{Certificate, Condition, Rule, RuleSet, Step};
pub use kernel::{
    Error, Kernel, Result, Term, TermNode, TheoryId, Thm, Ty, TyNode, TypeDefinition,
};
pub use path::{path_to_string, PathStep};
