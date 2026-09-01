//! The README's logic-layer example, kept honest.
//!
//! The other snippets in that file are illustrative — they elide setup behind
//! `#` lines and would not compile on their own. This one would, so it is
//! compiled: a sample that stops being true is worse than no sample.

use adamas::{Kernel, Result};

#[test]
fn the_readme_example_is_true() -> Result<()> {
    let mut k = Kernel::new();
    let th = k.new_theory("bool");
    let b = k.install_booleans(th)?; // ⊢ T, and ⊢ (p = T) = p
    let and = k.define_conjunction(th, &b.truth)?;
    let bool_ty = k.bool_ty();
    let p = k.term_var("p", bool_ty)?;

    let assumed = k.assume(th, p)?; // p ⊢ p
    let paired = k.conj(th, &and, &b.true_right, &assumed, &assumed)?;
    assert_eq!(paired.concl(), k.mk_conj(th, p, p)?); // p ⊢ p ∧ p
    assert!(k.axioms(th).is_empty());
    Ok(())
}
