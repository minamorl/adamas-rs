//! The README's logic-layer example, kept honest.
//!
//! The other snippets in that file are illustrative — they elide setup behind
//! `#` lines and would not compile on their own. This one would, so it is
//! compiled: a sample that stops being true is worse than no sample.

use adamas::logic::classical;
use adamas::{Kernel, Result};

#[test]
fn the_readme_example_is_true() -> Result<()> {
    let mut k = Kernel::new();
    let th = k.new_theory("logic");
    let logic = k.install_logic(th)?;
    assert!(k.axioms(th).is_empty()); // constructive by default
    assert!(!k.has_constant(th, "@"));

    let choice = classical::install(&mut k, th, &logic)?; // ETA, then SELECT
    let bool_ty = k.bool_ty();
    let p = k.term_var("p", bool_ty)?;
    let em = classical::em(&mut k, th, &choice, &logic, p)?;
    assert_eq!(em.concl(), k.excluded_middle(th, p)?); // ⊢ p ∨ ¬p
    assert!(em.hyps().is_empty());
    assert_eq!(k.axioms(th).len(), 2); // EM was derived
    Ok(())
}
