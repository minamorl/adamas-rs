//! The kernel's own tests, ported from adamas's `test/`.
//!
//! The forgery tests live as `compile_fail` doctests on `Thm`, because that is
//! where the boundary actually is. What is left here is behaviour: the ten
//! primitive rules do what `fusion.ml` says, the constructors refuse what they
//! should, and hash-consing makes alpha-equivalence a word comparison.

use std::collections::BTreeMap;

use adamas::{Kernel, Result, Term, TheoryId, Ty};

/// A theory with `p`, `q` : bool and `f` : bool → bool to hand.
struct Fixture {
    k: Kernel,
    th: TheoryId,
    bool_ty: Ty,
    p: Term,
    q: Term,
}

impl Fixture {
    fn new() -> Result<Self> {
        let mut k = Kernel::new();
        let th = k.new_theory("test");
        let bool_ty = k.bool_ty();
        let p = k.term_var("p", bool_ty)?;
        let q = k.term_var("q", bool_ty)?;
        Ok(Fixture {
            k,
            th,
            bool_ty,
            p,
            q,
        })
    }
}

// --- the ten primitive rules ----------------------------------------------

#[test]
fn refl_proves_reflexivity() -> Result<()> {
    let mut f = Fixture::new()?;
    let thm = f.k.refl(f.th, f.p)?;
    assert_eq!(f.k.thm_to_string(&thm), "⊢ p = p");
    assert!(thm.hyps().is_empty());
    Ok(())
}

#[test]
fn assume_makes_the_hypothesis_its_own_conclusion() -> Result<()> {
    let mut f = Fixture::new()?;
    let thm = f.k.assume(f.th, f.p)?;
    assert_eq!(f.k.thm_to_string(&thm), "p ⊢ p");
    Ok(())
}

#[test]
fn assume_refuses_a_non_proposition() -> Result<()> {
    let mut f = Fixture::new()?;
    let a = f.k.ty_var("A")?;
    let x = f.k.term_var("x", a)?;
    assert!(f.k.assume(f.th, x).is_err());
    Ok(())
}

#[test]
fn trans_chains_two_equations() -> Result<()> {
    let mut f = Fixture::new()?;
    // p ⊢ p = q  and  q = p as an assumption chain: use ASSUME'd equations.
    let pq = f.k.term_eq(f.p, f.q)?;
    let left = f.k.assume(f.th, pq)?;
    let qp = f.k.term_eq(f.q, f.p)?;
    let right = f.k.assume(f.th, qp)?;
    let thm = f.k.trans(f.th, &left, &right)?;
    assert_eq!(f.k.thm_to_string(&thm), "p = q, q = p ⊢ p = p");
    Ok(())
}

#[test]
fn trans_refuses_a_broken_chain() -> Result<()> {
    let mut f = Fixture::new()?;
    let pq = f.k.term_eq(f.p, f.q)?;
    let left = f.k.assume(f.th, pq)?;
    let right = f.k.refl(f.th, f.p)?; // ⊢ p = p, and p is not q
    assert!(f.k.trans(f.th, &left, &right).is_err());
    Ok(())
}

#[test]
fn mk_comb_congruence() -> Result<()> {
    let mut f = Fixture::new()?;
    let fun_ty = f.k.ty_fun(f.bool_ty, f.bool_ty)?;
    let g = f.k.term_var("g", fun_ty)?;
    let fun_thm = f.k.refl(f.th, g)?;
    let pq = f.k.term_eq(f.p, f.q)?;
    let arg_thm = f.k.assume(f.th, pq)?;
    let thm = f.k.mk_comb(f.th, &fun_thm, &arg_thm)?;
    assert_eq!(f.k.thm_to_string(&thm), "p = q ⊢ g p = g q");
    Ok(())
}

#[test]
fn abs_generalises_over_a_variable() -> Result<()> {
    let mut f = Fixture::new()?;
    let thm = f.k.refl(f.th, f.p)?;
    let abstracted = f.k.abs(f.th, f.p, &thm)?;
    assert_eq!(f.k.thm_to_string(&abstracted), "⊢ (λp. «0») = (λp. «0»)");
    Ok(())
}

#[test]
fn abs_refuses_a_variable_free_in_a_hypothesis() -> Result<()> {
    let mut f = Fixture::new()?;
    // p ⊢ p = q, and p is free in the hypothesis, so ABS must refuse.
    let pq = f.k.term_eq(f.p, f.q)?;
    let thm = f.k.assume(f.th, pq)?;
    assert!(f.k.abs(f.th, f.p, &thm).is_err());
    Ok(())
}

#[test]
fn beta_reduces_the_trivial_redex() -> Result<()> {
    let mut f = Fixture::new()?;
    let body = f.k.term_eq(f.p, f.p)?;
    let lam = f.k.term_abs(f.p, body)?;
    let redex = f.k.term_comb(lam, f.q)?;
    let thm = f.k.beta(f.th, redex)?;
    assert_eq!(f.k.thm_to_string(&thm), "⊢ (λp. «0» = «0») q = (q = q)");
    Ok(())
}

#[test]
fn beta_refuses_a_non_trivial_redex() -> Result<()> {
    let mut f = Fixture::new()?;
    let body = f.k.term_eq(f.p, f.p)?;
    let lam = f.k.term_abs(f.p, body)?;
    // the argument is not a variable
    let arg = f.k.term_eq(f.q, f.q)?;
    let redex = f.k.term_comb(lam, arg)?;
    assert!(f.k.beta(f.th, redex).is_err());
    Ok(())
}

#[test]
fn eq_mp_moves_across_an_equation() -> Result<()> {
    let mut f = Fixture::new()?;
    let pq = f.k.term_eq(f.p, f.q)?;
    let eq_thm = f.k.assume(f.th, pq)?;
    let thm = f.k.assume(f.th, f.p)?;
    let out = f.k.eq_mp(f.th, &eq_thm, &thm)?;
    assert_eq!(f.k.thm_to_string(&out), "p, p = q ⊢ q");
    Ok(())
}

#[test]
fn eq_mp_refuses_a_mismatched_left_side() -> Result<()> {
    let mut f = Fixture::new()?;
    let pq = f.k.term_eq(f.p, f.q)?;
    let eq_thm = f.k.assume(f.th, pq)?;
    let thm = f.k.assume(f.th, f.q)?; // q, not p
    assert!(f.k.eq_mp(f.th, &eq_thm, &thm).is_err());
    Ok(())
}

#[test]
fn deduct_antisym_discharges_both_hypotheses() -> Result<()> {
    let mut f = Fixture::new()?;
    let left = f.k.assume(f.th, f.p)?; // p ⊢ p
    let right = f.k.assume(f.th, f.q)?; // q ⊢ q
    let thm = f.k.deduct_antisym_rule(f.th, &left, &right)?;
    // (p - q) ∪ (q - p) ⊢ p = q  — neither hypothesis is the other's conclusion
    assert_eq!(f.k.thm_to_string(&thm), "p, q ⊢ p = q");

    // When they *do* entail each other, the hypotheses vanish.
    let l2 = f.k.assume(f.th, f.p)?;
    let r2 = f.k.assume(f.th, f.p)?;
    let thm2 = f.k.deduct_antisym_rule(f.th, &l2, &r2)?;
    assert_eq!(f.k.thm_to_string(&thm2), "⊢ p = p");
    Ok(())
}

#[test]
fn inst_substitutes_terms_for_variables() -> Result<()> {
    let mut f = Fixture::new()?;
    let thm = f.k.assume(f.th, f.p)?;
    let theta = BTreeMap::from([(f.p, f.q)]);
    let out = f.k.inst(f.th, &theta, &thm)?;
    assert_eq!(f.k.thm_to_string(&out), "q ⊢ q");
    Ok(())
}

#[test]
fn inst_refuses_a_type_mismatched_substitution() -> Result<()> {
    let mut f = Fixture::new()?;
    let thm = f.k.assume(f.th, f.p)?;
    let a = f.k.ty_var("A")?;
    let x = f.k.term_var("x", a)?;
    let theta = BTreeMap::from([(f.p, x)]);
    assert!(f.k.inst(f.th, &theta, &thm).is_err());
    Ok(())
}

#[test]
fn inst_type_substitutes_types_for_type_variables() -> Result<()> {
    let mut f = Fixture::new()?;
    let a = f.k.ty_var("A")?;
    let x = f.k.term_var("x", a)?;
    let thm = f.k.refl(f.th, x)?;
    assert_eq!(f.k.thm_to_string(&thm), "⊢ x = x");
    let theta = BTreeMap::from([(a, f.bool_ty)]);
    let out = f.k.inst_type(f.th, &theta, &thm)?;
    assert_eq!(f.k.thm_to_string(&out), "⊢ x = x");
    // The conclusion is now at bool, which is a different term.
    assert_ne!(thm.concl(), out.concl());
    Ok(())
}

#[test]
fn inst_type_refuses_a_non_variable_key() -> Result<()> {
    let mut f = Fixture::new()?;
    let thm = f.k.refl(f.th, f.p)?;
    let theta = BTreeMap::from([(f.bool_ty, f.bool_ty)]);
    assert!(f.k.inst_type(f.th, &theta, &thm).is_err());
    Ok(())
}

// --- theory scoping --------------------------------------------------------

#[test]
fn a_theorem_of_another_theory_is_not_a_theorem_here() -> Result<()> {
    let mut f = Fixture::new()?;
    let other = f.k.new_theory("other");
    let foreign = f.k.assume(other, f.p)?;
    let mine = f.k.assume(f.th, f.p)?;
    assert!(f.k.trans(f.th, &foreign, &mine).is_err());
    assert!(f.k.eq_mp(f.th, &mine, &foreign).is_err());
    Ok(())
}

// --- hash-consing ----------------------------------------------------------

#[test]
fn alpha_equivalent_abstractions_are_the_same_node() -> Result<()> {
    let mut f = Fixture::new()?;
    let x = f.k.term_var("x", f.bool_ty)?;
    let y = f.k.term_var("y", f.bool_ty)?;
    let lam_x = f.k.term_abs(x, x)?; // λx. x
    let lam_y = f.k.term_abs(y, y)?; // λy. y
    assert_eq!(lam_x, lam_y, "alpha-equivalence is one word comparison");
    Ok(())
}

#[test]
fn variables_differing_only_in_type_are_different() -> Result<()> {
    let mut f = Fixture::new()?;
    let a = f.k.ty_var("A")?;
    let x_bool = f.k.term_var("x", f.bool_ty)?;
    let x_a = f.k.term_var("x", a)?;
    assert_ne!(x_bool, x_a);
    Ok(())
}

// --- the constructors refuse ill-typed syntax ------------------------------

#[test]
fn a_non_function_cannot_be_applied() -> Result<()> {
    let mut f = Fixture::new()?;
    assert!(f.k.term_comb(f.p, f.q).is_err());
    Ok(())
}

#[test]
fn an_argument_of_the_wrong_type_is_refused() -> Result<()> {
    let mut f = Fixture::new()?;
    let a = f.k.ty_var("A")?;
    let fun_ty = f.k.ty_fun(a, f.bool_ty)?;
    let g = f.k.term_var("g", fun_ty)?;
    assert!(f.k.term_comb(g, f.p).is_err());
    Ok(())
}

#[test]
fn terms_of_different_types_cannot_be_equated() -> Result<()> {
    let mut f = Fixture::new()?;
    let a = f.k.ty_var("A")?;
    let x = f.k.term_var("x", a)?;
    assert!(f.k.term_eq(f.p, x).is_err());
    Ok(())
}

#[test]
fn an_unknown_type_constructor_is_refused() -> Result<()> {
    let mut f = Fixture::new()?;
    assert!(f.k.ty_con("list", &[f.bool_ty]).is_err());
    Ok(())
}

#[test]
fn a_type_constructor_cannot_be_declared_twice() -> Result<()> {
    let mut f = Fixture::new()?;
    assert!(f.k.new_type("ind", 0).is_ok());
    assert!(f.k.new_type("ind", 0).is_err());
    assert!(f.k.new_type("bool", 0).is_err());
    Ok(())
}

// --- the gates -------------------------------------------------------------

#[test]
fn new_axiom_asserts_without_proof() -> Result<()> {
    let mut f = Fixture::new()?;
    let thm = f.k.new_axiom(f.th, f.p)?;
    assert_eq!(f.k.thm_to_string(&thm), "⊢ p");
    assert_eq!(f.k.axioms(f.th).len(), 1);
    Ok(())
}

#[test]
fn new_axiom_refuses_an_open_term() -> Result<()> {
    let mut f = Fixture::new()?;
    let a = f.k.ty_var("A")?;
    let x = f.k.term_var("x", a)?;
    assert!(f.k.new_axiom(f.th, x).is_err());
    Ok(())
}

#[test]
fn new_basic_definition_declares_and_proves() -> Result<()> {
    let mut f = Fixture::new()?;
    // T = ((λx:bool. x) = (λx:bool. x))
    let x = f.k.term_var("x", f.bool_ty)?;
    let idf = f.k.term_abs(x, x)?;
    let rhs = f.k.term_eq(idf, idf)?;
    let c = f.k.term_var("T", f.bool_ty)?;
    let defn = f.k.term_eq(c, rhs)?;
    let thm = f.k.new_basic_definition(f.th, defn)?;
    assert_eq!(f.k.thm_to_string(&thm), "⊢ T = ((λx. «0») = (λx. «0»))");
    assert!(f.k.has_constant(f.th, "T"));
    Ok(())
}

#[test]
fn new_basic_definition_refuses_a_free_variable_on_the_right() -> Result<()> {
    let mut f = Fixture::new()?;
    let c = f.k.term_var("C", f.bool_ty)?;
    let defn = f.k.term_eq(c, f.q)?; // q is free
    assert!(f.k.new_basic_definition(f.th, defn).is_err());
    Ok(())
}

#[test]
fn a_constant_may_only_be_used_at_an_instance_of_its_type() -> Result<()> {
    let mut f = Fixture::new()?;
    let a = f.k.ty_var("A")?;
    let poly = f.k.ty_fun(a, a)?;
    f.k.new_constant(f.th, "id", poly)?;
    // bool → bool is an instance of A → A
    let bb = f.k.ty_fun(f.bool_ty, f.bool_ty)?;
    assert!(f.k.constant(f.th, "id", Some(bb)).is_ok());
    // bool is not
    assert!(f.k.constant(f.th, "id", Some(f.bool_ty)).is_err());
    Ok(())
}

#[test]
fn new_basic_type_definition_yields_the_two_theorems() -> Result<()> {
    let mut f = Fixture::new()?;
    // A predicate that holds of something: (λx:bool. x = x), applied to p.
    let x = f.k.term_var("x", f.bool_ty)?;
    let body = f.k.term_eq(x, x)?;
    let pred = f.k.term_abs(x, body)?;
    let applied = f.k.term_comb(pred, f.p)?;
    // ⊢ P p, taken as an axiom so we have a witness without a derivation.
    let witness = f.k.new_axiom(f.th, applied)?;
    let (abs_rep, rep_abs) =
        f.k.new_basic_type_definition(f.th, "small", "mk_small", "dest_small", &witness)?;
    assert_eq!(f.k.thm_to_string(&abs_rep), "⊢ mk_small (dest_small a) = a");
    assert_eq!(
        f.k.thm_to_string(&rep_abs),
        "⊢ (λx. «0» = «0») r = (dest_small (mk_small r) = r)"
    );
    assert_eq!(f.k.type_definitions(f.th).len(), 1);
    Ok(())
}

#[test]
fn new_basic_type_definition_refuses_a_witness_with_hypotheses() -> Result<()> {
    let mut f = Fixture::new()?;
    let x = f.k.term_var("x", f.bool_ty)?;
    let body = f.k.term_eq(x, x)?;
    let pred = f.k.term_abs(x, body)?;
    let applied = f.k.term_comb(pred, f.p)?;
    let witness = f.k.assume(f.th, applied)?; // has a hypothesis
    assert!(f
        .k
        .new_basic_type_definition(f.th, "small2", "mk2", "dest2", &witness)
        .is_err());
    Ok(())
}

// --- a real derivation, end to end -----------------------------------------

#[test]
fn beta_conversion_for_an_arbitrary_argument_is_derivable() -> Result<()> {
    // The point of a small kernel: BETA is primitive only for the trivial
    // redex, and the general case is *derived* from BETA + INST rather than
    // trusted. `⊢ (λv. v = v) q = (q = q)`, reached the long way.
    let mut f = Fixture::new()?;
    let v = f.k.term_var("v", f.bool_ty)?;
    let body = f.k.term_eq(v, v)?;
    let lam = f.k.term_abs(v, body)?;

    // BETA at the binder's own variable, then INST it to q.
    let trivial = f.k.term_comb(lam, v)?;
    let base = f.k.beta(f.th, trivial)?;
    let theta = BTreeMap::from([(v, f.q)]);
    let derived = f.k.inst(f.th, &theta, &base)?;

    assert_eq!(f.k.thm_to_string(&derived), "⊢ (λv. «0» = «0») q = (q = q)");
    assert!(derived.hyps().is_empty());
    Ok(())
}
