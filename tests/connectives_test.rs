//! `∧` and `∀`: the first two connectives that mean something.
//!
//! The fixture installs the booleans and defines both constants, so every test
//! here runs against a theory whose entire content is three definitions and no
//! axiom — and each test says so, because a theorem obtained by asserting it
//! would pass every other assertion in this file.

use adamas::{Kernel, Result, Term, TheoryId, Thm, Ty};

struct Fixture {
    k: Kernel,
    th: TheoryId,
    a: Ty,
    p: Term,
    q: Term,
    truth: Thm,
    true_right: Thm,
    conjunction: Thm,
    universal: Thm,
}

impl Fixture {
    fn new() -> Result<Self> {
        let mut k = Kernel::new();
        let th = k.new_theory("connectives");
        let bool_ty = k.bool_ty();
        let a = k.ty_var("A")?;
        let b = k.install_booleans(th)?;
        let conjunction = k.define_conjunction(th, &b.truth)?;
        let universal = k.define_universal(th, &b.truth)?;
        let p = k.term_var("p", bool_ty)?;
        let q = k.term_var("q", bool_ty)?;
        Ok(Fixture {
            k,
            th,
            a,
            p,
            q,
            truth: b.truth,
            true_right: b.true_right,
            conjunction,
            universal,
        })
    }
}

/// Hypotheses as a set: the kernel is free to hold them in any order.
fn hyps(thm: &Thm) -> Vec<Term> {
    let mut h = thm.hyps().to_vec();
    h.sort();
    h.dedup();
    h
}

fn sorted(mut terms: Vec<Term>) -> Vec<Term> {
    terms.sort();
    terms.dedup();
    terms
}

// --- ∧ ---------------------------------------------------------------------

#[test]
fn conjunction_is_defined_as_a_pair_selector() -> Result<()> {
    let mut fx = Fixture::new()?;
    let bool_ty = fx.k.bool_ty();
    let t = fx.k.constant(fx.th, "T", None)?;

    let selector_ty = {
        let inner = fx.k.ty_fun(bool_ty, bool_ty)?;
        fx.k.ty_fun(bool_ty, inner)?
    };
    let f = fx.k.term_var("f", selector_ty)?;
    let (p, q) = (fx.p, fx.q);

    let applied = {
        let half = fx.k.term_comb(f, p)?;
        let whole = fx.k.term_comb(half, q)?;
        fx.k.term_abs(f, whole)?
    };
    let constant = {
        let half = fx.k.term_comb(f, t)?;
        let whole = fx.k.term_comb(half, t)?;
        fx.k.term_abs(f, whole)?
    };
    let body = fx.k.term_eq(applied, constant)?;
    let inner = fx.k.term_abs(q, body)?;
    let rhs = fx.k.term_abs(p, inner)?;

    let and = fx.k.constant(fx.th, "∧", None)?;
    let expected = fx.k.term_eq(and, rhs)?;
    assert_eq!(fx.conjunction.concl(), expected);
    assert!(fx.conjunction.hyps().is_empty());
    Ok(())
}

#[test]
fn conj_joins_two_theorems_and_keeps_both_hypotheses() -> Result<()> {
    let mut fx = Fixture::new()?;
    let (p, q) = (fx.p, fx.q);
    let left = fx.k.assume(fx.th, p)?;
    let right = fx.k.assume(fx.th, q)?;

    let (definition, true_right) = (fx.conjunction.clone(), fx.true_right.clone());
    let thm = fx.k.conj(fx.th, &definition, &true_right, &left, &right)?;

    assert_eq!(thm.concl(), fx.k.mk_conj(fx.th, p, q)?);
    assert_eq!(hyps(&thm), sorted(vec![p, q]));
    assert!(fx.k.axioms(fx.th).is_empty());
    Ok(())
}

#[test]
fn the_projections_take_a_conjunction_apart() -> Result<()> {
    let mut fx = Fixture::new()?;
    let (p, q) = (fx.p, fx.q);
    let conjunction = fx.k.mk_conj(fx.th, p, q)?;
    let assumed = fx.k.assume(fx.th, conjunction)?;

    let (definition, truth) = (fx.conjunction.clone(), fx.truth.clone());
    let first = fx.k.conjunct1(fx.th, &definition, &truth, &assumed)?;
    let second = fx.k.conjunct2(fx.th, &definition, &truth, &assumed)?;

    assert_eq!(first.concl(), p);
    assert_eq!(hyps(&first), vec![conjunction]);
    assert_eq!(second.concl(), q);
    assert_eq!(hyps(&second), vec![conjunction]);
    Ok(())
}

#[test]
fn pairing_and_projecting_come_back_to_where_they_started() -> Result<()> {
    let mut fx = Fixture::new()?;
    let (p, q) = (fx.p, fx.q);
    let left = fx.k.assume(fx.th, p)?;
    let right = fx.k.assume(fx.th, q)?;

    let (definition, true_right, truth) = (
        fx.conjunction.clone(),
        fx.true_right.clone(),
        fx.truth.clone(),
    );
    let paired = fx.k.conj(fx.th, &definition, &true_right, &left, &right)?;
    let back = fx.k.conjunct2(fx.th, &definition, &truth, &paired)?;

    assert_eq!(back.concl(), q);
    assert_eq!(hyps(&back), sorted(vec![p, q]));
    Ok(())
}

#[test]
fn a_projection_refuses_a_theorem_that_is_not_a_conjunction() -> Result<()> {
    let mut fx = Fixture::new()?;
    let p = fx.p;
    let assumed = fx.k.assume(fx.th, p)?;

    let (definition, truth) = (fx.conjunction.clone(), fx.truth.clone());
    assert!(fx
        .k
        .conjunct1(fx.th, &definition, &truth, &assumed)
        .is_err());
    assert!(fx
        .k
        .conjunct2(fx.th, &definition, &truth, &assumed)
        .is_err());
    Ok(())
}

// --- ∀ ---------------------------------------------------------------------

#[test]
fn universal_quantification_is_being_the_constantly_true_predicate() -> Result<()> {
    let mut fx = Fixture::new()?;
    let bool_ty = fx.k.bool_ty();
    let t = fx.k.constant(fx.th, "T", None)?;

    let predicate_ty = fx.k.ty_fun(fx.a, bool_ty)?;
    let predicate = fx.k.term_var("P", predicate_ty)?;
    let witness = fx.k.term_var("x", fx.a)?;
    let constantly_true = fx.k.term_abs(witness, t)?;
    let body = fx.k.term_eq(predicate, constantly_true)?;
    let rhs = fx.k.term_abs(predicate, body)?;

    let quantifier_ty = fx.k.ty_fun(predicate_ty, bool_ty)?;
    let all = fx.k.constant(fx.th, "∀", Some(quantifier_ty))?;
    let expected = fx.k.term_eq(all, rhs)?;
    assert_eq!(fx.universal.concl(), expected);
    assert!(fx.universal.hyps().is_empty());
    Ok(())
}

#[test]
fn gen_binds_a_variable_and_spec_lets_another_one_in() -> Result<()> {
    let mut fx = Fixture::new()?;
    let x = fx.k.term_var("x", fx.a)?;
    let reflexive = fx.k.refl(fx.th, x)?;

    let (definition, true_right, truth) = (
        fx.universal.clone(),
        fx.true_right.clone(),
        fx.truth.clone(),
    );
    let general = fx.k.gen(fx.th, &definition, &true_right, x, &reflexive)?;

    let body = fx.k.term_eq(x, x)?;
    assert_eq!(general.concl(), fx.k.mk_forall(fx.th, x, body)?);
    assert!(general.hyps().is_empty());

    let y = fx.k.term_var("y", fx.a)?;
    let instance = fx.k.spec(fx.th, &definition, &truth, &general, y)?;
    assert_eq!(instance.concl(), fx.k.term_eq(y, y)?);
    assert!(instance.hyps().is_empty());
    assert!(fx.k.axioms(fx.th).is_empty());
    Ok(())
}

#[test]
fn spec_carries_the_hypotheses_through() -> Result<()> {
    let mut fx = Fixture::new()?;
    let bool_ty = fx.k.bool_ty();
    let x = fx.k.term_var("x", bool_ty)?;
    let p = fx.p;
    let assumed = fx.k.assume(fx.th, p)?;

    let (definition, true_right, truth) = (
        fx.universal.clone(),
        fx.true_right.clone(),
        fx.truth.clone(),
    );
    // `x` is free in no hypothesis of `p ⊢ p`, so it may be generalised.
    let general = fx.k.gen(fx.th, &definition, &true_right, x, &assumed)?;
    let instance = fx.k.spec(fx.th, &definition, &truth, &general, fx.q)?;

    assert_eq!(instance.concl(), p);
    assert_eq!(hyps(&instance), vec![p]);
    Ok(())
}

#[test]
fn gen_refuses_a_variable_a_hypothesis_still_mentions() -> Result<()> {
    let mut fx = Fixture::new()?;
    let p = fx.p;
    let assumed = fx.k.assume(fx.th, p)?;

    let (definition, true_right) = (fx.universal.clone(), fx.true_right.clone());
    assert!(fx
        .k
        .gen(fx.th, &definition, &true_right, p, &assumed)
        .is_err());
    Ok(())
}

#[test]
fn spec_refuses_a_theorem_that_is_not_a_quantification() -> Result<()> {
    let mut fx = Fixture::new()?;
    let p = fx.p;
    let assumed = fx.k.assume(fx.th, p)?;

    let (definition, truth) = (fx.universal.clone(), fx.truth.clone());
    assert!(fx
        .k
        .spec(fx.th, &definition, &truth, &assumed, fx.q)
        .is_err());
    Ok(())
}

#[test]
fn three_definitions_and_no_axiom() -> Result<()> {
    let fx = Fixture::new()?;
    assert!(fx.k.axioms(fx.th).is_empty());
    assert_eq!(fx.k.definitions(fx.th).len(), 3, "T, ∧ and ∀");
    Ok(())
}
