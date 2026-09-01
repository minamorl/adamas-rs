//! `⇒`, and the rules that make a hypothesis into an antecedent and back.
//!
//! `p ⇒ q` is defined as `p ∧ q = p`, so everything here rests on the
//! conjunction module — and, through it, on `T`. The theory these tests run in
//! holds three definitions and no axiom, and the last test says so.

use adamas::{ImplicationRules, Kernel, Result, Term, TheoryId, Thm};

struct Fixture {
    k: Kernel,
    th: TheoryId,
    rules: ImplicationRules,
    p: Term,
    q: Term,
    r: Term,
}

impl Fixture {
    fn new() -> Result<Self> {
        let mut k = Kernel::new();
        let th = k.new_theory("implication");
        let bool_ty = k.bool_ty();
        let b = k.install_booleans(th)?;
        let conjunction_definition = k.define_conjunction(th, &b.truth)?;
        let definition = k.define_implication(th)?;
        let p = k.term_var("p", bool_ty)?;
        let q = k.term_var("q", bool_ty)?;
        let r = k.term_var("r", bool_ty)?;
        Ok(Fixture {
            k,
            th,
            rules: ImplicationRules {
                definition,
                conjunction_definition,
                truth: b.truth,
                true_right: b.true_right,
            },
            p,
            q,
            r,
        })
    }
}

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

#[test]
fn implication_is_the_conjunction_being_the_antecedent() -> Result<()> {
    let mut fx = Fixture::new()?;
    let (p, q) = (fx.p, fx.q);

    let conjunction = fx.k.mk_conj(fx.th, p, q)?;
    let body = fx.k.term_eq(conjunction, p)?;
    let inner = fx.k.term_abs(q, body)?;
    let rhs = fx.k.term_abs(p, inner)?;
    let implies = fx.k.constant(fx.th, "⇒", None)?;
    let expected = fx.k.term_eq(implies, rhs)?;

    assert_eq!(fx.rules.definition.concl(), expected);
    assert!(fx.rules.definition.hyps().is_empty());
    Ok(())
}

#[test]
fn mp_takes_the_consequent() -> Result<()> {
    let mut fx = Fixture::new()?;
    let (p, q) = (fx.p, fx.q);
    let implication_term = fx.k.mk_imp(fx.th, p, q)?;
    let implication = fx.k.assume(fx.th, implication_term)?;
    let antecedent = fx.k.assume(fx.th, p)?;

    let thm = fx.k.mp(fx.th, &fx.rules, &implication, &antecedent)?;

    assert_eq!(thm.concl(), q);
    assert_eq!(hyps(&thm), sorted(vec![implication_term, p]));
    Ok(())
}

#[test]
fn mp_refuses_an_antecedent_that_is_not_the_one() -> Result<()> {
    let mut fx = Fixture::new()?;
    let (p, q, r) = (fx.p, fx.q, fx.r);
    let implication_term = fx.k.mk_imp(fx.th, p, q)?;
    let implication = fx.k.assume(fx.th, implication_term)?;
    let wrong = fx.k.assume(fx.th, r)?;

    assert!(fx.k.mp(fx.th, &fx.rules, &implication, &wrong).is_err());

    let not_an_implication = fx.k.assume(fx.th, p)?;
    let antecedent = fx.k.assume(fx.th, p)?;
    assert!(fx
        .k
        .mp(fx.th, &fx.rules, &not_an_implication, &antecedent)
        .is_err());
    Ok(())
}

#[test]
fn disch_turns_a_hypothesis_into_an_antecedent() -> Result<()> {
    let mut fx = Fixture::new()?;
    let p = fx.p;
    let assumed = fx.k.assume(fx.th, p)?;

    let thm = fx.k.disch(fx.th, &fx.rules, p, &assumed)?;

    assert_eq!(thm.concl(), fx.k.mk_imp(fx.th, p, p)?);
    assert!(thm.hyps().is_empty(), "p was discharged");
    assert!(fx.k.axioms(fx.th).is_empty());
    Ok(())
}

#[test]
fn disch_keeps_the_hypotheses_it_was_not_asked_about() -> Result<()> {
    let mut fx = Fixture::new()?;
    let (p, q) = (fx.p, fx.q);
    let assumed = fx.k.assume(fx.th, q)?;

    let thm = fx.k.disch(fx.th, &fx.rules, p, &assumed)?;

    assert_eq!(thm.concl(), fx.k.mk_imp(fx.th, p, q)?);
    assert_eq!(hyps(&thm), vec![q]);
    Ok(())
}

#[test]
fn undisch_puts_the_antecedent_back_as_a_hypothesis() -> Result<()> {
    let mut fx = Fixture::new()?;
    let (p, q) = (fx.p, fx.q);
    let implication_term = fx.k.mk_imp(fx.th, p, q)?;
    let implication = fx.k.assume(fx.th, implication_term)?;

    let thm = fx.k.undisch(fx.th, &fx.rules, &implication)?;

    assert_eq!(thm.concl(), q);
    assert_eq!(hyps(&thm), sorted(vec![implication_term, p]));
    Ok(())
}

#[test]
fn disch_all_leaves_nothing_assumed() -> Result<()> {
    let mut fx = Fixture::new()?;
    let (p, q) = (fx.p, fx.q);
    let left = fx.k.assume(fx.th, p)?;
    let right = fx.k.assume(fx.th, q)?;
    let (definition, true_right) = (
        fx.rules.conjunction_definition.clone(),
        fx.rules.true_right.clone(),
    );
    let paired = fx.k.conj(fx.th, &definition, &true_right, &left, &right)?;
    assert_eq!(hyps(&paired).len(), 2);

    let thm = fx.k.disch_all(fx.th, &fx.rules, &paired)?;

    assert!(thm.hyps().is_empty());
    assert!(fx.k.dest_imp(thm.concl()).is_some());
    Ok(())
}

#[test]
fn imp_antisym_rule_makes_an_equation_out_of_two_implications() -> Result<()> {
    let mut fx = Fixture::new()?;
    let (p, q) = (fx.p, fx.q);
    let forwards_term = fx.k.mk_imp(fx.th, p, q)?;
    let backwards_term = fx.k.mk_imp(fx.th, q, p)?;
    let forwards = fx.k.assume(fx.th, forwards_term)?;
    let backwards = fx.k.assume(fx.th, backwards_term)?;

    let thm =
        fx.k.imp_antisym_rule(fx.th, &fx.rules, &forwards, &backwards)?;

    assert_eq!(thm.concl(), fx.k.term_eq(p, q)?);
    assert_eq!(hyps(&thm), sorted(vec![forwards_term, backwards_term]));
    Ok(())
}

#[test]
fn eq_imp_rule_makes_two_implications_out_of_an_equation() -> Result<()> {
    let mut fx = Fixture::new()?;
    let (p, q) = (fx.p, fx.q);
    let equation_term = fx.k.term_eq(p, q)?;
    let equation = fx.k.assume(fx.th, equation_term)?;

    let (forwards, backwards) = fx.k.eq_imp_rule(fx.th, &fx.rules, &equation)?;

    assert_eq!(forwards.concl(), fx.k.mk_imp(fx.th, p, q)?);
    assert_eq!(backwards.concl(), fx.k.mk_imp(fx.th, q, p)?);
    assert_eq!(hyps(&forwards), vec![equation_term]);
    assert_eq!(hyps(&backwards), vec![equation_term]);
    Ok(())
}

#[test]
fn imp_trans_composes_two_implications() -> Result<()> {
    let mut fx = Fixture::new()?;
    let (p, q, r) = (fx.p, fx.q, fx.r);
    let first_term = fx.k.mk_imp(fx.th, p, q)?;
    let second_term = fx.k.mk_imp(fx.th, q, r)?;
    let first = fx.k.assume(fx.th, first_term)?;
    let second = fx.k.assume(fx.th, second_term)?;

    let thm = fx.k.imp_trans(fx.th, &fx.rules, &first, &second)?;

    assert_eq!(thm.concl(), fx.k.mk_imp(fx.th, p, r)?);
    assert_eq!(hyps(&thm), sorted(vec![first_term, second_term]));
    Ok(())
}

#[test]
fn implication_asserts_nothing_either() -> Result<()> {
    let fx = Fixture::new()?;
    assert!(fx.k.axioms(fx.th).is_empty());
    assert_eq!(fx.k.definitions(fx.th).len(), 3, "T, ∧ and ⇒");
    Ok(())
}
