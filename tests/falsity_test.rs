//! `F`, defined as `∀p. p`, and explosion from that definition.
//!
//! Ported from the Ruby original's `test/logic/falsity_test.rb`. Every expected
//! proposition is assembled as a [`Term`]; printer output is not evidence.

use adamas::{FalsityRules, Kernel, Result, Term, TheoryId, Thm};

struct Fixture {
    k: Kernel,
    th: TheoryId,
    rules: FalsityRules,
    p: Term,
    q: Term,
}

impl Fixture {
    fn new() -> Result<Self> {
        let mut k = Kernel::new();
        let th = k.new_theory("falsity");
        let bool_ty = k.bool_ty();
        let booleans = k.install_booleans(th)?;
        let universal_definition = k.define_universal(th, &booleans.truth)?;
        let definition = k.define_falsity(th)?;
        let p = k.term_var("p", bool_ty)?;
        let q = k.term_var("q", bool_ty)?;
        Ok(Self {
            k,
            th,
            rules: FalsityRules {
                definition,
                universal_definition,
                truth: booleans.truth,
            },
            p,
            q,
        })
    }
}

fn hyps(thm: &Thm) -> Vec<Term> {
    let mut terms = thm.hyps().to_vec();
    terms.sort();
    terms.dedup();
    terms
}

fn sorted(mut terms: Vec<Term>) -> Vec<Term> {
    terms.sort();
    terms.dedup();
    terms
}

#[test]
fn falsity_is_every_proposition_at_once() -> Result<()> {
    let mut fx = Fixture::new()?;
    let p = fx.p;
    let rhs = fx.k.mk_forall(fx.th, p, p)?;
    let falsity = fx.k.constant(fx.th, "F", None)?;
    let expected = fx.k.term_eq(falsity, rhs)?;

    assert_eq!(fx.rules.definition.concl(), expected);
    assert!(fx.rules.definition.hyps().is_empty());
    assert!(fx.k.frees(rhs).is_empty());
    assert!(fx.k.term_type_vars(rhs).is_empty());
    Ok(())
}

#[test]
fn falsity_refuses_redefinition() -> Result<()> {
    let mut fx = Fixture::new()?;
    assert!(fx.k.define_falsity(fx.th).is_err());
    Ok(())
}

#[test]
fn falsity_needs_the_universal_constant() -> Result<()> {
    let mut k = Kernel::new();
    let th = k.new_theory("falsity without universal");
    k.install_booleans(th)?;

    assert!(k.define_falsity(th).is_err());
    assert!(k.axioms(th).is_empty());
    Ok(())
}

#[test]
fn contr_derives_any_proposition_from_falsity() -> Result<()> {
    let mut fx = Fixture::new()?;
    let falsity = fx.k.constant(fx.th, "F", None)?;
    let assumed = fx.k.assume(fx.th, falsity)?;

    let thm = fx.k.contr(fx.th, &fx.rules, &assumed, fx.p)?;

    assert_eq!(thm.concl(), fx.p);
    assert_eq!(hyps(&thm), vec![falsity]);
    assert!(fx.k.axioms(fx.th).is_empty());
    Ok(())
}

#[test]
fn contr_preserves_existing_hypotheses() -> Result<()> {
    let mut fx = Fixture::new()?;
    let falsity = fx.k.constant(fx.th, "F", None)?;
    let equation = fx.k.term_eq(fx.p, falsity)?;
    let assumed_equation = fx.k.assume(fx.th, equation)?;
    let assumed_proposition = fx.k.assume(fx.th, fx.p)?;
    let false_thm = fx.k.eq_mp(fx.th, &assumed_equation, &assumed_proposition)?;

    let thm = fx.k.contr(fx.th, &fx.rules, &false_thm, fx.q)?;

    assert_eq!(thm.concl(), fx.q);
    assert_eq!(hyps(&thm), sorted(vec![fx.p, equation]));
    assert!(fx.k.axioms(fx.th).is_empty());
    Ok(())
}

#[test]
fn falsity_adds_one_definition_and_no_axiom() -> Result<()> {
    let fx = Fixture::new()?;
    assert_eq!(fx.k.definitions(fx.th).len(), 3, "T, ∀ and F");
    assert!(fx.k.axioms(fx.th).is_empty());
    Ok(())
}
