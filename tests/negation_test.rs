//! `¬p`, defined as `p ⇒ F`, with its fold/unfold and equality rules.
//!
//! The derivations follow `lib/adamas/logic/negation.rb` from Ruby `origin/main`.

use adamas::{FalsityRules, ImplicationRules, Kernel, NegationRules, Result, Term, TheoryId, Thm};

struct Fixture {
    k: Kernel,
    th: TheoryId,
    rules: NegationRules,
    p: Term,
    q: Term,
}

impl Fixture {
    fn new() -> Result<Self> {
        let mut k = Kernel::new();
        let th = k.new_theory("negation");
        let bool_ty = k.bool_ty();
        let booleans = k.install_booleans(th)?;
        let conjunction_definition = k.define_conjunction(th, &booleans.truth)?;
        let universal_definition = k.define_universal(th, &booleans.truth)?;
        let implication_definition = k.define_implication(th)?;
        let falsity_definition = k.define_falsity(th)?;
        let definition = k.define_negation(th)?;
        let implication_rules = ImplicationRules {
            definition: implication_definition,
            conjunction_definition,
            truth: booleans.truth.clone(),
            true_right: booleans.true_right,
        };
        let falsity_rules = FalsityRules {
            definition: falsity_definition,
            universal_definition,
            truth: booleans.truth,
        };
        let p = k.term_var("p", bool_ty)?;
        let q = k.term_var("q", bool_ty)?;
        Ok(Self {
            k,
            th,
            rules: NegationRules {
                definition,
                implication_rules,
                falsity_rules,
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

#[test]
fn negation_is_implication_to_falsity() -> Result<()> {
    let mut fx = Fixture::new()?;
    let falsity = fx.k.constant(fx.th, "F", None)?;
    let implication = fx.k.mk_imp(fx.th, fx.p, falsity)?;
    let rhs = fx.k.term_abs(fx.p, implication)?;
    let negation = fx.k.constant(fx.th, "¬", None)?;
    let expected = fx.k.term_eq(negation, rhs)?;

    assert_eq!(fx.rules.definition.concl(), expected);
    assert!(fx.rules.definition.hyps().is_empty());
    assert!(fx.k.frees(rhs).is_empty());
    assert!(fx.k.term_type_vars(rhs).is_empty());
    Ok(())
}

#[test]
fn negation_refuses_redefinition() -> Result<()> {
    let mut fx = Fixture::new()?;
    assert!(fx.k.define_negation(fx.th).is_err());
    Ok(())
}

#[test]
fn negation_needs_implication_and_falsity() -> Result<()> {
    let mut k = Kernel::new();
    let th = k.new_theory("negation without falsity");
    let booleans = k.install_booleans(th)?;
    k.define_conjunction(th, &booleans.truth)?;
    k.define_implication(th)?;

    assert!(k.define_negation(th).is_err());
    assert!(k.axioms(th).is_empty());
    Ok(())
}

#[test]
fn not_elim_unfolds_negation_to_implication() -> Result<()> {
    let mut fx = Fixture::new()?;
    let negated = fx.k.mk_neg(fx.th, fx.p)?;
    let assumed = fx.k.assume(fx.th, negated)?;

    let thm = fx.k.not_elim(fx.th, &fx.rules, &assumed)?;

    let falsity = fx.k.constant(fx.th, "F", None)?;
    assert_eq!(thm.concl(), fx.k.mk_imp(fx.th, fx.p, falsity)?);
    assert_eq!(hyps(&thm), vec![negated]);
    Ok(())
}

#[test]
fn not_intro_folds_implication_to_negation() -> Result<()> {
    let mut fx = Fixture::new()?;
    let falsity = fx.k.constant(fx.th, "F", None)?;
    let implication = fx.k.mk_imp(fx.th, fx.p, falsity)?;
    let assumed = fx.k.assume(fx.th, implication)?;

    let thm = fx.k.not_intro(fx.th, &fx.rules, &assumed)?;

    assert_eq!(thm.concl(), fx.k.mk_neg(fx.th, fx.p)?);
    assert_eq!(hyps(&thm), vec![implication]);
    Ok(())
}

#[test]
fn not_elim_refuses_a_non_negation() -> Result<()> {
    let mut fx = Fixture::new()?;
    let assumed = fx.k.assume(fx.th, fx.p)?;
    assert!(fx.k.not_elim(fx.th, &fx.rules, &assumed).is_err());
    Ok(())
}

#[test]
fn not_intro_refuses_a_non_falsity_consequent() -> Result<()> {
    let mut fx = Fixture::new()?;
    let implication = fx.k.mk_imp(fx.th, fx.p, fx.q)?;
    let assumed = fx.k.assume(fx.th, implication)?;
    assert!(fx.k.not_intro(fx.th, &fx.rules, &assumed).is_err());
    Ok(())
}

#[test]
fn eqf_intro_turns_negation_into_equality_with_falsity() -> Result<()> {
    let mut fx = Fixture::new()?;
    let negated = fx.k.mk_neg(fx.th, fx.p)?;
    let assumed = fx.k.assume(fx.th, negated)?;

    let thm = fx.k.eqf_intro(fx.th, &fx.rules, &assumed)?;

    let falsity = fx.k.constant(fx.th, "F", None)?;
    assert_eq!(thm.concl(), fx.k.term_eq(fx.p, falsity)?);
    assert_eq!(hyps(&thm), vec![negated]);
    Ok(())
}

#[test]
fn eqf_elim_turns_equality_with_falsity_into_negation() -> Result<()> {
    let mut fx = Fixture::new()?;
    let falsity = fx.k.constant(fx.th, "F", None)?;
    let equality = fx.k.term_eq(fx.p, falsity)?;
    let assumed = fx.k.assume(fx.th, equality)?;

    let thm = fx.k.eqf_elim(fx.th, &fx.rules, &assumed)?;

    assert_eq!(thm.concl(), fx.k.mk_neg(fx.th, fx.p)?);
    assert_eq!(hyps(&thm), vec![equality]);
    assert!(fx.k.axioms(fx.th).is_empty());
    Ok(())
}

#[test]
fn eqf_elim_refuses_a_non_falsity_equation() -> Result<()> {
    let mut fx = Fixture::new()?;
    let equality = fx.k.term_eq(fx.p, fx.q)?;
    let assumed = fx.k.assume(fx.th, equality)?;
    assert!(fx.k.eqf_elim(fx.th, &fx.rules, &assumed).is_err());
    Ok(())
}

#[test]
fn all_eight_m1_definitions_are_axiom_free_and_reversible() -> Result<()> {
    let mut k = Kernel::new();
    let th = k.new_theory("all m1 definitions");
    let booleans = k.install_booleans(th)?;
    let conjunction = k.define_conjunction(th, &booleans.truth)?;
    let universal = k.define_universal(th, &booleans.truth)?;
    let implication = k.define_implication(th)?;
    let falsity = k.define_falsity(th)?;
    let disjunction = k.define_disjunction(th)?;
    let existential = k.define_existential(th)?;
    let negation = k.define_negation(th)?;
    let definitions = vec![
        booleans.definition,
        conjunction,
        universal,
        implication,
        falsity,
        disjunction,
        existential,
        negation,
    ];

    assert_eq!(k.definitions(th).len(), 8);
    assert!(k.axioms(th).is_empty());
    for definition in definitions {
        let once = k.sym(th, &definition)?;
        let twice = k.sym(th, &once)?;
        assert_eq!(twice.concl(), definition.concl());
    }
    Ok(())
}
