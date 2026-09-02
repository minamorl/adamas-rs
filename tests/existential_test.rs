//! `∃`, encoded by implication and universal quantification.
//!
//! These are Term-level ports of Ruby `origin/main`'s existential tests,
//! including the eigenvariable refusals inherited from the kernel's `ABS`.

use std::collections::BTreeMap;

use adamas::{ExistentialRules, ImplicationRules, Kernel, Result, Term, TheoryId, Thm, Ty};

struct Fixture {
    k: Kernel,
    th: TheoryId,
    rules: ExistentialRules,
    a: Ty,
    x: Term,
    y: Term,
    predicate: Term,
    q: Term,
}

impl Fixture {
    fn new() -> Result<Self> {
        let mut k = Kernel::new();
        let th = k.new_theory("existential");
        let bool_ty = k.bool_ty();
        let a = k.ty_var("A")?;
        let booleans = k.install_booleans(th)?;
        let conjunction_definition = k.define_conjunction(th, &booleans.truth)?;
        let universal_definition = k.define_universal(th, &booleans.truth)?;
        let implication_definition = k.define_implication(th)?;
        let definition = k.define_existential(th)?;
        let implication_rules = ImplicationRules {
            definition: implication_definition,
            conjunction_definition,
            truth: booleans.truth.clone(),
            true_right: booleans.true_right.clone(),
        };
        let x = k.term_var("x", a)?;
        let y = k.term_var("y", a)?;
        let predicate_ty = k.ty_fun(a, bool_ty)?;
        let predicate = k.term_var("P", predicate_ty)?;
        let q = k.term_var("q", bool_ty)?;
        Ok(Self {
            k,
            th,
            rules: ExistentialRules {
                definition,
                universal_definition,
                implication_rules,
                truth: booleans.truth,
                true_right: booleans.true_right,
            },
            a,
            x,
            y,
            predicate,
            q,
        })
    }

    fn application(&mut self, argument: Term) -> Result<Term> {
        self.k.term_comb(self.predicate, argument)
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
fn existential_is_the_universal_continuation_encoding() -> Result<()> {
    let mut fx = Fixture::new()?;
    let instance = fx.application(fx.x)?;
    let implication = fx.k.mk_imp(fx.th, instance, fx.q)?;
    let universal_instance = fx.k.mk_forall(fx.th, fx.x, implication)?;
    let body = fx.k.mk_imp(fx.th, universal_instance, fx.q)?;
    let quantified = fx.k.mk_forall(fx.th, fx.q, body)?;
    let rhs = fx.k.term_abs(fx.predicate, quantified)?;
    let existential = fx.k.constant(fx.th, "∃", None)?;
    let expected = fx.k.term_eq(existential, rhs)?;

    assert_eq!(fx.rules.definition.concl(), expected);
    assert!(fx.rules.definition.hyps().is_empty());
    assert!(fx.k.frees(rhs).is_empty());
    assert_eq!(fx.k.term_type_vars(rhs), vec![fx.a]);
    Ok(())
}

#[test]
fn existential_has_a_boolean_instance() -> Result<()> {
    let mut fx = Fixture::new()?;
    let bool_ty = fx.k.bool_ty();
    let x = fx.k.term_var("x", bool_ty)?;
    let predicate_ty = fx.k.ty_fun(bool_ty, bool_ty)?;
    let predicate = fx.k.term_var("P_bool", predicate_ty)?;
    let body = fx.k.term_comb(predicate, x)?;
    let existential = fx.k.mk_exists(fx.th, x, body)?;
    let (opened, opened_body) = fx.k.dest_exists(existential).expect("an existential");

    assert_eq!(fx.k.type_of(opened), bool_ty);
    assert_eq!(opened_body, fx.k.term_comb(predicate, opened)?);
    Ok(())
}

#[test]
fn existential_refuses_redefinition() -> Result<()> {
    let mut fx = Fixture::new()?;
    assert!(fx.k.define_existential(fx.th).is_err());
    Ok(())
}

#[test]
fn existential_needs_universal_and_implication() -> Result<()> {
    let mut k = Kernel::new();
    let th = k.new_theory("existential without universal");
    let booleans = k.install_booleans(th)?;
    k.define_conjunction(th, &booleans.truth)?;
    k.define_implication(th)?;

    assert!(k.define_existential(th).is_err());
    assert!(k.axioms(th).is_empty());
    Ok(())
}

#[test]
fn exists_introduces_an_existential_quantifier() -> Result<()> {
    let mut fx = Fixture::new()?;
    let body = fx.application(fx.x)?;
    let instance = fx.application(fx.y)?;
    let existential = fx.k.mk_exists(fx.th, fx.x, body)?;
    let assumed = fx.k.assume(fx.th, instance)?;

    let thm = fx.k.exists(fx.th, &fx.rules, existential, fx.y, &assumed)?;

    assert_eq!(thm.concl(), existential);
    assert_eq!(hyps(&thm), vec![instance]);
    assert!(fx.k.axioms(fx.th).is_empty());
    Ok(())
}

#[test]
fn simple_exists_uses_the_bound_variable_as_witness() -> Result<()> {
    let mut fx = Fixture::new()?;
    let body = fx.application(fx.x)?;
    let assumed = fx.k.assume(fx.th, body)?;

    let thm = fx.k.simple_exists(fx.th, &fx.rules, fx.x, &assumed)?;

    assert_eq!(thm.concl(), fx.k.mk_exists(fx.th, fx.x, body)?);
    assert_eq!(hyps(&thm), vec![body]);
    Ok(())
}

#[test]
fn exists_refuses_a_non_existential_target() -> Result<()> {
    let mut fx = Fixture::new()?;
    let body = fx.application(fx.x)?;
    let assumed = fx.k.assume(fx.th, body)?;

    assert!(fx.k.exists(fx.th, &fx.rules, body, fx.x, &assumed).is_err());
    Ok(())
}

#[test]
fn exists_refuses_the_wrong_witness_proof() -> Result<()> {
    let mut fx = Fixture::new()?;
    let body = fx.application(fx.x)?;
    let existential = fx.k.mk_exists(fx.th, fx.x, body)?;
    let wrong = fx.k.assume(fx.th, body)?;

    assert!(fx
        .k
        .exists(fx.th, &fx.rules, existential, fx.y, &wrong)
        .is_err());
    Ok(())
}

#[test]
fn choose_eliminates_an_existential_quantifier() -> Result<()> {
    let mut fx = Fixture::new()?;
    let body = fx.application(fx.x)?;
    let instance = fx.application(fx.y)?;
    let target = fx.k.mk_exists(fx.th, fx.x, body)?;
    let assumed_instance = fx.k.assume(fx.th, instance)?;
    let existential =
        fx.k.exists(fx.th, &fx.rules, target, fx.y, &assumed_instance)?;
    let branch = fx.k.assume(fx.th, fx.q)?;

    let thm = fx.k.choose(fx.th, &fx.rules, &existential, &branch)?;

    assert_eq!(thm.concl(), fx.q);
    assert_eq!(hyps(&thm), sorted(vec![instance, fx.q]));
    Ok(())
}

#[test]
fn choose_refuses_a_non_existential_theorem() -> Result<()> {
    let mut fx = Fixture::new()?;
    let existential = fx.k.assume(fx.th, fx.q)?;
    let branch = fx.k.assume(fx.th, fx.q)?;

    assert!(fx
        .k
        .choose(fx.th, &fx.rules, &existential, &branch)
        .is_err());
    Ok(())
}

#[test]
fn choose_refuses_a_witness_free_in_branch_hypotheses() -> Result<()> {
    let mut fx = Fixture::new()?;
    let body = fx.application(fx.x)?;
    let instance = fx.application(fx.y)?;
    let target = fx.k.mk_exists(fx.th, fx.x, body)?;
    let assumed_instance = fx.k.assume(fx.th, instance)?;
    let existential =
        fx.k.exists(fx.th, &fx.rules, target, fx.y, &assumed_instance)?;
    let constrained = fx.k.term_eq(fx.x, fx.y)?;
    let implication_term = fx.k.mk_imp(fx.th, constrained, fx.q)?;
    let implication = fx.k.assume(fx.th, implication_term)?;
    let constraint = fx.k.assume(fx.th, constrained)?;
    let branch = fx.k.mp(
        fx.th,
        &fx.rules.implication_rules,
        &implication,
        &constraint,
    )?;

    assert!(fx
        .k
        .choose(fx.th, &fx.rules, &existential, &branch)
        .is_err());
    Ok(())
}

#[test]
fn choose_refuses_a_witness_free_in_existential_hypotheses() -> Result<()> {
    let mut fx = Fixture::new()?;
    let body = fx.application(fx.x)?;
    let existential_term = fx.k.mk_exists(fx.th, fx.x, body)?;
    let assumed_existential = fx.k.assume(fx.th, existential_term)?;
    let constrained = fx.k.term_eq(fx.x, fx.y)?;
    let equation = fx.k.term_eq(constrained, assumed_existential.concl())?;
    let assumed_equation = fx.k.assume(fx.th, equation)?;
    let assumed_constraint = fx.k.assume(fx.th, constrained)?;
    let existential = fx.k.eq_mp(fx.th, &assumed_equation, &assumed_constraint)?;
    let branch = fx.k.assume(fx.th, fx.q)?;

    assert!(fx
        .k
        .choose(fx.th, &fx.rules, &existential, &branch)
        .is_err());
    Ok(())
}

#[test]
fn choose_refuses_a_witness_free_in_the_conclusion() -> Result<()> {
    let mut fx = Fixture::new()?;
    let body = fx.application(fx.x)?;
    let instance = fx.application(fx.y)?;
    let target = fx.k.mk_exists(fx.th, fx.x, body)?;
    let assumed_instance = fx.k.assume(fx.th, instance)?;
    let existential =
        fx.k.exists(fx.th, &fx.rules, target, fx.y, &assumed_instance)?;
    let conclusion = fx.k.term_eq(fx.x, fx.x)?;
    let branch = fx.k.assume(fx.th, conclusion)?;

    assert!(fx
        .k
        .choose(fx.th, &fx.rules, &existential, &branch)
        .is_err());
    Ok(())
}

#[test]
fn existential_definition_instantiates_at_another_type() -> Result<()> {
    let mut fx = Fixture::new()?;
    let bool_ty = fx.k.bool_ty();
    let definition = fx.rules.definition.clone();
    let instantiated =
        fx.k.inst_type(fx.th, &BTreeMap::from([(fx.a, bool_ty)]), &definition)?;
    let (lhs, _) = fx.k.dest_eq(instantiated.concl()).expect("an equation");
    let predicate_ty = fx.k.ty_fun(bool_ty, bool_ty)?;
    let expected_ty = fx.k.ty_fun(predicate_ty, bool_ty)?;

    assert_eq!(fx.k.type_of(lhs), expected_ty);
    assert!(instantiated.hyps().is_empty());
    Ok(())
}

#[test]
fn existential_adds_one_definition_and_no_axiom() -> Result<()> {
    let fx = Fixture::new()?;
    assert_eq!(fx.k.definitions(fx.th).len(), 5, "T, ∧, ∀, ⇒ and ∃");
    assert!(fx.k.axioms(fx.th).is_empty());
    Ok(())
}
