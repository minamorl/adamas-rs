//! `∨`, encoded by implication and universal quantification.
//!
//! The proofs and refusals are direct ports of Ruby `origin/main`'s
//! `lib/adamas/logic/disjunction.rb` and its test.

use adamas::{DisjunctionRules, ImplicationRules, Kernel, Result, Term, TheoryId, Thm};

struct Fixture {
    k: Kernel,
    th: TheoryId,
    rules: DisjunctionRules,
    p: Term,
    q: Term,
    r: Term,
}

impl Fixture {
    fn new() -> Result<Self> {
        let mut k = Kernel::new();
        let th = k.new_theory("disjunction");
        let bool_ty = k.bool_ty();
        let booleans = k.install_booleans(th)?;
        let conjunction_definition = k.define_conjunction(th, &booleans.truth)?;
        let universal_definition = k.define_universal(th, &booleans.truth)?;
        let implication_definition = k.define_implication(th)?;
        let definition = k.define_disjunction(th)?;
        let implication_rules = ImplicationRules {
            definition: implication_definition,
            conjunction_definition,
            truth: booleans.truth.clone(),
            true_right: booleans.true_right.clone(),
        };
        let p = k.term_var("p", bool_ty)?;
        let q = k.term_var("q", bool_ty)?;
        let r = k.term_var("r", bool_ty)?;
        Ok(Self {
            k,
            th,
            rules: DisjunctionRules {
                definition,
                universal_definition,
                implication_rules,
                truth: booleans.truth,
                true_right: booleans.true_right,
            },
            p,
            q,
            r,
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
fn disjunction_is_the_universal_case_split() -> Result<()> {
    let mut fx = Fixture::new()?;
    let left_case = fx.k.mk_imp(fx.th, fx.p, fx.r)?;
    let right_case = fx.k.mk_imp(fx.th, fx.q, fx.r)?;
    let inner = fx.k.mk_imp(fx.th, right_case, fx.r)?;
    let cases = fx.k.mk_imp(fx.th, left_case, inner)?;
    let quantified = fx.k.mk_forall(fx.th, fx.r, cases)?;
    let right_abs = fx.k.term_abs(fx.q, quantified)?;
    let rhs = fx.k.term_abs(fx.p, right_abs)?;
    let disjunction = fx.k.constant(fx.th, "∨", None)?;
    let expected = fx.k.term_eq(disjunction, rhs)?;

    assert_eq!(fx.rules.definition.concl(), expected);
    assert!(fx.rules.definition.hyps().is_empty());
    assert!(fx.k.frees(rhs).is_empty());
    assert!(fx.k.term_type_vars(rhs).is_empty());
    Ok(())
}

#[test]
fn disjunction_refuses_redefinition() -> Result<()> {
    let mut fx = Fixture::new()?;
    assert!(fx.k.define_disjunction(fx.th).is_err());
    Ok(())
}

#[test]
fn disjunction_needs_universal_and_implication() -> Result<()> {
    let mut k = Kernel::new();
    let th = k.new_theory("disjunction without universal");
    let booleans = k.install_booleans(th)?;
    k.define_conjunction(th, &booleans.truth)?;
    k.define_implication(th)?;

    assert!(k.define_disjunction(th).is_err());
    assert!(k.axioms(th).is_empty());
    Ok(())
}

#[test]
fn disj1_introduces_a_left_disjunction() -> Result<()> {
    let mut fx = Fixture::new()?;
    let assumed = fx.k.assume(fx.th, fx.p)?;

    let thm = fx.k.disj1(fx.th, &fx.rules, &assumed, fx.q)?;

    assert_eq!(thm.concl(), fx.k.mk_disj(fx.th, fx.p, fx.q)?);
    assert_eq!(hyps(&thm), vec![fx.p]);
    assert!(fx.k.axioms(fx.th).is_empty());
    Ok(())
}

#[test]
fn disj2_introduces_a_right_disjunction() -> Result<()> {
    let mut fx = Fixture::new()?;
    let assumed = fx.k.assume(fx.th, fx.q)?;

    let thm = fx.k.disj2(fx.th, &fx.rules, fx.p, &assumed)?;

    assert_eq!(thm.concl(), fx.k.mk_disj(fx.th, fx.p, fx.q)?);
    assert_eq!(hyps(&thm), vec![fx.q]);
    Ok(())
}

#[test]
fn disj_cases_eliminates_by_case_split() -> Result<()> {
    let mut fx = Fixture::new()?;
    let disjunction_term = fx.k.mk_disj(fx.th, fx.p, fx.q)?;
    let disjunction = fx.k.assume(fx.th, disjunction_term)?;
    let left_implication_term = fx.k.mk_imp(fx.th, fx.p, fx.r)?;
    let left_implication = fx.k.assume(fx.th, left_implication_term)?;
    let left_assumption = fx.k.assume(fx.th, fx.p)?;
    let left_case = fx.k.mp(
        fx.th,
        &fx.rules.implication_rules,
        &left_implication,
        &left_assumption,
    )?;
    let right_implication_term = fx.k.mk_imp(fx.th, fx.q, fx.r)?;
    let right_implication = fx.k.assume(fx.th, right_implication_term)?;
    let right_assumption = fx.k.assume(fx.th, fx.q)?;
    let right_case = fx.k.mp(
        fx.th,
        &fx.rules.implication_rules,
        &right_implication,
        &right_assumption,
    )?;

    let thm =
        fx.k.disj_cases(fx.th, &fx.rules, &disjunction, &left_case, &right_case)?;

    assert_eq!(thm.concl(), fx.r);
    assert_eq!(
        hyps(&thm),
        sorted(vec![
            disjunction_term,
            left_implication_term,
            right_implication_term,
        ])
    );
    Ok(())
}

#[test]
fn disj_cases_refuses_a_non_disjunction() -> Result<()> {
    let mut fx = Fixture::new()?;
    let proposition = fx.k.assume(fx.th, fx.p)?;
    let left = fx.k.assume(fx.th, fx.r)?;
    let right = fx.k.assume(fx.th, fx.r)?;

    assert!(fx
        .k
        .disj_cases(fx.th, &fx.rules, &proposition, &left, &right)
        .is_err());
    Ok(())
}

#[test]
fn disj_cases_refuses_mismatched_branch_conclusions() -> Result<()> {
    let mut fx = Fixture::new()?;
    let disjunction_term = fx.k.mk_disj(fx.th, fx.p, fx.q)?;
    let disjunction = fx.k.assume(fx.th, disjunction_term)?;
    let left = fx.k.assume(fx.th, fx.r)?;
    let right = fx.k.assume(fx.th, fx.p)?;

    assert!(fx
        .k
        .disj_cases(fx.th, &fx.rules, &disjunction, &left, &right)
        .is_err());
    Ok(())
}

#[test]
fn disjunction_adds_one_definition_and_no_axiom() -> Result<()> {
    let fx = Fixture::new()?;
    assert_eq!(fx.k.definitions(fx.th).len(), 5, "T, ∧, ∀, ⇒ and ∨");
    assert!(fx.k.axioms(fx.th).is_empty());
    Ok(())
}
