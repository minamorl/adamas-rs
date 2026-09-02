//! Hypothesis-free rewrite rules derived from the constructive connectives.
//!
//! This is a direct port of Ruby adamas's `lib/adamas/logic/simp.rb`. Every
//! rule is assembled from existing derived rules and registered with the
//! ordinary untrusted [`RuleSet`]; no assertion is made here.

use crate::booleans::Booleans;
use crate::certificate::RuleSet;
use crate::kernel::{Kernel, Result, Term, TheoryId, Thm};

use super::disjunction::DisjunctionRules;
use super::falsity::FalsityRules;
use super::implication::ImplicationRules;
use super::negation::NegationRules;

/// The definitions and derived rule handles used to construct the simp set.
#[derive(Clone)]
pub struct SimpRules {
    pub booleans: Booleans,
    pub conjunction_definition: Thm,
    pub universal_definition: Thm,
    pub implication_rules: ImplicationRules,
    pub falsity_rules: FalsityRules,
    pub disjunction_rules: DisjunctionRules,
    pub negation_rules: NegationRules,
}

/// Install the three boolean equations followed by Ruby's thirteen logical
/// additions, preserving registration order.
pub fn install(kernel: &mut Kernel, theory: TheoryId, rules: &SimpRules) -> Result<RuleSet> {
    let mut set = RuleSet::new();
    set.add(kernel, "refl", rules.booleans.refl_is_true.clone())?;
    set.add(kernel, "true_left", rules.booleans.true_left.clone())?;
    set.add(kernel, "true_right", rules.booleans.true_right.clone())?;

    let proposition = kernel.term_var("p", kernel.bool_ty())?;
    let element = kernel.ty_var("A")?;
    let variable = kernel.term_var("x", element)?;

    let additions = [
        (
            "conj_true_left",
            conj_true_left(kernel, theory, rules, proposition)?,
        ),
        (
            "conj_true_right",
            conj_true_right(kernel, theory, rules, proposition)?,
        ),
        (
            "conj_false_left",
            conj_false_left(kernel, theory, rules, proposition)?,
        ),
        (
            "conj_idempotent",
            conj_idempotent(kernel, theory, rules, proposition)?,
        ),
        (
            "imp_true_left",
            imp_true_left(kernel, theory, rules, proposition)?,
        ),
        (
            "imp_true_right",
            imp_true_right(kernel, theory, rules, proposition)?,
        ),
        (
            "imp_false_left",
            imp_false_left(kernel, theory, rules, proposition)?,
        ),
        (
            "disj_true_left",
            disj_true_left(kernel, theory, rules, proposition)?,
        ),
        (
            "disj_true_right",
            disj_true_right(kernel, theory, rules, proposition)?,
        ),
        (
            "disj_false_left",
            disj_false_left(kernel, theory, rules, proposition)?,
        ),
        ("neg_true", neg_true(kernel, theory, rules)?),
        ("neg_false", neg_false(kernel, theory, rules)?),
        ("forall_true", forall_true(kernel, theory, rules, variable)?),
    ];
    for (name, theorem) in additions {
        set.add(kernel, name, theorem)?;
    }
    Ok(set)
}

fn conj_true_left(
    kernel: &mut Kernel,
    theory: TheoryId,
    rules: &SimpRules,
    proposition: Term,
) -> Result<Thm> {
    let left = kernel.mk_conj(theory, rules.booleans.true_const, proposition)?;
    let assumed_left = kernel.assume(theory, left)?;
    let left_to_right = kernel.conjunct2(
        theory,
        &rules.conjunction_definition,
        &rules.booleans.truth,
        &assumed_left,
    )?;
    let assumed_right = kernel.assume(theory, proposition)?;
    let right_to_left = kernel.conj(
        theory,
        &rules.conjunction_definition,
        &rules.booleans.true_right,
        &rules.booleans.truth,
        &assumed_right,
    )?;
    from_assumptions(kernel, theory, &left_to_right, &right_to_left)
}

fn conj_true_right(
    kernel: &mut Kernel,
    theory: TheoryId,
    rules: &SimpRules,
    proposition: Term,
) -> Result<Thm> {
    let left = kernel.mk_conj(theory, proposition, rules.booleans.true_const)?;
    let assumed_left = kernel.assume(theory, left)?;
    let left_to_right = kernel.conjunct1(
        theory,
        &rules.conjunction_definition,
        &rules.booleans.truth,
        &assumed_left,
    )?;
    let assumed_right = kernel.assume(theory, proposition)?;
    let right_to_left = kernel.conj(
        theory,
        &rules.conjunction_definition,
        &rules.booleans.true_right,
        &assumed_right,
        &rules.booleans.truth,
    )?;
    from_assumptions(kernel, theory, &left_to_right, &right_to_left)
}

fn conj_false_left(
    kernel: &mut Kernel,
    theory: TheoryId,
    rules: &SimpRules,
    proposition: Term,
) -> Result<Thm> {
    let falsity = kernel.constant(theory, "F", None)?;
    let left = kernel.mk_conj(theory, falsity, proposition)?;
    let assumed_false = kernel.assume(theory, falsity)?;
    let assumed_left = kernel.assume(theory, left)?;
    let left_to_right = kernel.conjunct1(
        theory,
        &rules.conjunction_definition,
        &rules.booleans.truth,
        &assumed_left,
    )?;
    let explosion = kernel.contr(theory, &rules.falsity_rules, &assumed_false, proposition)?;
    let right_to_left = kernel.conj(
        theory,
        &rules.conjunction_definition,
        &rules.booleans.true_right,
        &assumed_false,
        &explosion,
    )?;
    from_assumptions(kernel, theory, &left_to_right, &right_to_left)
}

fn conj_idempotent(
    kernel: &mut Kernel,
    theory: TheoryId,
    rules: &SimpRules,
    proposition: Term,
) -> Result<Thm> {
    let left = kernel.mk_conj(theory, proposition, proposition)?;
    let assumed_left = kernel.assume(theory, left)?;
    let left_to_right = kernel.conjunct1(
        theory,
        &rules.conjunction_definition,
        &rules.booleans.truth,
        &assumed_left,
    )?;
    let assumed = kernel.assume(theory, proposition)?;
    let right_to_left = kernel.conj(
        theory,
        &rules.conjunction_definition,
        &rules.booleans.true_right,
        &assumed,
        &assumed,
    )?;
    from_assumptions(kernel, theory, &left_to_right, &right_to_left)
}

fn imp_true_left(
    kernel: &mut Kernel,
    theory: TheoryId,
    rules: &SimpRules,
    proposition: Term,
) -> Result<Thm> {
    let left = kernel.mk_imp(theory, rules.booleans.true_const, proposition)?;
    let assumed_left = kernel.assume(theory, left)?;
    let left_to_right = kernel.mp(
        theory,
        &rules.implication_rules,
        &assumed_left,
        &rules.booleans.truth,
    )?;
    let assumed_right = kernel.assume(theory, proposition)?;
    let right_to_left = kernel.disch(
        theory,
        &rules.implication_rules,
        rules.booleans.true_const,
        &assumed_right,
    )?;
    from_assumptions(kernel, theory, &left_to_right, &right_to_left)
}

fn imp_true_right(
    kernel: &mut Kernel,
    theory: TheoryId,
    rules: &SimpRules,
    proposition: Term,
) -> Result<Thm> {
    let implication = kernel.disch(
        theory,
        &rules.implication_rules,
        proposition,
        &rules.booleans.truth,
    )?;
    kernel.deduct_antisym_rule(theory, &implication, &rules.booleans.truth)
}

fn imp_false_left(
    kernel: &mut Kernel,
    theory: TheoryId,
    rules: &SimpRules,
    proposition: Term,
) -> Result<Thm> {
    let falsity = kernel.constant(theory, "F", None)?;
    let assumed_false = kernel.assume(theory, falsity)?;
    let explosion = kernel.contr(theory, &rules.falsity_rules, &assumed_false, proposition)?;
    let implication = kernel.disch(theory, &rules.implication_rules, falsity, &explosion)?;
    kernel.deduct_antisym_rule(theory, &implication, &rules.booleans.truth)
}

fn disj_true_left(
    kernel: &mut Kernel,
    theory: TheoryId,
    rules: &SimpRules,
    proposition: Term,
) -> Result<Thm> {
    let disjunction = kernel.disj1(
        theory,
        &rules.disjunction_rules,
        &rules.booleans.truth,
        proposition,
    )?;
    kernel.deduct_antisym_rule(theory, &disjunction, &rules.booleans.truth)
}

fn disj_true_right(
    kernel: &mut Kernel,
    theory: TheoryId,
    rules: &SimpRules,
    proposition: Term,
) -> Result<Thm> {
    let disjunction = kernel.disj2(
        theory,
        &rules.disjunction_rules,
        proposition,
        &rules.booleans.truth,
    )?;
    kernel.deduct_antisym_rule(theory, &disjunction, &rules.booleans.truth)
}

fn disj_false_left(
    kernel: &mut Kernel,
    theory: TheoryId,
    rules: &SimpRules,
    proposition: Term,
) -> Result<Thm> {
    let falsity = kernel.constant(theory, "F", None)?;
    let left = kernel.mk_disj(theory, falsity, proposition)?;
    let assumed_false = kernel.assume(theory, falsity)?;
    let false_case = kernel.contr(theory, &rules.falsity_rules, &assumed_false, proposition)?;
    let assumed_left = kernel.assume(theory, left)?;
    let assumed_right = kernel.assume(theory, proposition)?;
    let left_to_right = kernel.disj_cases(
        theory,
        &rules.disjunction_rules,
        &assumed_left,
        &false_case,
        &assumed_right,
    )?;
    let right_to_left = kernel.disj2(theory, &rules.disjunction_rules, falsity, &assumed_right)?;
    from_assumptions(kernel, theory, &left_to_right, &right_to_left)
}

fn neg_true(kernel: &mut Kernel, theory: TheoryId, rules: &SimpRules) -> Result<Thm> {
    let falsity = kernel.constant(theory, "F", None)?;
    let negation = kernel.mk_neg(theory, rules.booleans.true_const)?;
    let assumed_negation = kernel.assume(theory, negation)?;
    let implication = kernel.not_elim(theory, &rules.negation_rules, &assumed_negation)?;
    let left_to_right = kernel.mp(
        theory,
        &rules.implication_rules,
        &implication,
        &rules.booleans.truth,
    )?;
    let assumed_false = kernel.assume(theory, falsity)?;
    let implication = kernel.disch(
        theory,
        &rules.implication_rules,
        rules.booleans.true_const,
        &assumed_false,
    )?;
    let right_to_left = kernel.not_intro(theory, &rules.negation_rules, &implication)?;
    from_assumptions(kernel, theory, &left_to_right, &right_to_left)
}

fn neg_false(kernel: &mut Kernel, theory: TheoryId, rules: &SimpRules) -> Result<Thm> {
    let falsity = kernel.constant(theory, "F", None)?;
    let assumed_false = kernel.assume(theory, falsity)?;
    let implication = kernel.disch(theory, &rules.implication_rules, falsity, &assumed_false)?;
    let negation = kernel.not_intro(theory, &rules.negation_rules, &implication)?;
    kernel.deduct_antisym_rule(theory, &negation, &rules.booleans.truth)
}

fn forall_true(
    kernel: &mut Kernel,
    theory: TheoryId,
    rules: &SimpRules,
    variable: Term,
) -> Result<Thm> {
    let quantified = kernel.gen(
        theory,
        &rules.universal_definition,
        &rules.booleans.true_right,
        variable,
        &rules.booleans.truth,
    )?;
    kernel.deduct_antisym_rule(theory, &quantified, &rules.booleans.truth)
}

fn from_assumptions(
    kernel: &mut Kernel,
    theory: TheoryId,
    left_to_right: &Thm,
    right_to_left: &Thm,
) -> Result<Thm> {
    let equation = kernel.deduct_antisym_rule(theory, left_to_right, right_to_left)?;
    kernel.sym(theory, &equation)
}
