//! Opt-in classical logic from ETA and SELECT.
//!
//! This follows Ruby adamas's `lib/adamas/logic/classical.rb` derivation in
//! the same order. [`install`] declares choice and asserts exactly ETA then
//! SELECT through [`Kernel::new_axiom`]. Excluded middle is Diaconescu's
//! theorem derived from SELECT; it is never added to the axiom ledger.

use std::collections::BTreeMap;

use crate::kernel::{Error, Kernel, Result, Term, TermNode, TheoryId, Thm, Ty};

use super::LogicBootstrap;

/// The constant, two asserted axioms, and derived excluded-middle theorem
/// installed by [`install`].
#[derive(Clone)]
pub struct ClassicalBundle {
    /// Polymorphic choice, `@ : (A → bool) → A`.
    pub select_const: Term,
    /// `⊢ ∀t. (λx. t x) = t`.
    pub eta_ax: Thm,
    /// `⊢ ∀P x. P x ⇒ P (@ P)`.
    pub select_ax: Thm,
    /// `⊢ ∀t. t ∨ ¬t`, derived from SELECT.
    pub excluded_middle: Thm,
}

#[derive(Clone)]
struct ClassicalAxioms {
    select_const: Term,
    eta_ax: Thm,
    select_ax: Thm,
}

impl From<&ClassicalBundle> for ClassicalAxioms {
    fn from(bundle: &ClassicalBundle) -> Self {
        Self {
            select_const: bundle.select_const,
            eta_ax: bundle.eta_ax.clone(),
            select_ax: bundle.select_ax.clone(),
        }
    }
}

/// Install classical logic as an explicit opt-in.
///
/// The only assertions are ETA followed by SELECT. Excluded middle is then
/// derived from them without calling `new_axiom` again.
pub fn install(
    kernel: &mut Kernel,
    theory: TheoryId,
    boot: &LogicBootstrap,
) -> Result<ClassicalBundle> {
    let a = kernel.ty_var("A")?;
    let ty = select_type(kernel, a)?;
    let select_const = kernel.new_constant(theory, "@", ty)?;
    let eta = eta_axiom(kernel, theory)?;
    let eta_ax = kernel.new_axiom(theory, eta)?;
    let select = select_axiom(kernel, theory, select_const)?;
    let select_ax = kernel.new_axiom(theory, select)?;
    let axioms = ClassicalAxioms {
        select_const,
        eta_ax,
        select_ax,
    };
    let excluded_middle = derive_excluded_middle(kernel, theory, &axioms, boot)?;

    Ok(ClassicalBundle {
        select_const: axioms.select_const,
        eta_ax: axioms.eta_ax,
        select_ax: axioms.select_ax,
        excluded_middle,
    })
}

/// From `Γ ⊢ ∃x. P x`, derive `Γ ⊢ P (@ P)`.
pub fn select_rule(
    kernel: &mut Kernel,
    theory: TheoryId,
    bundle: &ClassicalBundle,
    boot: &LogicBootstrap,
    existential: &Thm,
) -> Result<Thm> {
    let axioms = ClassicalAxioms::from(bundle);
    select_rule_from(kernel, theory, &axioms, boot, existential)
}

/// Derive `⊢ ∀t. t ∨ ¬t` from SELECT using Diaconescu's construction.
pub fn excluded_middle(
    kernel: &mut Kernel,
    theory: TheoryId,
    bundle: &ClassicalBundle,
    boot: &LogicBootstrap,
) -> Result<Thm> {
    let axioms = ClassicalAxioms::from(bundle);
    derive_excluded_middle(kernel, theory, &axioms, boot)
}

/// Specialize the installed excluded-middle theorem at `proposition`.
pub fn em(
    kernel: &mut Kernel,
    theory: TheoryId,
    bundle: &ClassicalBundle,
    boot: &LogicBootstrap,
    proposition: Term,
) -> Result<Thm> {
    kernel.spec(
        theory,
        &boot.universal_definition,
        &boot.truth,
        &bundle.excluded_middle,
        proposition,
    )
}

/// The choice-constant type `(element → bool) → element`.
pub fn select_type(kernel: &mut Kernel, element: Ty) -> Result<Ty> {
    let predicate = kernel.ty_fun(element, kernel.bool_ty())?;
    kernel.ty_fun(predicate, element)
}

fn eta_axiom(kernel: &mut Kernel, theory: TheoryId) -> Result<Term> {
    let a = kernel.ty_var("A")?;
    let b = kernel.ty_var("B")?;
    let function_ty = kernel.ty_fun(a, b)?;
    let function = kernel.term_var("t", function_ty)?;
    let argument = kernel.term_var("x", a)?;
    let application = kernel.term_comb(function, argument)?;
    let expansion = kernel.term_abs(argument, application)?;
    let equality = kernel.term_eq(expansion, function)?;

    kernel.mk_forall(theory, function, equality)
}

fn select_axiom(kernel: &mut Kernel, theory: TheoryId, select_const: Term) -> Result<Term> {
    let a = kernel.ty_var("A")?;
    let predicate_ty = kernel.ty_fun(a, kernel.bool_ty())?;
    let predicate = kernel.term_var("P", predicate_ty)?;
    let witness = kernel.term_var("x", a)?;
    let choice = kernel.term_comb(select_const, predicate)?;
    let selected = kernel.term_comb(predicate, choice)?;
    let instance = kernel.term_comb(predicate, witness)?;
    let body = kernel.mk_imp(theory, instance, selected)?;
    let inner = kernel.mk_forall(theory, witness, body)?;

    kernel.mk_forall(theory, predicate, inner)
}

fn select_rule_from(
    kernel: &mut Kernel,
    theory: TheoryId,
    axioms: &ClassicalAxioms,
    boot: &LogicBootstrap,
    existential: &Thm,
) -> Result<Thm> {
    let Some((element, predicate)) = existential_parts(kernel, existential.concl()) else {
        return Err(Error::Rule(format!(
            "SELECT_RULE: {} is not an existential quantification",
            kernel.term_to_string(existential.concl())
        )));
    };
    let (predicate, existential) = contract_eta(
        kernel,
        theory,
        axioms,
        boot,
        element,
        predicate,
        existential,
    )?;
    let select = select_const(kernel, theory, element)?;
    let choice = kernel.term_comb(select, predicate)?;
    let selected = kernel.term_comb(predicate, choice)?;
    let unfolded = unfold_existential(kernel, theory, boot, element, predicate)?;
    let expanded = kernel.eq_mp(theory, &unfolded, &existential)?;
    let elimination = kernel.spec(
        theory,
        &boot.universal_definition,
        &boot.truth,
        &expanded,
        selected,
    )?;
    let selection = select_axiom_for(kernel, theory, axioms, boot, element, predicate)?;
    let applied = kernel.mp(theory, &boot.implication_rules, &elimination, &selection)?;

    kernel.beta_rule(theory, &applied)
}

fn select_axiom_for(
    kernel: &mut Kernel,
    theory: TheoryId,
    axioms: &ClassicalAxioms,
    boot: &LogicBootstrap,
    element: Ty,
    predicate: Term,
) -> Result<Thm> {
    let a = kernel.ty_var("A")?;
    let axiom = kernel.inst_type(theory, &BTreeMap::from([(a, element)]), &axioms.select_ax)?;
    kernel.spec(
        theory,
        &boot.universal_definition,
        &boot.truth,
        &axiom,
        predicate,
    )
}

fn unfold_existential(
    kernel: &mut Kernel,
    theory: TheoryId,
    boot: &LogicBootstrap,
    element: Ty,
    predicate: Term,
) -> Result<Thm> {
    let definition = &boot.existential_definition;
    let (lhs, _) = kernel.dest_eq(definition.concl()).ok_or_else(|| {
        Error::Rule(format!(
            "EXISTS_DEF: {} is not an equation",
            kernel.term_to_string(definition.concl())
        ))
    })?;
    let wanted = existential_type(kernel, element)?;
    let definition = if kernel.type_of(lhs) == wanted {
        definition.clone()
    } else {
        let a = kernel.ty_var("A")?;
        kernel.inst_type(theory, &BTreeMap::from([(a, element)]), definition)?
    };
    let applied = kernel.ap_thm(theory, &definition, predicate)?;
    kernel.beta_rule(theory, &applied)
}

fn existential_parts(kernel: &Kernel, term: Term) -> Option<(Ty, Term)> {
    let TermNode::Comb {
        rator,
        rand: predicate,
    } = *kernel.term_node(term)
    else {
        return None;
    };
    let TermNode::Const { name, .. } = kernel.term_node(rator) else {
        return None;
    };
    if name != "∃" {
        return None;
    }
    let (element, _) = kernel.dest_fun(kernel.type_of(predicate))?;
    Some((element, predicate))
}

fn contract_eta(
    kernel: &mut Kernel,
    theory: TheoryId,
    axioms: &ClassicalAxioms,
    boot: &LogicBootstrap,
    element: Ty,
    predicate: Term,
    existential: &Thm,
) -> Result<(Term, Thm)> {
    let Some(function) = eta_function(kernel, predicate)? else {
        return Ok((predicate, existential.clone()));
    };

    let a = kernel.ty_var("A")?;
    let b = kernel.ty_var("B")?;
    let axiom = kernel.inst_type(
        theory,
        &BTreeMap::from([(a, element), (b, kernel.bool_ty())]),
        &axioms.eta_ax,
    )?;
    let equality = kernel.spec(
        theory,
        &boot.universal_definition,
        &boot.truth,
        &axiom,
        function,
    )?;
    let quantifier_ty = existential_type(kernel, element)?;
    let quantifier = kernel.constant(theory, "∃", Some(quantifier_ty))?;
    let quantified_equality = kernel.ap_term(theory, quantifier, &equality)?;
    let rewritten = kernel.eq_mp(theory, &quantified_equality, existential)?;

    Ok((function, rewritten))
}

fn eta_function(kernel: &mut Kernel, predicate: Term) -> Result<Option<Term>> {
    if !matches!(kernel.term_node(predicate), TermNode::Abs { .. }) {
        return Ok(None);
    }
    let (variable, body) = kernel.dest_abs(predicate)?;
    let TermNode::Comb { rator, rand } = *kernel.term_node(body) else {
        return Ok(None);
    };
    if rand != variable || kernel.free_in(variable, rator) {
        return Ok(None);
    }
    Ok(Some(rator))
}

fn derive_excluded_middle(
    kernel: &mut Kernel,
    theory: TheoryId,
    axioms: &ClassicalAxioms,
    boot: &LogicBootstrap,
) -> Result<Thm> {
    let proposition = kernel.term_var("t", kernel.bool_ty())?;
    let false_selection = choice(
        kernel,
        theory,
        axioms,
        boot,
        proposition,
        boot.falsity_const,
    )?;
    let true_selection = choice(kernel, theory, axioms, boot, proposition, boot.true_const)?;
    let proof = combine_choices(
        kernel,
        theory,
        boot,
        proposition,
        false_selection,
        true_selection,
    )?;

    kernel.gen(
        theory,
        &boot.universal_definition,
        &boot.booleans.true_right,
        proposition,
        &proof,
    )
}

fn choice(
    kernel: &mut Kernel,
    theory: TheoryId,
    axioms: &ClassicalAxioms,
    boot: &LogicBootstrap,
    proposition: Term,
    witness: Term,
) -> Result<(Term, Thm)> {
    let variable = kernel.term_var("x", kernel.bool_ty())?;
    let equality = kernel.term_eq(variable, witness)?;
    let body = kernel.mk_disj(theory, equality, proposition)?;
    let predicate = kernel.term_abs(variable, body)?;
    let reflexivity = kernel.refl(theory, witness)?;
    let proof = kernel.disj1(theory, &boot.disjunction_rules, &reflexivity, proposition)?;
    let target = kernel.mk_exists(theory, variable, body)?;
    let existential = kernel.exists(theory, &boot.existential_rules, target, witness, &proof)?;
    let selection = select_rule_from(kernel, theory, axioms, boot, &existential)?;

    Ok((predicate, selection))
}

fn combine_choices(
    kernel: &mut Kernel,
    theory: TheoryId,
    boot: &LogicBootstrap,
    proposition: Term,
    false_selection: (Term, Thm),
    true_selection: (Term, Thm),
) -> Result<Thm> {
    let (false_predicate, false_choice) = false_selection;
    let (true_predicate, true_choice) = true_selection;
    let (false_equality, _) = kernel
        .dest_disj(false_choice.concl())
        .ok_or_else(|| Error::Rule("CLASSICAL: false choice is not a disjunction".into()))?;
    let (true_equality, _) = kernel
        .dest_disj(true_choice.concl())
        .ok_or_else(|| Error::Rule("CLASSICAL: true choice is not a disjunction".into()))?;
    let negative = negative_branch(
        kernel,
        theory,
        boot,
        proposition,
        (false_predicate, true_predicate),
        (false_equality, true_equality),
    )?;
    let positive = positive_branch(kernel, theory, boot, proposition)?;
    let after_true = kernel.disj_cases(
        theory,
        &boot.disjunction_rules,
        &true_choice,
        &negative,
        &positive,
    )?;

    kernel.disj_cases(
        theory,
        &boot.disjunction_rules,
        &false_choice,
        &after_true,
        &positive,
    )
}

fn negative_branch(
    kernel: &mut Kernel,
    theory: TheoryId,
    boot: &LogicBootstrap,
    proposition: Term,
    predicates: (Term, Term),
    equalities: (Term, Term),
) -> Result<Thm> {
    let (false_predicate, true_predicate) = predicates;
    let (false_equality, true_equality) = equalities;
    let predicate_equality = predicates_equal_under(
        kernel,
        theory,
        boot,
        proposition,
        false_predicate,
        true_predicate,
    )?;
    let select = select_const(kernel, theory, kernel.bool_ty())?;
    let select_reflexivity = kernel.refl(theory, select)?;
    let selected_equality = kernel.mk_comb(theory, &select_reflexivity, &predicate_equality)?;
    let assumed_false = kernel.assume(theory, false_equality)?;
    let false_to_selected = kernel.sym(theory, &assumed_false)?;
    let false_to_middle = kernel.trans(theory, &false_to_selected, &selected_equality)?;
    let assumed_true = kernel.assume(theory, true_equality)?;
    let false_to_true = kernel.trans(theory, &false_to_middle, &assumed_true)?;
    let true_to_false = kernel.sym(theory, &false_to_true)?;
    let falsity = kernel.eq_mp(theory, &true_to_false, &boot.truth)?;
    let implication = kernel.disch(theory, &boot.implication_rules, proposition, &falsity)?;
    let negation = kernel.not_intro(theory, &boot.negation_rules, &implication)?;

    kernel.disj2(theory, &boot.disjunction_rules, proposition, &negation)
}

fn predicates_equal_under(
    kernel: &mut Kernel,
    theory: TheoryId,
    boot: &LogicBootstrap,
    proposition: Term,
    false_predicate: Term,
    true_predicate: Term,
) -> Result<Thm> {
    let variable = kernel.term_var("x", kernel.bool_ty())?;
    let false_body = kernel.open_abs(false_predicate, variable)?;
    let true_body = kernel.open_abs(true_predicate, variable)?;
    let false_is_true = body_equals_truth(kernel, theory, boot, proposition, false_body)?;
    let true_is_true = body_equals_truth(kernel, theory, boot, proposition, true_body)?;
    let true_is_true = kernel.sym(theory, &true_is_true)?;
    let bodies_equal = kernel.trans(theory, &false_is_true, &true_is_true)?;

    kernel.abs(theory, variable, &bodies_equal)
}

fn body_equals_truth(
    kernel: &mut Kernel,
    theory: TheoryId,
    boot: &LogicBootstrap,
    proposition: Term,
    body: Term,
) -> Result<Thm> {
    let (equality, _) = kernel
        .dest_disj(body)
        .ok_or_else(|| Error::Rule("CLASSICAL: choice body is not a disjunction".into()))?;
    let assumed = kernel.assume(theory, proposition)?;
    let proof = kernel.disj2(theory, &boot.disjunction_rules, equality, &assumed)?;
    let truth_to_body = kernel.deduct_antisym_rule(theory, &boot.truth, &proof)?;
    kernel.sym(theory, &truth_to_body)
}

fn positive_branch(
    kernel: &mut Kernel,
    theory: TheoryId,
    boot: &LogicBootstrap,
    proposition: Term,
) -> Result<Thm> {
    let assumed = kernel.assume(theory, proposition)?;
    let negation = kernel.mk_neg(theory, proposition)?;
    kernel.disj1(theory, &boot.disjunction_rules, &assumed, negation)
}

fn select_const(kernel: &mut Kernel, theory: TheoryId, element: Ty) -> Result<Term> {
    let ty = select_type(kernel, element)?;
    kernel.constant(theory, "@", Some(ty))
}

fn existential_type(kernel: &mut Kernel, element: Ty) -> Result<Ty> {
    let predicate = kernel.ty_fun(element, kernel.bool_ty())?;
    kernel.ty_fun(predicate, kernel.bool_ty())
}
