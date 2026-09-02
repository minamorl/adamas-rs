//! A small proof-producing decision procedure for propositional formulas.
//!
//! Maximal boolean atoms are split with derived excluded middle. At each leaf,
//! proof-producing contextual substitution replaces the atoms with `T` or `F`
//! and the ordinary logical simp set produces a certificate which replay must
//! accept. Failure is `Ok(None)`, never an assumed atom escaping one branch.

use crate::kernel::{Error, Kernel, Result, Term, TermNode, TheoryId, Thm};
use crate::rewriter::{Ordering, DEFAULT_LIMIT};

use super::classical::{self, ClassicalBundle};
use super::LogicBootstrap;

pub const MAX_ATOMS: usize = 12;

/// Prove a closed propositional tautology, using [`MAX_ATOMS`] as the explicit
/// exponential-search bound.
pub fn prove(
    kernel: &mut Kernel,
    theory: TheoryId,
    boot: &LogicBootstrap,
    classical: &ClassicalBundle,
    term: Term,
) -> Result<Option<Thm>> {
    prove_with_limit(kernel, theory, boot, classical, term, MAX_ATOMS)
}

/// The same procedure with a caller-supplied atom bound.
pub fn prove_with_limit(
    kernel: &mut Kernel,
    theory: TheoryId,
    boot: &LogicBootstrap,
    classical: &ClassicalBundle,
    term: Term,
    max_atoms: usize,
) -> Result<Option<Thm>> {
    if !kernel.closed(term) {
        return Err(Error::Type(format!(
            "TAUT: {} is not closed",
            kernel.term_to_string(term)
        )));
    }
    if kernel.type_of(term) != kernel.bool_ty() {
        return Err(Error::Type(format!(
            "TAUT: {} is not a proposition",
            kernel.term_to_string(term)
        )));
    }

    let normalization = beta_normalize(kernel, theory, term)?;
    let (_, normalized) = kernel.dest_eq(normalization.concl()).ok_or_else(|| {
        Error::Rule("TAUT: beta normalization did not produce an equation".into())
    })?;
    let atoms = atoms(kernel, boot, normalized);
    if atoms.len() > max_atoms {
        return Err(Error::Rule(format!(
            "TAUT: {} atoms exceed the limit of {max_atoms}",
            atoms.len()
        )));
    }

    let Some(proof) = decide(kernel, theory, boot, classical, normalized, &atoms, &[])? else {
        return Ok(None);
    };
    let backwards = kernel.sym(theory, &normalization)?;
    Ok(Some(kernel.eq_mp(theory, &backwards, &proof)?))
}

/// Maximal boolean atoms in first-occurrence order. Logical connectives and
/// boolean equality are decomposed; the constants `T` and `F` are not atoms.
pub fn atoms(kernel: &Kernel, boot: &LogicBootstrap, term: Term) -> Vec<Term> {
    let mut found = Vec::new();
    collect_atoms(kernel, boot, term, &mut found);
    found
}

fn collect_atoms(kernel: &Kernel, boot: &LogicBootstrap, term: Term, found: &mut Vec<Term>) {
    if term == boot.true_const || term == boot.falsity_const {
        return;
    }
    if let Some(parts) = logical_parts(kernel, term).or_else(|| boolean_equality(kernel, term)) {
        for part in parts {
            collect_atoms(kernel, boot, part, found);
        }
    } else if !found.contains(&term) {
        found.push(term);
    }
}

fn logical_parts(kernel: &Kernel, term: Term) -> Option<Vec<Term>> {
    if let Some((left, right)) = kernel.dest_conj(term) {
        return Some(vec![left, right]);
    }
    if let Some((left, right)) = kernel.dest_imp(term) {
        return Some(vec![left, right]);
    }
    if let Some((left, right)) = kernel.dest_disj(term) {
        return Some(vec![left, right]);
    }
    kernel.dest_neg(term).map(|body| vec![body])
}

fn boolean_equality(kernel: &Kernel, term: Term) -> Option<Vec<Term>> {
    let (left, right) = kernel.dest_eq(term)?;
    if kernel.type_of(left) == kernel.bool_ty() {
        Some(vec![left, right])
    } else {
        None
    }
}

fn decide(
    kernel: &mut Kernel,
    theory: TheoryId,
    boot: &LogicBootstrap,
    classical: &ClassicalBundle,
    term: Term,
    atoms: &[Term],
    assignments: &[Thm],
) -> Result<Option<Thm>> {
    let Some((&atom, rest)) = atoms.split_first() else {
        return prove_leaf(kernel, theory, boot, term, assignments);
    };

    let positive = truth_assignment(kernel, theory, boot, atom)?;
    let mut positive_assignments = assignments.to_vec();
    positive_assignments.push(positive);
    let Some(positive_case) = decide(
        kernel,
        theory,
        boot,
        classical,
        term,
        rest,
        &positive_assignments,
    )?
    else {
        return Ok(None);
    };

    let negative = false_assignment(kernel, theory, boot, atom)?;
    let mut negative_assignments = assignments.to_vec();
    negative_assignments.push(negative);
    let Some(negative_case) = decide(
        kernel,
        theory,
        boot,
        classical,
        term,
        rest,
        &negative_assignments,
    )?
    else {
        return Ok(None);
    };

    let excluded_middle = classical::em(kernel, theory, classical, boot, atom)?;
    Ok(Some(kernel.disj_cases(
        theory,
        &boot.disjunction_rules,
        &excluded_middle,
        &positive_case,
        &negative_case,
    )?))
}

fn truth_assignment(
    kernel: &mut Kernel,
    theory: TheoryId,
    boot: &LogicBootstrap,
    atom: Term,
) -> Result<Thm> {
    let assumed = kernel.assume(theory, atom)?;
    kernel.eqt_intro(theory, &boot.booleans.true_right, &assumed)
}

fn false_assignment(
    kernel: &mut Kernel,
    theory: TheoryId,
    boot: &LogicBootstrap,
    atom: Term,
) -> Result<Thm> {
    let negation = kernel.mk_neg(theory, atom)?;
    let assumed = kernel.assume(theory, negation)?;
    kernel.eqf_intro(theory, &boot.negation_rules, &assumed)
}

fn prove_leaf(
    kernel: &mut Kernel,
    theory: TheoryId,
    boot: &LogicBootstrap,
    term: Term,
    assignments: &[Thm],
) -> Result<Option<Thm>> {
    let mut substituted = kernel.refl(theory, term)?;
    for assignment in assignments {
        let (_, current) = kernel
            .dest_eq(substituted.concl())
            .ok_or_else(|| Error::Rule("TAUT: contextual substitution lost its equation".into()))?;
        let step = contextual_substitution(kernel, theory, assignment, current)?;
        substituted = kernel.trans(theory, &substituted, &step)?;
    }
    let (_, normal) = kernel
        .dest_eq(substituted.concl())
        .ok_or_else(|| Error::Rule("TAUT: contextual substitution lost its equation".into()))?;
    let simplified = kernel.rewrite_to_theorem(
        theory,
        normal,
        &boot.rules,
        DEFAULT_LIMIT,
        Ordering::Unordered,
    )?;
    let (_, result) = kernel.dest_eq(simplified.concl()).ok_or_else(|| {
        Error::Rule("TAUT: logical simplification did not produce an equation".into())
    })?;
    if result != boot.true_const {
        return Ok(None);
    }

    let chain = kernel.trans(theory, &substituted, &simplified)?;
    Ok(Some(kernel.eqt_elim(theory, &boot.truth, &chain)?))
}

fn contextual_substitution(
    kernel: &mut Kernel,
    theory: TheoryId,
    equality: &Thm,
    term: Term,
) -> Result<Thm> {
    let (left, _) = kernel
        .dest_eq(equality.concl())
        .ok_or_else(|| Error::Rule("TAUT: assignment is not an equation".into()))?;
    if term == left {
        return Ok(equality.clone());
    }

    match kernel.term_node(term).clone() {
        TermNode::Comb { rator, rand } => {
            let left = contextual_substitution(kernel, theory, equality, rator)?;
            let right = contextual_substitution(kernel, theory, equality, rand)?;
            kernel.mk_comb(theory, &left, &right)
        }
        TermNode::Abs { .. } => {
            let (variable, body) = kernel.dest_abs(term)?;
            let body = contextual_substitution(kernel, theory, equality, body)?;
            kernel.abs(theory, variable, &body)
        }
        _ => kernel.refl(theory, term),
    }
}

fn beta_normalize(kernel: &mut Kernel, theory: TheoryId, term: Term) -> Result<Thm> {
    let mut proof = kernel.refl(theory, term)?;
    loop {
        let (_, current) = kernel
            .dest_eq(proof.concl())
            .ok_or_else(|| Error::Rule("TAUT: beta normalization lost its equation".into()))?;
        let step = kernel.beta_reduce(theory, current)?;
        let (_, reduced) = kernel
            .dest_eq(step.concl())
            .ok_or_else(|| Error::Rule("TAUT: beta normalization lost its equation".into()))?;
        if reduced == current {
            return Ok(proof);
        }
        proof = kernel.trans(theory, &proof, &step)?;
    }
}
