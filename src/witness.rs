//! The two witness algebras used by conversions.
//!
//! [`Theorem`] crosses the trust boundary immediately: every operation calls
//! a public kernel rule. [`Steps`] stays wholly untrusted and records a
//! certificate for replay. A conversion is written once against [`Builder`]
//! and can therefore either prove as it goes or merely describe the same work.

use std::collections::BTreeMap;

use crate::certificate::{Condition, Rule, Step};
use crate::conversion::Conv;
use crate::kernel::{Error, Kernel, Result, Term, TermNode, TheoryId, Thm};
use crate::matching::Match;
use crate::path::PathStep;

/// A value produced by either witness algebra.
///
/// The common `term` / `result` shape is deliberate: combinators do not need
/// to know whether they are carrying a theorem or a list of claimed steps.
/// A theorem witness has `thm = Some(_)`; a steps witness has `thm = None`.
#[derive(Clone, PartialEq, Eq, Debug)]
pub struct Witness {
    pub term: Term,
    pub steps: Vec<Step>,
    pub result: Term,
    pub thm: Option<Thm>,
}

impl Witness {
    /// Construct an untrusted steps witness. This is intentionally public: a
    /// caller may invent any certificate it likes, and replay must still
    /// refuse a lie.
    pub fn steps(term: Term, steps: Vec<Step>, result: Term) -> Self {
        Self {
            term,
            steps,
            result,
            thm: None,
        }
    }

    fn theorem(kernel: &Kernel, thm: Thm) -> Result<Self> {
        let Some((term, result)) = kernel.dest_eq(thm.concl()) else {
            return Err(Error::Certificate(
                "a theorem witness is not an equation".into(),
            ));
        };
        Ok(Self {
            term,
            steps: Vec::new(),
            result,
            thm: Some(thm),
        })
    }
}

/// The protocol implemented by the proof-producing and step-recording
/// algebras. Conversion failure is not represented here: it is the outer
/// `Option` returned by [`Conv::call`]. Every error from these operations is a
/// real error and is propagated by combinators.
pub trait Builder {
    fn refl(&self, kernel: &mut Kernel, term: Term) -> Result<Witness>;

    fn rewrite(
        &self,
        kernel: &mut Kernel,
        term: Term,
        rule: &Rule,
        matched: &Match,
        conditions: Option<&Conv>,
    ) -> Result<Witness>;

    fn seq(&self, kernel: &mut Kernel, left: Witness, right: Witness) -> Result<Witness>;

    fn comb(&self, kernel: &mut Kernel, rator: Witness, rand: Witness) -> Result<Witness>;

    fn under(
        &self,
        kernel: &mut Kernel,
        abstraction: Term,
        var: Term,
        witness: Witness,
    ) -> Result<Witness>;
}

/// Proof-producing witness algebra.
#[derive(Clone, Copy, PartialEq, Eq, Debug)]
pub struct Theorem {
    theory: TheoryId,
}

impl Theorem {
    pub fn new(theory: TheoryId) -> Self {
        Self { theory }
    }

    pub fn theory(&self) -> TheoryId {
        self.theory
    }

    fn require_theorem(witness: &Witness) -> Result<&Thm> {
        witness
            .thm
            .as_ref()
            .ok_or_else(|| Error::Certificate("the theorem witness has no theorem".into()))
    }

    /// Type instantiation precedes term instantiation, because the term
    /// substitution is keyed by the variables as written in the rule.
    fn instantiate(&self, kernel: &mut Kernel, rule: &Rule, matched: &Match) -> Result<Thm> {
        let mut thm = if matched.type_subst.is_empty() {
            rule.thm.clone()
        } else {
            kernel.inst_type(self.theory, &matched.type_subst, &rule.thm)?
        };
        if matched.term_subst.is_empty() {
            return Ok(thm);
        }

        let mut retyped = BTreeMap::new();
        for (var, value) in &matched.term_subst {
            let key = kernel.inst_type_term(&matched.type_subst, *var)?;
            retyped.insert(key, *value);
        }
        thm = kernel.inst(self.theory, &retyped, &thm)?;
        Ok(thm)
    }

    fn discharge(
        &self,
        kernel: &mut Kernel,
        mut thm: Thm,
        conditions: Option<&Conv>,
    ) -> Result<Thm> {
        let Some(conditions) = conditions else {
            return Ok(thm);
        };
        let truth_const = kernel.constant(self.theory, "T", None)?;
        let hypotheses = thm.hyps().to_vec();
        for hypothesis in hypotheses {
            let proof = conditions.call(kernel, self, hypothesis, 0)?;
            let Some(proof) = proof else {
                continue;
            };
            if proof.result != truth_const {
                continue;
            }
            let equation = Self::require_theorem(&proof)?;
            let truth = kernel.truth_theorem(self.theory)?;
            let proved_hypothesis = kernel.eqt_elim(self.theory, &truth, equation)?;
            thm = kernel.prove_hyp(self.theory, &proved_hypothesis, &thm)?;
        }
        Ok(thm)
    }
}

impl Builder for Theorem {
    fn refl(&self, kernel: &mut Kernel, term: Term) -> Result<Witness> {
        let theorem = kernel.refl(self.theory, term)?;
        Witness::theorem(kernel, theorem)
    }

    fn rewrite(
        &self,
        kernel: &mut Kernel,
        _term: Term,
        rule: &Rule,
        matched: &Match,
        conditions: Option<&Conv>,
    ) -> Result<Witness> {
        let instantiated = self.instantiate(kernel, rule, matched)?;
        let discharged = self.discharge(kernel, instantiated, conditions)?;
        Witness::theorem(kernel, discharged)
    }

    fn seq(&self, kernel: &mut Kernel, left: Witness, right: Witness) -> Result<Witness> {
        let left_thm = Self::require_theorem(&left)?;
        let right_thm = Self::require_theorem(&right)?;
        let left_reflexive = kernel
            .dest_eq(left_thm.concl())
            .map(|(lhs, rhs)| lhs == rhs)
            .unwrap_or(false);
        if left_reflexive {
            return Ok(right);
        }
        let right_reflexive = kernel
            .dest_eq(right_thm.concl())
            .map(|(lhs, rhs)| lhs == rhs)
            .unwrap_or(false);
        if right_reflexive {
            return Ok(left);
        }
        let theorem = kernel.trans(self.theory, left_thm, right_thm)?;
        Witness::theorem(kernel, theorem)
    }

    fn comb(&self, kernel: &mut Kernel, rator: Witness, rand: Witness) -> Result<Witness> {
        let theorem = kernel.mk_comb(
            self.theory,
            Self::require_theorem(&rator)?,
            Self::require_theorem(&rand)?,
        )?;
        Witness::theorem(kernel, theorem)
    }

    fn under(
        &self,
        kernel: &mut Kernel,
        _abstraction: Term,
        var: Term,
        witness: Witness,
    ) -> Result<Witness> {
        let theorem = kernel.abs(self.theory, var, Self::require_theorem(&witness)?)?;
        Witness::theorem(kernel, theorem)
    }
}

/// Certificate-step witness algebra.
#[derive(Clone, Copy, Default, PartialEq, Eq, Debug)]
pub struct Steps;

impl Steps {
    pub fn new() -> Self {
        Self
    }

    fn prefix(head: PathStep, steps: &[Step]) -> Vec<Step> {
        steps
            .iter()
            .map(|step| {
                let mut path = Vec::with_capacity(step.path.len() + 1);
                path.push(head);
                path.extend_from_slice(&step.path);
                Step::new(path, &step.rule)
                    .with_types(step.type_subst.clone())
                    .with_terms(step.term_subst.clone())
                    .with_conditions(step.conditions.clone())
            })
            .collect()
    }

    fn is_truth(kernel: &Kernel, term: Term) -> bool {
        matches!(
            kernel.term_node(term),
            TermNode::Const { name, ty } if name == "T" && *ty == kernel.bool_ty()
        )
    }

    fn solved_conditions(
        &self,
        kernel: &mut Kernel,
        rule: &Rule,
        matched: &Match,
        conditions: Option<&Conv>,
    ) -> Result<Vec<Condition>> {
        let mut solved = Vec::with_capacity(rule.thm.hyps().len());
        for hypothesis in rule.thm.hyps() {
            let hypothesis = kernel.instantiate_match(matched, *hypothesis)?;
            let certificate = match conditions {
                Some(conv) => Some(conv.certify(kernel, hypothesis)?),
                None => None,
            };
            let condition = match certificate {
                Some(certificate) if Self::is_truth(kernel, certificate.result) => {
                    Condition::Discharged(certificate)
                }
                _ => Condition::Assumed,
            };
            solved.push(condition);
        }
        Ok(solved)
    }
}

impl Builder for Steps {
    fn refl(&self, _kernel: &mut Kernel, term: Term) -> Result<Witness> {
        Ok(Witness::steps(term, Vec::new(), term))
    }

    fn rewrite(
        &self,
        kernel: &mut Kernel,
        term: Term,
        rule: &Rule,
        matched: &Match,
        conditions: Option<&Conv>,
    ) -> Result<Witness> {
        let condition_steps = self.solved_conditions(kernel, rule, matched, conditions)?;
        let step = Step::new(Vec::new(), &rule.name)
            .with_types(matched.type_subst.clone())
            .with_terms(matched.term_subst.clone())
            .with_conditions(condition_steps);
        let result = kernel.instantiate_match(matched, rule.rhs)?;
        Ok(Witness::steps(term, vec![step], result))
    }

    fn seq(&self, _kernel: &mut Kernel, left: Witness, right: Witness) -> Result<Witness> {
        if left.steps.is_empty() {
            return Ok(right);
        }
        if right.steps.is_empty() {
            return Ok(left);
        }
        let mut steps = left.steps;
        steps.extend(right.steps);
        Ok(Witness::steps(left.term, steps, right.result))
    }

    fn comb(&self, kernel: &mut Kernel, rator: Witness, rand: Witness) -> Result<Witness> {
        let term = kernel.term_comb(rator.term, rand.term)?;
        let result = kernel.term_comb(rator.result, rand.result)?;
        let mut steps = Self::prefix(PathStep::Rator, &rator.steps);
        steps.extend(Self::prefix(PathStep::Rand, &rand.steps));
        Ok(Witness::steps(term, steps, result))
    }

    fn under(
        &self,
        kernel: &mut Kernel,
        abstraction: Term,
        var: Term,
        witness: Witness,
    ) -> Result<Witness> {
        let TermNode::Abs { binder_name, .. } = kernel.term_node(abstraction).clone() else {
            return Err(Error::Path(
                "cannot build a witness under a non-abstraction".into(),
            ));
        };
        let result = kernel.term_abs_named(&binder_name, var, witness.result)?;
        Ok(Witness::steps(
            abstraction,
            Self::prefix(PathStep::Body, &witness.steps),
            result,
        ))
    }
}
