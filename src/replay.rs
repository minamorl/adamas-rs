//! Turning a certificate into a theorem. Ported from `lib/adamas/replay.rb`.
//!
//! This file is untrusted too — it calls the ten rules and nothing else. Its
//! job is not to be right, it is to be *checkable*. If the rewriter lied about
//! a position, a substitution, which rule applies, or where it all ended up,
//! one of the calls below refuses and there is no theorem. That is precisely
//! why the rewriter above may be as clever, as heuristic and as unverified as
//! anyone likes.
//!
//! In Ruby this was a comment. Here it is a fact the compiler keeps: `replay`
//! lives outside `kernel`, so it *cannot* reach `Thm`'s fields even if a later
//! edit tried to.
//!
//! The shape of the reconstruction is the shape of the certificate:
//!
//! * a step at the root is the rule instantiated, and nothing else;
//! * a step under `rator` or `rand` is that step congruenced back up with
//!   MK_COMB against REFL of the sibling;
//! * a step under `body` is the abstraction opened, the step replayed inside,
//!   and ABS applied — after recorded conditions have either been checked and
//!   discharged, or left as ordinary hypotheses for ABS to check;
//! * the steps are chained with TRANS.

use std::collections::BTreeMap;

use crate::certificate::{Certificate, Condition, RuleSet, Step};
use crate::kernel::{Error, Kernel, Result, Term, TermNode, TheoryId, Thm};
use crate::path::{path_to_string, PathStep};

/// What `descend` remembers on the way down, so `congruence` can rebuild on the
/// way back up.
enum Frame {
    /// Went left; the sibling argument is kept to REFL against.
    Rator(Term),
    /// Went right; REFL of the operator was taken eagerly on the way down.
    Rand(Thm),
    /// Went under a binder; the variable it was opened with.
    Body(Term),
}

impl Kernel {
    /// `⊢ certificate.term = certificate.result`, or a refusal naming the step
    /// that did not hold up.
    pub fn prove_certificate(
        &mut self,
        theory: TheoryId,
        certificate: &Certificate,
        rules: &RuleSet,
    ) -> Result<Thm> {
        let mut chain = self.refl(theory, certificate.term)?;
        for step in &certificate.steps {
            let Some((_, current)) = self.dest_eq(chain.concl()) else {
                return Err(Error::Certificate("the chain lost its equation".into()));
            };
            let next = self.one_step(theory, current, step, rules)?;
            chain = self.trans(theory, &chain, &next)?;
        }
        self.confirm(&chain, certificate)
    }

    /// The rules got somewhere; the certificate said where. They must agree, or
    /// the certificate is describing a different rewrite than the one it did.
    fn confirm(&self, proof: &Thm, certificate: &Certificate) -> Result<Thm> {
        let Some((_, reached)) = self.dest_eq(proof.concl()) else {
            return Err(Error::Certificate("the proof is not an equation".into()));
        };
        if reached == certificate.result {
            return Ok(proof.clone());
        }
        Err(Error::Certificate(format!(
            "the certificate claims {}, but the rules give {}",
            self.term_to_string(certificate.result),
            self.term_to_string(reached)
        )))
    }

    fn one_step(
        &mut self,
        theory: TheoryId,
        term: Term,
        step: &Step,
        rules: &RuleSet,
    ) -> Result<Thm> {
        let (subterm, frames) = self.descend(theory, term, &step.path)?;

        let rule = rules.fetch(&step.rule)?.clone();
        let instantiated = self.instantiate(theory, &rule.thm, step)?;
        let instance = self.discharge_conditions(theory, &instantiated, &step.conditions, rules)?;
        let Some((lhs, _)) = self.dest_eq(instance.concl()) else {
            return Err(Error::Certificate(format!(
                "{} did not instantiate to an equation",
                step.rule
            )));
        };
        if lhs != subterm {
            return Err(Error::Certificate(format!(
                "{} instantiates to {}, but {} holds {}",
                step.rule,
                self.term_to_string(lhs),
                path_to_string(&step.path),
                self.term_to_string(subterm)
            )));
        }

        // Back up through the frames, outermost last.
        let mut proof = instance;
        for frame in frames.into_iter().rev() {
            proof = match frame {
                Frame::Rator(rand) => {
                    let sibling = self.refl(theory, rand)?;
                    self.mk_comb(theory, &proof, &sibling)?
                }
                Frame::Rand(rator_proof) => self.mk_comb(theory, &rator_proof, &proof)?,
                Frame::Body(var) => self.abs(theory, var, &proof)?,
            };
        }
        Ok(proof)
    }

    /// Walks to the position, collecting what it will take to rebuild.
    ///
    /// Iterative on purpose. Certificates can arrive from outside this process,
    /// so path length must not become stack depth — the Ruby original recorded
    /// failing near 6,200 frames on ruby 3.3.8, and Rust's default stack would
    /// give out too.
    fn descend(
        &mut self,
        theory: TheoryId,
        term: Term,
        path: &[PathStep],
    ) -> Result<(Term, Vec<Frame>)> {
        let mut frames = Vec::with_capacity(path.len());
        let mut term = term;
        let mut depth = 0usize;
        for step in path {
            match (step, self.term_node(term).clone()) {
                (PathStep::Rator, TermNode::Comb { rator, rand }) => {
                    frames.push(Frame::Rator(rand));
                    term = rator;
                }
                (PathStep::Rand, TermNode::Comb { rator, rand }) => {
                    let rator_proof = self.refl(theory, rator)?;
                    frames.push(Frame::Rand(rator_proof));
                    term = rand;
                }
                (PathStep::Body, TermNode::Abs { .. }) => {
                    let var = self.path_opener(term, depth)?;
                    frames.push(Frame::Body(var));
                    term = self.open_abs(term, var)?;
                    depth += 1;
                }
                _ => {
                    return Err(Error::Certificate(format!(
                        "the certificate takes {step} of {}, which has no {step}",
                        self.term_to_string(term)
                    )))
                }
            }
        }
        Ok((term, frames))
    }

    /// The rule at the step's substitutions. Types first: the term substitution
    /// is keyed by the rule's variables as written, and those variables only
    /// acquire their concrete types once the type substitution has been
    /// applied.
    fn instantiate(&mut self, theory: TheoryId, rule: &Thm, step: &Step) -> Result<Thm> {
        let thm = if step.type_subst.is_empty() {
            rule.clone()
        } else {
            self.inst_type(theory, &step.type_subst, rule)?
        };
        if step.term_subst.is_empty() {
            return Ok(thm);
        }
        let mut retyped: BTreeMap<Term, Term> = BTreeMap::new();
        for (v, t) in &step.term_subst {
            let key = self.inst_type_term(&step.type_subst, *v)?;
            retyped.insert(key, *t);
        }
        self.inst(theory, &retyped, &thm)
    }

    fn discharge_conditions(
        &mut self,
        theory: TheoryId,
        thm: &Thm,
        conditions: &[Condition],
        rules: &RuleSet,
    ) -> Result<Thm> {
        if thm.hyps().len() != conditions.len() {
            return Err(Error::Certificate(format!(
                "{} condition certificates for {} hypotheses",
                conditions.len(),
                thm.hyps().len()
            )));
        }
        let pairs: Vec<(Term, Condition)> = thm
            .hyps()
            .iter()
            .copied()
            .zip(conditions.iter().cloned())
            .collect();
        let mut acc = thm.clone();
        for (hyp, condition) in pairs {
            acc = match condition {
                Condition::Assumed => acc,
                Condition::Discharged(cert) => {
                    self.discharge_condition(theory, &acc, hyp, &cert, rules)?
                }
            };
        }
        Ok(acc)
    }

    fn discharge_condition(
        &mut self,
        theory: TheoryId,
        thm: &Thm,
        hyp: Term,
        condition: &Certificate,
        rules: &RuleSet,
    ) -> Result<Thm> {
        if condition.term != hyp {
            return Err(Error::Certificate(format!(
                "condition certificate is for {}, not {}",
                self.term_to_string(condition.term),
                self.term_to_string(hyp)
            )));
        }
        let proof = self.prove_certificate(theory, condition, rules)?;
        let truth_const = self.constant(theory, "T", None)?;
        let Some((lhs, rhs)) = self.dest_eq(proof.concl()) else {
            return Err(Error::Certificate(
                "the condition proof is not an equation".into(),
            ));
        };
        if lhs != hyp || rhs != truth_const {
            return Err(Error::Certificate(format!(
                "condition certificate proves {}, not {} = {}",
                self.term_to_string(proof.concl()),
                self.term_to_string(hyp),
                self.term_to_string(truth_const)
            )));
        }
        let truth = self.truth_theorem(theory)?;
        let discharged = self.eqt_elim(theory, &truth, &proof)?;
        self.prove_hyp(theory, &discharged, thm)
    }

    /// `⊢ T`, rebuilt from the theory's own definition of `T` rather than
    /// assumed. If `T` was never defined there is nothing to discharge
    /// conditions with, and that is said rather than worked around.
    pub fn truth_theorem(&mut self, theory: TheoryId) -> Result<Thm> {
        let truth_const = self.constant(theory, "T", None)?;
        let definition = self
            .definitions(theory)
            .iter()
            .find(|thm| self.dest_eq(thm.concl()).map(|(l, _)| l) == Some(truth_const))
            .cloned();
        let Some(definition) = definition else {
            return Err(Error::Certificate(
                "cannot discharge conditions without a definition of T".into(),
            ));
        };
        let Some((_, body)) = self.dest_eq(definition.concl()) else {
            return Err(Error::Certificate(
                "the definition of T is malformed".into(),
            ));
        };
        let Some((witness, _)) = self.dest_eq(body) else {
            return Err(Error::Certificate(
                "the definition of T is not itself an equation".into(),
            ));
        };
        let symmetric = self.sym(theory, &definition)?;
        let reflexive = self.refl(theory, witness)?;
        self.eq_mp(theory, &symmetric, &reflexive)
    }
}
