//! Composable, untrusted rewrite strategies.
//!
//! This is the Rust form of Ruby adamas's `Conversion`: conversions are
//! values, failure is `Ok(None)`, and a genuine error remains `Err`. The same
//! value runs over either theorem-producing or certificate-recording witness
//! algebra, so strategy and trust boundary stay independent.

use std::rc::Rc;

use crate::certificate::{Certificate, RuleSet};
use crate::kernel::{Error, Kernel, Result, Term, TermNode, TheoryId, Thm};
use crate::witness::{Builder, Steps, Theorem, Witness};

type Operation = dyn Fn(&mut Kernel, &dyn Builder, Term, usize) -> Result<Option<Witness>>;

/// A conversion: a partial, proof-aware transformation of one whole term.
#[derive(Clone)]
pub struct Conv {
    operation: Rc<Operation>,
}

impl std::fmt::Debug for Conv {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        f.write_str("Conv(..)")
    }
}

impl Conv {
    pub fn new<F>(operation: F) -> Self
    where
        F: Fn(&mut Kernel, &dyn Builder, Term, usize) -> Result<Option<Witness>> + 'static,
    {
        Self {
            operation: Rc::new(operation),
        }
    }

    pub fn call(
        &self,
        kernel: &mut Kernel,
        build: &dyn Builder,
        term: Term,
        depth: usize,
    ) -> Result<Option<Witness>> {
        (self.operation)(kernel, build, term, depth)
    }

    /// `THENC`: the second conversion sees the first conversion's result.
    pub fn then_c(self, other: Conv) -> Conv {
        Conv::new(move |kernel, build, term, depth| {
            let Some(first) = self.call(kernel, build, term, depth)? else {
                return Ok(None);
            };
            let Some(second) = other.call(kernel, build, first.result, depth)? else {
                return Ok(None);
            };
            Ok(Some(build.seq(kernel, first, second)?))
        })
    }

    /// `ORELSEC`: fall through only for conversion failure, never for `Err`.
    pub fn or_else(self, other: Conv) -> Conv {
        Conv::new(move |kernel, build, term, depth| {
            match self.call(kernel, build, term, depth)? {
                Some(witness) => Ok(Some(witness)),
                None => other.call(kernel, build, term, depth),
            }
        })
    }

    pub fn try_conv(self) -> Conv {
        self.or_else(all_conv())
    }

    /// Prove the conversion result directly through the theorem algebra.
    pub fn prove(&self, kernel: &mut Kernel, theory: TheoryId, term: Term) -> Result<Thm> {
        let build = Theorem::new(theory);
        let witness = match self.call(kernel, &build, term, 0)? {
            Some(witness) => witness,
            None => build.refl(kernel, term)?,
        };
        witness
            .thm
            .ok_or_else(|| Error::Certificate("a theorem conversion emitted no theorem".into()))
    }

    /// Record the same conversion as replayable steps.
    pub fn certify(&self, kernel: &mut Kernel, term: Term) -> Result<Certificate> {
        if !kernel.closed(term) {
            return Err(Error::Type(format!(
                "term has a dangling de Bruijn index: {}",
                kernel.term_to_string(term)
            )));
        }
        let build = Steps::new();
        let witness = match self.call(kernel, &build, term, 0)? {
            Some(witness) => witness,
            None => build.refl(kernel, term)?,
        };
        let rerun = self.call(kernel, &build, witness.result, 0)?;
        let complete = rerun.map(|next| next.steps.is_empty()).unwrap_or(true);
        Ok(Certificate::new(
            term,
            witness.steps,
            witness.result,
            complete,
        ))
    }
}

/// `ALL_CONV`: reflexive success.
pub fn all_conv() -> Conv {
    Conv::new(|kernel, build, term, _| Ok(Some(build.refl(kernel, term)?)))
}

/// `NO_CONV`: ordinary conversion failure.
pub fn no_conv() -> Conv {
    Conv::new(|_, _, _, _| Ok(None))
}

/// Rewrite the whole term with one named rule (`REWR_CONV`).
pub fn rewr(rules: &RuleSet, name: &str) -> Conv {
    rewr_with_conditions(rules, name, None)
}

pub fn rewr_with_conditions(rules: &RuleSet, name: &str, conditions: Option<Conv>) -> Conv {
    let rules = rules.clone();
    let name = name.to_string();
    Conv::new(move |kernel, build, term, _| {
        // Fetch is deliberately inside the call. A missing rule is an error,
        // and ORELSEC must not turn it into ordinary non-applicability.
        let rule = rules.fetch(&name)?;
        let Some(matched) = kernel.match_pattern(rule.lhs, term, &rule.variables) else {
            return Ok(None);
        };
        Ok(Some(build.rewrite(
            kernel,
            term,
            rule,
            &matched,
            conditions.as_ref(),
        )?))
    })
}

/// First matching rule in registration order (`REWRITES_CONV`).
pub fn rewrites(rules: &RuleSet) -> Conv {
    rewrites_with(rules, None, false)
}

/// Configurable form of [`rewrites`]. With `ordered = true`, only
/// *permutative* rules are guarded by the term order.
pub fn rewrites_with(rules: &RuleSet, conditions: Option<Conv>, ordered: bool) -> Conv {
    let rules = rules.clone();
    Conv::new(move |kernel, build, term, _| {
        for rule in rules.iter() {
            let Some(matched) = kernel.match_pattern(rule.lhs, term, &rule.variables) else {
                continue;
            };
            if ordered && kernel.is_permutative(rule) {
                let result = kernel.instantiate_match(&matched, rule.rhs)?;
                if !kernel.term_greater(term, result) {
                    continue;
                }
            }
            return Ok(Some(build.rewrite(
                kernel,
                term,
                rule,
                &matched,
                conditions.as_ref(),
            )?));
        }
        Ok(None)
    })
}

/// `ORDERED_REWR_CONV`: unlike ordered [`rewrites_with`], this guards every
/// match, not only rules recognised as permutative.
pub fn ordered_rewr(rules: &RuleSet, name: &str) -> Conv {
    ordered_rewr_with_conditions(rules, name, None)
}

pub fn ordered_rewr_with_conditions(rules: &RuleSet, name: &str, conditions: Option<Conv>) -> Conv {
    let rules = rules.clone();
    let name = name.to_string();
    Conv::new(move |kernel, build, term, _| {
        let rule = rules.fetch(&name)?;
        let Some(matched) = kernel.match_pattern(rule.lhs, term, &rule.variables) else {
            return Ok(None);
        };
        let result = kernel.instantiate_match(&matched, rule.rhs)?;
        if !kernel.term_greater(term, result) {
            return Ok(None);
        }
        Ok(Some(build.rewrite(
            kernel,
            term,
            rule,
            &matched,
            conditions.as_ref(),
        )?))
    })
}

#[derive(Clone, Copy, PartialEq, Eq, Debug)]
pub enum RepeatReason {
    Nil,
    Limit,
}

#[derive(Clone, PartialEq, Eq, Debug)]
pub struct RepeatResult {
    pub witness: Witness,
    pub reason: RepeatReason,
}

impl RepeatResult {
    pub fn stopped_by_nil(&self) -> bool {
        self.reason == RepeatReason::Nil
    }

    pub fn exhausted(&self) -> bool {
        self.reason == RepeatReason::Limit
    }
}

/// Bounded repetition. A reflexive success still consumes one unit; `None`
/// and an exhausted limit remain distinguishable in [`RepeatResult`].
#[derive(Clone, Debug)]
pub struct Repeat {
    pub conv: Conv,
    pub limit: usize,
}

impl Repeat {
    pub fn run(
        &self,
        kernel: &mut Kernel,
        build: &dyn Builder,
        term: Term,
        depth: usize,
    ) -> Result<RepeatResult> {
        let mut current = build.refl(kernel, term)?;
        for _ in 0..self.limit {
            let Some(step) = self.conv.call(kernel, build, current.result, depth)? else {
                return Ok(RepeatResult {
                    witness: current,
                    reason: RepeatReason::Nil,
                });
            };
            current = build.seq(kernel, current, step)?;
        }
        Ok(RepeatResult {
            witness: current,
            reason: RepeatReason::Limit,
        })
    }

    pub fn as_conv(&self) -> Conv {
        let repeated = self.clone();
        Conv::new(move |kernel, build, term, depth| {
            Ok(Some(repeated.run(kernel, build, term, depth)?.witness))
        })
    }

    pub fn call(
        &self,
        kernel: &mut Kernel,
        build: &dyn Builder,
        term: Term,
        depth: usize,
    ) -> Result<Option<Witness>> {
        self.as_conv().call(kernel, build, term, depth)
    }

    pub fn prove(&self, kernel: &mut Kernel, theory: TheoryId, term: Term) -> Result<Thm> {
        self.as_conv().prove(kernel, theory, term)
    }

    pub fn certify(&self, kernel: &mut Kernel, term: Term) -> Result<Certificate> {
        self.as_conv().certify(kernel, term)
    }

    pub fn then_c(self, other: Conv) -> Conv {
        self.as_conv().then_c(other)
    }

    pub fn or_else(self, other: Conv) -> Conv {
        self.as_conv().or_else(other)
    }

    pub fn try_conv(self) -> Conv {
        self.as_conv().try_conv()
    }
}

impl From<Repeat> for Conv {
    fn from(repeated: Repeat) -> Self {
        repeated.as_conv()
    }
}

pub fn repeat(conv: Conv, limit: usize) -> Repeat {
    Repeat { conv, limit }
}

/// Convert both immediate children, treating a failed child as reflexivity.
pub fn sub(conv: Conv) -> Conv {
    Conv::new(move |kernel, build, term, depth| {
        Ok(Some(sub_witness(kernel, build, &conv, term, depth)?))
    })
}

pub fn comb_conv(conv: Conv) -> Conv {
    Conv::new(move |kernel, build, term, depth| {
        if !matches!(kernel.term_node(term), TermNode::Comb { .. }) {
            return Ok(None);
        }
        Ok(Some(comb_witness(kernel, build, &conv, term, depth)?))
    })
}

pub fn abs_conv(conv: Conv) -> Conv {
    Conv::new(move |kernel, build, term, depth| {
        if !matches!(kernel.term_node(term), TermNode::Abs { .. }) {
            return Ok(None);
        }
        Ok(Some(abs_witness(kernel, build, &conv, term, depth)?))
    })
}

fn sub_witness(
    kernel: &mut Kernel,
    build: &dyn Builder,
    conv: &Conv,
    term: Term,
    depth: usize,
) -> Result<Witness> {
    match kernel.term_node(term) {
        TermNode::Comb { .. } => comb_witness(kernel, build, conv, term, depth),
        TermNode::Abs { .. } => abs_witness(kernel, build, conv, term, depth),
        _ => build.refl(kernel, term),
    }
}

fn comb_witness(
    kernel: &mut Kernel,
    build: &dyn Builder,
    conv: &Conv,
    term: Term,
    depth: usize,
) -> Result<Witness> {
    let TermNode::Comb { rator, rand } = kernel.term_node(term).clone() else {
        return Err(Error::Path("COMB_CONV applied to a non-combination".into()));
    };
    let rator_witness = match conv.call(kernel, build, rator, depth)? {
        Some(witness) => witness,
        None => build.refl(kernel, rator)?,
    };
    let rand_witness = match conv.call(kernel, build, rand, depth)? {
        Some(witness) => witness,
        None => build.refl(kernel, rand)?,
    };
    build.comb(kernel, rator_witness, rand_witness)
}

fn abs_witness(
    kernel: &mut Kernel,
    build: &dyn Builder,
    conv: &Conv,
    term: Term,
    depth: usize,
) -> Result<Witness> {
    let var = kernel.path_opener(term, depth)?;
    let body = kernel.open_abs(term, var)?;
    let witness = match conv.call(kernel, build, body, depth + 1)? {
        Some(witness) => witness,
        None => build.refl(kernel, body)?,
    };
    if let Some(theorem) = &witness.thm {
        let blocked: Vec<Term> = theorem
            .hyps()
            .iter()
            .copied()
            .filter(|hypothesis| kernel.free_in(var, *hypothesis))
            .collect();
        if !blocked.is_empty() {
            let rendered = blocked
                .iter()
                .map(|hypothesis| kernel.term_to_string(*hypothesis))
                .collect::<Vec<_>>()
                .join(", ");
            return Err(Error::Rule(format!(
                "cannot abstract a conversion: {} is free in {rendered}",
                kernel.term_to_string(var)
            )));
        }
    }
    build.under(kernel, term, var, witness)
}

/// Bottom-up, repeating the conversion at each node.
pub fn depth(conv: Conv, limit: usize) -> Conv {
    Conv::new(move |kernel, build, term, current_depth| {
        let below = sub(depth(conv.clone(), limit));
        let here = repeat(conv.clone(), limit).as_conv();
        below.then_c(here).call(kernel, build, term, current_depth)
    })
}

/// Bottom-up, revisiting descendants after every successful rewrite.
pub fn redepth(conv: Conv) -> Conv {
    Conv::new(move |kernel, build, term, current_depth| {
        let below = sub(redepth(conv.clone()));
        let revisit = conv
            .clone()
            .then_c(redepth(conv.clone()))
            .or_else(all_conv());
        below
            .then_c(revisit)
            .call(kernel, build, term, current_depth)
    })
}

/// Top-down, first applicable redex independently on each branch.
pub fn once_depth(conv: Conv) -> Conv {
    Conv::new(move |kernel, build, term, current_depth| {
        conv.clone()
            .or_else(sub(once_depth(conv.clone())))
            .call(kernel, build, term, current_depth)
    })
}

/// Top-down, repeating at each parent before descending.
pub fn top_down(conv: Conv, limit: usize) -> Conv {
    Conv::new(move |kernel, build, term, current_depth| {
        repeat(conv.clone(), limit)
            .as_conv()
            .then_c(sub(top_down(conv.clone(), limit)))
            .call(kernel, build, term, current_depth)
    })
}

/// Leftmost-outermost, with at most one redex in the whole term.
pub fn first_redex(conv: Conv) -> Conv {
    Conv::new(
        move |kernel, build, term, depth| match conv.call(kernel, build, term, depth)? {
            Some(witness) => Ok(Some(witness)),
            None => first_redex_below(kernel, build, &conv, term, depth),
        },
    )
}

fn first_redex_below(
    kernel: &mut Kernel,
    build: &dyn Builder,
    conv: &Conv,
    term: Term,
    depth: usize,
) -> Result<Option<Witness>> {
    match kernel.term_node(term) {
        TermNode::Comb { .. } => first_redex_comb(kernel, build, conv, term, depth),
        TermNode::Abs { .. } => first_redex_abs(kernel, build, conv, term, depth),
        _ => Ok(None),
    }
}

fn first_redex_comb(
    kernel: &mut Kernel,
    build: &dyn Builder,
    conv: &Conv,
    term: Term,
    depth: usize,
) -> Result<Option<Witness>> {
    let TermNode::Comb { rator, rand } = kernel.term_node(term).clone() else {
        return Ok(None);
    };
    if let Some(rator_witness) = first_redex(conv.clone()).call(kernel, build, rator, depth)? {
        let rand_witness = build.refl(kernel, rand)?;
        return Ok(Some(build.comb(kernel, rator_witness, rand_witness)?));
    }
    let Some(rand_witness) = first_redex(conv.clone()).call(kernel, build, rand, depth)? else {
        return Ok(None);
    };
    let rator_witness = build.refl(kernel, rator)?;
    Ok(Some(build.comb(kernel, rator_witness, rand_witness)?))
}

fn first_redex_abs(
    kernel: &mut Kernel,
    build: &dyn Builder,
    conv: &Conv,
    term: Term,
    depth: usize,
) -> Result<Option<Witness>> {
    let var = kernel.path_opener(term, depth)?;
    let body = kernel.open_abs(term, var)?;
    let Some(witness) = first_redex(conv.clone()).call(kernel, build, body, depth + 1)? else {
        return Ok(None);
    };
    if let Some(theorem) = &witness.thm {
        if !theorem.hyps().is_empty() {
            let hypotheses = theorem
                .hyps()
                .iter()
                .map(|hypothesis| kernel.term_to_string(*hypothesis))
                .collect::<Vec<_>>()
                .join(", ");
            return Err(Error::Rule(format!(
                "cannot abstract a conversion with hypotheses: {hypotheses}"
            )));
        }
    }
    Ok(Some(build.under(kernel, term, var, witness)?))
}
