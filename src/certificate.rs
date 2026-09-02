//! What an untrusted rewriter claims it did. Ported from
//! `lib/adamas/certificate.rb` and `lib/adamas/rule_set.rb`.

use std::collections::BTreeMap;

use crate::kernel::{Error, Kernel, Result, Term, Thm, Ty};
use crate::path::{path_to_string, PathStep};

/// One claimed rewrite: at `path`, using the rule called `rule`, under these
/// substitutions.
///
/// The substitutions are keyed by the rule's *own* variables, exactly as the
/// rule was registered. Replay applies the type substitution to those keys
/// before instantiating, so a step reads as a statement about the rule rather
/// than about whatever the matcher happened to be looking at.
#[derive(Clone, PartialEq, Eq, Debug)]
pub struct Step {
    pub path: Vec<PathStep>,
    pub rule: String,
    pub type_subst: BTreeMap<Ty, Ty>,
    pub term_subst: BTreeMap<Term, Term>,
    pub conditions: Vec<Condition>,
}

impl Step {
    pub fn new(path: Vec<PathStep>, rule: &str) -> Self {
        Step {
            path,
            rule: rule.to_string(),
            type_subst: BTreeMap::new(),
            term_subst: BTreeMap::new(),
            conditions: Vec::new(),
        }
    }

    pub fn with_terms(mut self, theta: BTreeMap<Term, Term>) -> Self {
        self.term_subst = theta;
        self
    }

    pub fn with_types(mut self, theta: BTreeMap<Ty, Ty>) -> Self {
        self.type_subst = theta;
        self
    }

    pub fn with_conditions(mut self, conditions: Vec<Condition>) -> Self {
        self.conditions = conditions;
        self
    }

    pub fn describe(&self) -> String {
        format!("{}: {}", path_to_string(&self.path), self.rule)
    }
}

/// What a step says about a hypothesis its rule carried in.
///
/// A *condition* travels with its instance — `x ≠ 0 ⊢ x/x = 1` applied to
/// `y/y` should leave `y ≠ 0` to discharge. `Assumed` says the rewriter left it
/// as an ordinary hypothesis; `Discharged` carries a nested certificate that
/// must prove it equal to `T`.
#[derive(Clone, PartialEq, Eq, Debug)]
pub enum Condition {
    Assumed,
    Discharged(Certificate),
}

/// A plan, not a proof.
///
/// A certificate is what an untrusted rewriter *claims* it did: a starting
/// term, a list of steps, and the term it says they lead to. On its own it
/// proves nothing. [`Kernel::prove_certificate`] hands it to the kernel, which
/// either rebuilds it as a theorem out of the ten primitives, or refuses.
///
/// `complete` records whether the rewriter stopped because nothing else
/// applied, or because it ran out of budget. Neither answer is trusted; it is
/// there so a caller can tell "normal form" from "gave up".
#[derive(Clone, PartialEq, Eq, Debug)]
pub struct Certificate {
    pub term: Term,
    pub steps: Vec<Step>,
    pub result: Term,
    pub complete: bool,
}

impl Certificate {
    pub fn new(term: Term, steps: Vec<Step>, result: Term, complete: bool) -> Self {
        Certificate {
            term,
            steps,
            result,
            complete,
        }
    }

    pub fn is_empty(&self) -> bool {
        self.steps.is_empty()
    }

    pub fn len(&self) -> usize {
        self.steps.len()
    }
}

/// A named equational theorem, ready to rewrite with.
#[derive(Clone, PartialEq, Eq, Debug)]
pub struct Rule {
    pub name: String,
    pub thm: Thm,
    pub lhs: Term,
    pub rhs: Term,
    /// The variables a match may instantiate: the free variables of the left
    /// side. Everything else in the pattern has to occur literally.
    pub variables: Vec<Term>,
}

/// Named rules, looked up by a certificate's steps and searched by the
/// rewriter.
///
/// The conditions on registration are not about soundness — replay would refuse
/// a bad step whatever was registered — they are about the rewriter being able
/// to do its job at all:
///
/// * **the right side introduces nothing new**, because a variable matching
///   cannot determine is a variable the rewriter would have to invent;
/// * **hypotheses introduce nothing new**, for the same reason;
/// * **the left side is not a lone variable**, which would match everything,
///   including its own output.
///
/// Order of registration is the order the rewriter tries them in, so it is
/// kept rather than sorted by name.
#[derive(Clone, Default)]
pub struct RuleSet {
    rules: Vec<Rule>,
}

impl RuleSet {
    pub fn new() -> Self {
        RuleSet { rules: Vec::new() }
    }

    pub fn add(&mut self, kernel: &Kernel, name: &str, thm: Thm) -> Result<()> {
        if self.get(name).is_some() {
            return Err(Error::RuleSet(format!(
                "a rule named {name} is already registered"
            )));
        }
        let Some((lhs, rhs)) = kernel.dest_eq(thm.concl()) else {
            return Err(Error::RuleSet(format!(
                "{name}: not an equation ({})",
                kernel.thm_to_string(&thm)
            )));
        };
        if kernel.is_var(lhs) {
            return Err(Error::RuleSet(format!(
                "{name}: the left side is a bare variable"
            )));
        }

        let variables: Vec<Term> = kernel.frees(lhs).to_vec();
        let lhs_type_vars = kernel.term_type_vars(lhs);

        let undetermined = |kernel: &Kernel, side: Term| -> (Vec<String>, Vec<String>) {
            let terms = kernel
                .frees(side)
                .iter()
                .filter(|v| !variables.contains(v))
                .map(|v| kernel.term_to_string(*v))
                .collect();
            let types = kernel
                .term_type_vars(side)
                .into_iter()
                .filter(|t| !lhs_type_vars.contains(t))
                .map(|t| kernel.ty_to_string(t))
                .collect();
            (terms, types)
        };

        for (side, where_) in std::iter::once((rhs, "on the right"))
            .chain(thm.hyps().iter().map(|h| (*h, "in the hypotheses")))
        {
            let (loose_terms, loose_types) = undetermined(kernel, side);
            if !loose_terms.is_empty() {
                return Err(Error::RuleSet(format!(
                    "{name}: {} {where_} is not determined by the left",
                    loose_terms.join(", ")
                )));
            }
            if !loose_types.is_empty() {
                return Err(Error::RuleSet(format!(
                    "{name}: type variable {} {where_} is not determined by the left",
                    loose_types.join(", ")
                )));
            }
        }

        self.rules.push(Rule {
            name: name.to_string(),
            thm,
            lhs,
            rhs,
            variables,
        });
        Ok(())
    }

    pub fn fetch(&self, name: &str) -> Result<&Rule> {
        self.get(name)
            .ok_or_else(|| Error::RuleSet(format!("no such rule: {name}")))
    }

    pub fn get(&self, name: &str) -> Option<&Rule> {
        self.rules.iter().find(|r| r.name == name)
    }

    /// In registration order, which is the order the rewriter tries them in.
    pub fn iter(&self) -> impl Iterator<Item = &Rule> {
        self.rules.iter()
    }

    pub fn names(&self) -> Vec<&str> {
        self.rules.iter().map(|r| r.name.as_str()).collect()
    }

    pub fn len(&self) -> usize {
        self.rules.len()
    }

    pub fn is_empty(&self) -> bool {
        self.rules.is_empty()
    }
}
