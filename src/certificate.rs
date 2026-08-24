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
}

/// Named rules, looked up by a certificate's steps.
///
/// The Ruby original also refuses, at registration, a rule whose right side or
/// hypotheses introduce variables the left side cannot determine, and a rule
/// whose left side is a lone variable. **Those checks are not ported here**,
/// and their absence is not a soundness gap: they exist so the *rewriter* can
/// do its job, and replay refuses a bad step whatever was registered. What is
/// kept is the one check replay itself relies on — a rule must be an equation.
#[derive(Default)]
pub struct RuleSet {
    rules: BTreeMap<String, Rule>,
}

impl RuleSet {
    pub fn new() -> Self {
        RuleSet {
            rules: BTreeMap::new(),
        }
    }

    pub fn add(&mut self, kernel: &Kernel, name: &str, thm: Thm) -> Result<()> {
        if self.rules.contains_key(name) {
            return Err(Error::RuleSet(format!(
                "a rule named {name} is already registered"
            )));
        }
        let Some((lhs, rhs)) = kernel.dest_eq(thm.concl()) else {
            return Err(Error::RuleSet(format!(
                "{name} is not an equation: {}",
                kernel.term_to_string(thm.concl())
            )));
        };
        self.rules.insert(
            name.to_string(),
            Rule {
                name: name.to_string(),
                thm,
                lhs,
                rhs,
            },
        );
        Ok(())
    }

    pub fn fetch(&self, name: &str) -> Result<&Rule> {
        self.rules
            .get(name)
            .ok_or_else(|| Error::RuleSet(format!("no such rule: {name}")))
    }

    pub fn get(&self, name: &str) -> Option<&Rule> {
        self.rules.get(name)
    }

    pub fn names(&self) -> Vec<&str> {
        self.rules.keys().map(|s| s.as_str()).collect()
    }

    pub fn len(&self) -> usize {
        self.rules.len()
    }

    pub fn is_empty(&self) -> bool {
        self.rules.is_empty()
    }
}
