//! The untrusted half: look for something to do, and write down what was done.
//! Ported from `lib/adamas/rewriter.rb` and the `first_redex` traversal.
//!
//! Nothing here is trusted, and that is the point of the arrangement. It may
//! pick a poor strategy, run out of budget, or be thrown away for something
//! with a proper term index — what it emits is a [`Certificate`], a *claim*,
//! and [`Kernel::prove_certificate`] is where the claim meets the ten rules.
//!
//! The strategy is leftmost-outermost, first matching rule in registration
//! order, repeated until nothing applies or the budget runs out.
//!
//! **Not ported from the Ruby:** the conversion-combinator algebra, in which a
//! strategy is a composable *value* (`Conversion.repeat(first_redex(rewrites))`)
//! so a caller can ask for innermost-first or a single top pass; and the
//! discrimination-tree index that narrows candidate rules before matching. The
//! first is an API for composing strategies, the second is a speed-up: this
//! module tries every rule in order. Neither is load-bearing for soundness —
//! replay refuses a bad step however it was found.

use crate::certificate::{Certificate, Condition, RuleSet, Step};
use crate::kernel::{Error, Kernel, Result, Term, TermNode};
use crate::path::PathStep;

pub const DEFAULT_LIMIT: usize = 200;

/// How to treat a rule that matches its own output.
#[derive(Clone, Copy, PartialEq, Eq, Debug)]
pub enum Ordering {
    /// Every match is allowed. A commutativity law will swap forever, so this
    /// is only safe for a rule set that has none.
    Unordered,
    /// A permutative rule fires only when it makes the term strictly smaller in
    /// the structural term order. Commutativity then stops being a loop and
    /// becomes a sorting pass.
    Ordered,
}

impl Kernel {
    /// A certificate taking `term` towards a normal form.
    ///
    /// `complete` is "nothing else applied", not "the budget was untouched" —
    /// so `limit = 0` still reports that it gave up.
    pub fn rewrite(
        &mut self,
        term: Term,
        rules: &RuleSet,
        limit: usize,
        ordering: Ordering,
    ) -> Result<Certificate> {
        if !self.closed(term) {
            return Err(Error::Type(format!(
                "term has a dangling de Bruijn index: {}",
                self.term_to_string(term)
            )));
        }
        let mut steps = Vec::new();
        let mut current = term;
        let complete = loop {
            if steps.len() >= limit {
                break false;
            }
            match self.one_rewrite(current, rules, ordering)? {
                None => break true,
                Some((step, next)) => {
                    steps.push(step);
                    current = next;
                }
            }
        };
        Ok(Certificate::new(term, steps, current, complete))
    }

    /// `⊢ term = normal_form`, in one call, for when the certificate itself is
    /// not what you wanted. The certificate still goes through replay — this is
    /// a convenience, not a shortcut past the kernel.
    pub fn rewrite_to_theorem(
        &mut self,
        theory: crate::kernel::TheoryId,
        term: Term,
        rules: &RuleSet,
        limit: usize,
        ordering: Ordering,
    ) -> Result<crate::kernel::Thm> {
        let certificate = self.rewrite(term, rules, limit, ordering)?;
        self.prove_certificate(theory, &certificate, rules)
    }

    /// One leftmost-outermost rewrite: the step, and the whole term after it.
    fn one_rewrite(
        &mut self,
        term: Term,
        rules: &RuleSet,
        ordering: Ordering,
    ) -> Result<Option<(Step, Term)>> {
        let mut path = Vec::new();
        let Some((found_path, step, replacement)) =
            self.find_redex(term, rules, ordering, &mut path, 0)?
        else {
            return Ok(None);
        };
        let rewritten = self.replace(term, &found_path, replacement)?;
        Ok(Some((step, rewritten)))
    }

    /// Leftmost-outermost: this node first, then rator, then rand, then under a
    /// binder.
    fn find_redex(
        &mut self,
        term: Term,
        rules: &RuleSet,
        ordering: Ordering,
        path: &mut Vec<PathStep>,
        depth: usize,
    ) -> Result<Option<(Vec<PathStep>, Step, Term)>> {
        if let Some((step, replacement)) = self.try_rules_here(term, rules, ordering, path)? {
            return Ok(Some((path.clone(), step, replacement)));
        }
        match self.term_node(term).clone() {
            TermNode::Comb { rator, rand } => {
                path.push(PathStep::Rator);
                let found = self.find_redex(rator, rules, ordering, path, depth)?;
                path.pop();
                if found.is_some() {
                    return Ok(found);
                }
                path.push(PathStep::Rand);
                let found = self.find_redex(rand, rules, ordering, path, depth)?;
                path.pop();
                Ok(found)
            }
            TermNode::Abs { .. } => {
                // Opened by *position*, the same choice `replace` will make on
                // the way back, so the path means the same thing to both.
                let body = self.open_body(term, depth)?;
                path.push(PathStep::Body);
                let found = self.find_redex(body, rules, ordering, path, depth + 1)?;
                path.pop();
                Ok(found)
            }
            _ => Ok(None),
        }
    }

    fn try_rules_here(
        &mut self,
        term: Term,
        rules: &RuleSet,
        ordering: Ordering,
        path: &[PathStep],
    ) -> Result<Option<(Step, Term)>> {
        let candidates: Vec<crate::certificate::Rule> = rules.iter().cloned().collect();
        for rule in candidates {
            let Some(m) = self.match_pattern(rule.lhs, term, &rule.variables) else {
                continue;
            };
            let replacement = self.instantiate_match(&m, rule.rhs)?;
            if ordering == Ordering::Ordered
                && self.is_permutative(&rule)
                && !self.term_greater(term, replacement)
            {
                continue;
            }
            let step = Step::new(path.to_vec(), &rule.name)
                .with_types(m.type_subst.clone())
                .with_terms(m.term_subst.clone())
                // The rewriter does not try to discharge conditions; it records
                // that it left them standing, and replay checks the count.
                .with_conditions(vec![Condition::Assumed; rule.thm.hyps().len()]);
            return Ok(Some((step, replacement)));
        }
        Ok(None)
    }

    /// A rule is permutative when each side matches the other — `m * n = n * m`
    /// does, `_0 + n = n` does not. This is HOL Light's
    /// `matchable l r && matchable r l`, and it is the whole test for whether a
    /// rule has to be ordered to be usable at all.
    pub fn is_permutative(&self, rule: &crate::certificate::Rule) -> bool {
        self.match_pattern(rule.lhs, rule.rhs, &rule.variables)
            .is_some()
            && self
                .match_pattern(rule.rhs, rule.lhs, &rule.variables)
                .is_some()
    }
}
