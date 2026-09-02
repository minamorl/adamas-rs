//! The untrusted half: look for something to do, and write down what was done.
//! Ported from `lib/adamas/rewriter.rb`.
//!
//! Nothing here is trusted, and that is the point of the arrangement. It may
//! pick a poor strategy, run out of budget, or be thrown away for something
//! with a proper term index — what it emits is a [`Certificate`], a *claim*,
//! and [`Kernel::prove_certificate`] is where the claim meets the ten rules.
//!
//! The default is now expressed as the value
//! `repeat(first_redex(rewrites), limit)`. Callers may inject another function
//! from leaf conversion to strategy without changing either witness algebra.

use crate::certificate::{Certificate, RuleSet};
use crate::conversion::{first_redex, repeat, rewrites_with, Conv};
use crate::kernel::{Error, Kernel, Result, Term};
use crate::witness::Steps;

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
        self.rewrite_with_strategy(term, rules, limit, ordering, first_redex)
    }

    /// The same rewriter with an explicit conversion strategy.
    ///
    /// `strategy` receives the leaf conversion and returns the traversal to
    /// repeat. The repeat budget counts successful strategy invocations, just
    /// as Ruby's `Rewriter` does; the default `first_redex` emits one step per
    /// invocation and therefore preserves the earlier public behaviour.
    pub fn rewrite_with_strategy<F>(
        &mut self,
        term: Term,
        rules: &RuleSet,
        limit: usize,
        ordering: Ordering,
        strategy: F,
    ) -> Result<Certificate>
    where
        F: FnOnce(Conv) -> Conv,
    {
        if !self.closed(term) {
            return Err(Error::Type(format!(
                "term has a dangling de Bruijn index: {}",
                self.term_to_string(term)
            )));
        }
        let leaf = rewrites_with(rules, None, ordering == Ordering::Ordered);
        let repeated = repeat(strategy(leaf), limit);
        let outcome = repeated.run(self, &Steps::new(), term, 0)?;
        let complete = outcome.stopped_by_nil();
        Ok(Certificate::new(
            term,
            outcome.witness.steps,
            outcome.witness.result,
            complete,
        ))
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
