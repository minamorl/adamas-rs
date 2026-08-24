//! First-order matching of a rewrite rule's left side against a term.
//! Ported from `lib/adamas/matching.rb`.
//!
//! Untrusted. A wrong answer here produces a certificate step that replay
//! refuses — never a theorem that is false. That freedom is why this file can
//! be replaced by something faster or cleverer without anyone re-auditing the
//! kernel.

use std::collections::BTreeMap;

use crate::kernel::{Kernel, Result, Term, TermNode, Ty};

/// The substitutions that turn a pattern into a term.
#[derive(Clone, PartialEq, Eq, Debug, Default)]
pub struct Match {
    pub type_subst: BTreeMap<Ty, Ty>,
    pub term_subst: BTreeMap<Term, Term>,
}

impl Kernel {
    /// The substitutions that turn `pattern` into `term`, or `None` if there
    /// are none. `variables` are the pattern's instantiable variables — for a
    /// rewrite rule, the free variables of its left side.
    pub fn match_pattern(&self, pattern: Term, term: Term, variables: &[Term]) -> Option<Match> {
        let mut state = Match::default();
        self.match_walk(pattern, term, variables, &mut state)
            .then_some(state)
    }

    /// `term` under this match — in practice the rule's *other* side. Ordinary
    /// term surgery, not inference: the theorem saying the two are equal is
    /// replay's business.
    pub fn instantiate_match(&mut self, m: &Match, term: Term) -> Result<Term> {
        let term = self.inst_type_term(&m.type_subst, term)?;
        if m.term_subst.is_empty() {
            return Ok(term);
        }
        let mut retyped = BTreeMap::new();
        for (v, t) in &m.term_subst {
            let key = self.inst_type_term(&m.type_subst, *v)?;
            retyped.insert(key, *t);
        }
        self.subst(&retyped, term)
    }

    fn match_walk(&self, pattern: Term, term: Term, variables: &[Term], state: &mut Match) -> bool {
        match (self.term_node(pattern), self.term_node(term)) {
            (TermNode::Var { ty, .. }, _) => self.match_var(pattern, *ty, term, variables, state),

            (TermNode::Const { name: pn, ty: pt }, TermNode::Const { name: tn, ty: tt }) => {
                pn == tn && self.unify_type(*pt, *tt, state)
            }

            (TermNode::Bound { index: pi, ty: pt }, TermNode::Bound { index: ti, ty: tt }) => {
                pi == ti && self.unify_type(*pt, *tt, state)
            }

            (
                TermNode::Comb {
                    rator: pr,
                    rand: pd,
                },
                TermNode::Comb {
                    rator: tr,
                    rand: td,
                },
            ) => {
                self.match_walk(*pr, *tr, variables, state)
                    && self.match_walk(*pd, *td, variables, state)
            }

            (
                TermNode::Abs {
                    binder_type: pt,
                    body: pb,
                    ..
                },
                TermNode::Abs {
                    binder_type: tt,
                    body: tb,
                    ..
                },
            ) => self.unify_type(*pt, *tt, state) && self.match_walk(*pb, *tb, variables, state),

            _ => false,
        }
    }

    fn match_var(
        &self,
        pattern: Term,
        pattern_ty: Ty,
        term: Term,
        variables: &[Term],
        state: &mut Match,
    ) -> bool {
        // A variable the rule does not quantify over has to occur literally.
        if !variables.contains(&pattern) {
            return pattern == term;
        }
        // A pattern variable may not swallow a bound occurrence: that index
        // means nothing outside the binder it belongs to.
        if !self.closed(term) {
            return false;
        }
        if !self.unify_type(pattern_ty, self.type_of(term), state) {
            return false;
        }
        match state.term_subst.get(&pattern) {
            Some(&already) => already == term,
            None => {
                state.term_subst.insert(pattern, term);
                true
            }
        }
    }

    fn unify_type(&self, pattern: Ty, target: Ty, state: &mut Match) -> bool {
        match self.ty_match(pattern, target, state.type_subst.clone()) {
            Some(theta) => {
                state.type_subst = theta;
                true
            }
            None => false,
        }
    }
}
