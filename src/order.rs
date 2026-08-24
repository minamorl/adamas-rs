//! A total order on terms, and the rewriting that only ever goes down it.
//! Ported from `lib/adamas/conversion/ordered.rb`.
//!
//! A permutative rule — `m * n = n * m` — cannot be used as a rewrite rule:
//! every application matches its own output, so the rewriter swaps forever.
//! HOL Light's answer (`simp.ml`, `ORDERED_REWR_CONV` and `term_order`) is to
//! apply such a rule only when the result is *smaller* than what it replaced.
//! Commutativity then stops being a loop and becomes a sorting pass.
//!
//! # Nothing here may be process-global
//!
//! The order is HOL Light's dynamic lexicographic one, and its fallback has to
//! be a function of the term's own structure. In this port that warning has
//! teeth the Ruby original did not have to worry about: [`Term`] is a newtype
//! over its rank in the intern table, so it *derives* `Ord` — and that derived
//! order is an insertion counter. Using it here would make the same two terms
//! compare differently in two processes, and a certificate written by one
//! rewriter would stop replaying in another.
//!
//! So the comparison below never touches `Term`'s own ordering, never renders a
//! term to a string (binder display names are donated by whichever
//! alpha-variant was interned first), and reads only node class, canonical
//! name, de Bruijn index, type structure and subterms.

use std::cmp::Ordering;

use crate::kernel::{Kernel, Term, TermNode, Ty, TyNode};

/// Var < Const < Comb < Abs < Bound. Any fixed order will do; this one follows
/// the constructor order of HOL Light's own `term` type, with the de Bruijn
/// index — which HOL Light does not have — put last.
fn class_of(node: &TermNode) -> u8 {
    match node {
        TermNode::Var { .. } => 0,
        TermNode::Const { .. } => 1,
        TermNode::Comb { .. } => 2,
        TermNode::Abs { .. } => 3,
        TermNode::Bound { .. } => 4,
    }
}

impl Kernel {
    /// `true` when `left` is strictly greater than `right`.
    ///
    /// The recursion starts with no head at all: HOL Light passes `T` as a
    /// value no real head is expected to be, and `None` says the same thing
    /// without pinning the meaning of the order to some particular constant of
    /// some theory.
    pub fn term_greater(&self, left: Term, right: Term) -> bool {
        self.dyn_greater(None, left, right)
    }

    fn dyn_greater(&self, top: Option<Term>, left: Term, right: Term) -> bool {
        let (head1, args1) = self.strip_comb(left);
        let (head2, args2) = self.strip_comb(right);
        if head1 == head2 {
            return self.lexify(Some(head1), &args1, &args2);
        }
        if Some(head2) == top {
            return false;
        }
        if Some(head1) == top {
            return true;
        }
        self.compare_terms(head1, head2) == Ordering::Greater
    }

    /// Equal heads compare their arguments lexically, with that head itself
    /// counting as the largest thing there is, so a nested `+` outweighs any of
    /// its neighbours.
    fn lexify(&self, top: Option<Term>, left: &[Term], right: &[Term]) -> bool {
        if left.is_empty() {
            return false;
        }
        if right.is_empty() {
            return true;
        }
        if self.dyn_greater(top, left[0], right[0]) {
            return true;
        }
        left[0] == right[0] && self.lexify(top, &left[1..], &right[1..])
    }

    /// `f x y` as `(f, [x, y])`.
    fn strip_comb(&self, term: Term) -> (Term, Vec<Term>) {
        let mut args = Vec::new();
        let mut term = term;
        while let TermNode::Comb { rator, rand } = self.term_node(term) {
            args.push(*rand);
            term = *rator;
        }
        args.reverse();
        (term, args)
    }

    /// `Equal` only for identical terms. Reads structure only — never
    /// `Term`'s derived ordering, which is an intern-table insertion counter.
    fn compare_terms(&self, left: Term, right: Term) -> Ordering {
        if left == right {
            return Ordering::Equal;
        }
        let ln = self.term_node(left);
        let rn = self.term_node(right);
        match class_of(ln).cmp(&class_of(rn)) {
            Ordering::Equal => self.compare_alike(ln, rn),
            other => other,
        }
    }

    fn compare_alike(&self, left: &TermNode, right: &TermNode) -> Ordering {
        match (left, right) {
            (TermNode::Var { name: ln, ty: lt }, TermNode::Var { name: rn, ty: rt })
            | (TermNode::Const { name: ln, ty: lt }, TermNode::Const { name: rn, ty: rt }) => {
                ln.cmp(rn).then_with(|| self.compare_types(*lt, *rt))
            }
            (TermNode::Bound { index: li, ty: lt }, TermNode::Bound { index: ri, ty: rt }) => {
                li.cmp(ri).then_with(|| self.compare_types(*lt, *rt))
            }
            (
                TermNode::Comb {
                    rator: lr,
                    rand: ld,
                },
                TermNode::Comb {
                    rator: rr,
                    rand: rd,
                },
            ) => self
                .compare_terms(*lr, *rr)
                .then_with(|| self.compare_terms(*ld, *rd)),
            (
                TermNode::Abs {
                    binder_type: lt,
                    body: lb,
                    ..
                },
                TermNode::Abs {
                    binder_type: rt,
                    body: rb,
                    ..
                },
            ) => self
                .compare_types(*lt, *rt)
                .then_with(|| self.compare_terms(*lb, *rb)),
            _ => Ordering::Equal,
        }
    }

    /// Type variables before type constructors, then by name, then argument by
    /// argument — the same shape, one level down.
    fn compare_types(&self, left: Ty, right: Ty) -> Ordering {
        if left == right {
            return Ordering::Equal;
        }
        match (self.ty_node(left), self.ty_node(right)) {
            (TyNode::Var { name: ln }, TyNode::Var { name: rn }) => ln.cmp(rn),
            (TyNode::Var { .. }, TyNode::Con { .. }) => Ordering::Less,
            (TyNode::Con { .. }, TyNode::Var { .. }) => Ordering::Greater,
            (TyNode::Con { name: ln, args: la }, TyNode::Con { name: rn, args: ra }) => {
                ln.cmp(rn).then_with(|| {
                    for (l, r) in la.iter().zip(ra.iter()) {
                        match self.compare_types(*l, *r) {
                            Ordering::Equal => continue,
                            other => return other,
                        }
                    }
                    la.len().cmp(&ra.len())
                })
            }
        }
    }
}
