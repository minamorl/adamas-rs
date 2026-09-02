//! The syntax of the connectives: how `∧`, `⇒`, `∨`, `¬`, `∀` and `∃` are
//! spelled as terms, and how to take them apart again.
//!
//! Ported from the constructor and destructor half of adamas's
//! `lib/adamas/logic.rb`. Nothing here proves anything — these functions only
//! assemble terms around constants the theory has already declared. The
//! theorems about them live in the sibling modules.

mod conjunction;
pub mod disjunction;
pub mod existential;
pub mod falsity;
pub mod implication;
pub mod negation;
mod universal;

use crate::kernel::{Kernel, Result, Term, TermNode, TheoryId};

impl Kernel {
    /// `∀x. body`, as the term `∀ (λx. body)`.
    pub fn mk_forall(&mut self, theory: TheoryId, var: Term, body: Term) -> Result<Term> {
        self.mk_quantified(theory, "∀", var, body)
    }

    /// `∃x. body`, as the term `∃ (λx. body)`.
    pub fn mk_exists(&mut self, theory: TheoryId, var: Term, body: Term) -> Result<Term> {
        self.mk_quantified(theory, "∃", var, body)
    }

    /// `left ∧ right`.
    pub fn mk_conj(&mut self, theory: TheoryId, left: Term, right: Term) -> Result<Term> {
        self.mk_binary(theory, "∧", left, right)
    }

    /// `left ⇒ right`.
    pub fn mk_imp(&mut self, theory: TheoryId, left: Term, right: Term) -> Result<Term> {
        self.mk_binary(theory, "⇒", left, right)
    }

    /// `left ∨ right`.
    pub fn mk_disj(&mut self, theory: TheoryId, left: Term, right: Term) -> Result<Term> {
        self.mk_binary(theory, "∨", left, right)
    }

    /// `¬term`.
    pub fn mk_neg(&mut self, theory: TheoryId, term: Term) -> Result<Term> {
        let ty = self.ty_fun(self.bool_ty(), self.bool_ty())?;
        let c = self.constant(theory, "¬", Some(ty))?;
        self.term_comb(c, term)
    }

    /// The proposition `p ∨ ¬p` as a term, not a theorem.
    pub fn excluded_middle(&mut self, theory: TheoryId, proposition: Term) -> Result<Term> {
        let neg = self.mk_neg(theory, proposition)?;
        self.mk_disj(theory, proposition, neg)
    }

    /// The binder's variable and the opened body of `∀x. body`.
    pub fn dest_forall(&mut self, term: Term) -> Option<(Term, Term)> {
        self.dest_quantified(term, "∀")
    }

    /// The binder's variable and the opened body of `∃x. body`.
    pub fn dest_exists(&mut self, term: Term) -> Option<(Term, Term)> {
        self.dest_quantified(term, "∃")
    }

    /// The two sides of `left ∧ right`.
    pub fn dest_conj(&self, term: Term) -> Option<(Term, Term)> {
        self.dest_binary(term, "∧")
    }

    /// The two sides of `left ⇒ right`.
    pub fn dest_imp(&self, term: Term) -> Option<(Term, Term)> {
        self.dest_binary(term, "⇒")
    }

    /// The two sides of `left ∨ right`.
    pub fn dest_disj(&self, term: Term) -> Option<(Term, Term)> {
        self.dest_binary(term, "∨")
    }

    /// The body of `¬p`.
    pub fn dest_neg(&self, term: Term) -> Option<Term> {
        let TermNode::Comb { rator, rand: body } = *self.term_node(term) else {
            return None;
        };
        let TermNode::Const { name, .. } = self.term_node(rator) else {
            return None;
        };
        if name == "¬" {
            Some(body)
        } else {
            None
        }
    }

    // ------------------------------------------------------------------
    // private helpers (binary)
    // ------------------------------------------------------------------

    fn mk_binary(&mut self, theory: TheoryId, name: &str, left: Term, right: Term) -> Result<Term> {
        let bool_ty = self.bool_ty();
        let inner = self.ty_fun(bool_ty, bool_ty)?;
        let ty = self.ty_fun(bool_ty, inner)?;
        let c = self.constant(theory, name, Some(ty))?;
        let half = self.term_comb(c, left)?;
        self.term_comb(half, right)
    }

    fn dest_binary(&self, term: Term, name: &str) -> Option<(Term, Term)> {
        let TermNode::Comb { rator, rand: right } = *self.term_node(term) else {
            return None;
        };
        let TermNode::Comb {
            rator: head,
            rand: left,
        } = *self.term_node(rator)
        else {
            return None;
        };
        match self.term_node(head) {
            TermNode::Const { name: found, .. } if found == name => Some((left, right)),
            _ => None,
        }
    }

    // ------------------------------------------------------------------
    // private helpers (quantified)
    // ------------------------------------------------------------------

    fn mk_quantified(
        &mut self,
        theory: TheoryId,
        name: &str,
        var: Term,
        body: Term,
    ) -> Result<Term> {
        let bool_ty = self.bool_ty();
        let var_ty = self.type_of(var);
        let inner = self.ty_fun(var_ty, bool_ty)?;
        let ty = self.ty_fun(inner, bool_ty)?;
        let c = self.constant(theory, name, Some(ty))?;
        let abs = self.term_abs(var, body)?;
        self.term_comb(c, abs)
    }

    fn dest_quantified(&mut self, term: Term, name: &str) -> Option<(Term, Term)> {
        let TermNode::Comb { rator, rand } = *self.term_node(term) else {
            return None;
        };
        let TermNode::Const { name: found, .. } = self.term_node(rator) else {
            return None;
        };
        if found != name {
            return None;
        }
        let TermNode::Abs { .. } = *self.term_node(rand) else {
            return None;
        };
        self.dest_abs(rand).ok()
    }
}
