//! The syntax of the connectives: how `∧`, `⇒`, `∨`, `¬`, `∀` and `∃` are
//! spelled as terms, and how to take them apart again.
//!
//! Ported from the constructor and destructor half of adamas's
//! `lib/adamas/logic.rb`. Nothing here proves anything — these functions only
//! assemble terms around constants the theory has already declared. The
//! theorems about them live in the sibling modules.

mod conjunction;
mod universal;

use crate::kernel::{Kernel, Result, Term, TheoryId};

impl Kernel {
    /// `∀x. body`, as the term `∀ (λx. body)`.
    pub fn mk_forall(&mut self, theory: TheoryId, var: Term, body: Term) -> Result<Term> {
        todo!("port Logic.mk_forall")
    }

    /// `∃x. body`, as the term `∃ (λx. body)`.
    pub fn mk_exists(&mut self, theory: TheoryId, var: Term, body: Term) -> Result<Term> {
        todo!("port Logic.mk_exists")
    }

    /// `left ∧ right`.
    pub fn mk_conj(&mut self, theory: TheoryId, left: Term, right: Term) -> Result<Term> {
        todo!("port Logic.mk_conj")
    }

    /// `left ⇒ right`.
    pub fn mk_imp(&mut self, theory: TheoryId, left: Term, right: Term) -> Result<Term> {
        todo!("port Logic.mk_imp")
    }

    /// `left ∨ right`.
    pub fn mk_disj(&mut self, theory: TheoryId, left: Term, right: Term) -> Result<Term> {
        todo!("port Logic.mk_disj")
    }

    /// `¬term`.
    pub fn mk_neg(&mut self, theory: TheoryId, term: Term) -> Result<Term> {
        todo!("port Logic.mk_neg")
    }

    /// The proposition `p ∨ ¬p` as a term, not a theorem.
    pub fn excluded_middle(&mut self, theory: TheoryId, proposition: Term) -> Result<Term> {
        todo!("port Logic.excluded_middle")
    }

    /// The binder's variable and the opened body of `∀x. body`.
    pub fn dest_forall(&mut self, term: Term) -> Option<(Term, Term)> {
        todo!("port Logic.dest_forall")
    }

    /// The binder's variable and the opened body of `∃x. body`.
    pub fn dest_exists(&mut self, term: Term) -> Option<(Term, Term)> {
        todo!("port Logic.dest_exists")
    }

    /// The two sides of `left ∧ right`.
    pub fn dest_conj(&self, term: Term) -> Option<(Term, Term)> {
        todo!("port Logic.dest_conj")
    }

    /// The two sides of `left ⇒ right`.
    pub fn dest_imp(&self, term: Term) -> Option<(Term, Term)> {
        todo!("port Logic.dest_imp")
    }

    /// The two sides of `left ∨ right`.
    pub fn dest_disj(&self, term: Term) -> Option<(Term, Term)> {
        todo!("port Logic.dest_disj")
    }

    /// The body of `¬p`.
    pub fn dest_neg(&self, term: Term) -> Option<Term> {
        todo!("port Logic.dest_neg")
    }
}
