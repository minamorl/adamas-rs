//! The syntax of the connectives: how `∧`, `⇒`, `∨`, `¬`, `∀` and `∃` are
//! spelled as terms, and how to take them apart again.
//!
//! Ported from the constructor and destructor half of adamas's
//! `lib/adamas/logic.rb`. Nothing here proves anything — these functions only
//! assemble terms around constants the theory has already declared. The
//! theorems about them live in the sibling modules.

pub mod classical;
mod conjunction;
pub mod disjunction;
pub mod existential;
pub mod falsity;
pub mod implication;
pub mod negation;
mod universal;

use crate::booleans::Booleans;
use crate::kernel::{Kernel, Result, Term, TermNode, TheoryId, Thm};

use self::disjunction::DisjunctionRules;
use self::existential::ExistentialRules;
use self::falsity::FalsityRules;
use self::implication::ImplicationRules;
use self::negation::NegationRules;

/// The constructive definitions and rule handles installed by
/// [`Kernel::install_logic`].
///
/// This is Ruby adamas's `Logic::Bootstrap`, minus the `Simp` fields that do
/// not exist in this crate yet. Installing it declares only definitions and
/// leaves the theory's axiom ledger empty.
#[derive(Clone)]
pub struct LogicBootstrap {
    pub booleans: Booleans,
    pub truth: Thm,
    pub true_const: Term,
    pub falsity_const: Term,
    pub conjunction_const: Term,
    pub universal_const: Term,
    pub implication_const: Term,
    pub disjunction_const: Term,
    pub existential_const: Term,
    pub negation_const: Term,
    pub truth_definition: Thm,
    pub conjunction_definition: Thm,
    pub universal_definition: Thm,
    pub implication_definition: Thm,
    pub falsity_definition: Thm,
    pub disjunction_definition: Thm,
    pub existential_definition: Thm,
    pub negation_definition: Thm,
    pub implication_rules: ImplicationRules,
    pub falsity_rules: FalsityRules,
    pub disjunction_rules: DisjunctionRules,
    pub existential_rules: ExistentialRules,
    pub negation_rules: NegationRules,
}

impl Kernel {
    /// Install the complete constructive logic layer in Ruby's definition
    /// order. No axiom is asserted; classical logic remains a separate opt-in.
    pub fn install_logic(&mut self, theory: TheoryId) -> Result<LogicBootstrap> {
        let booleans = self.install_booleans(theory)?;
        let conjunction_definition = self.define_conjunction(theory, &booleans.truth)?;
        let universal_definition = self.define_universal(theory, &booleans.truth)?;
        let implication_definition = self.define_implication(theory)?;
        let falsity_definition = self.define_falsity(theory)?;
        let disjunction_definition = self.define_disjunction(theory)?;
        let existential_definition = self.define_existential(theory)?;
        let negation_definition = self.define_negation(theory)?;

        let implication_rules = ImplicationRules {
            definition: implication_definition.clone(),
            conjunction_definition: conjunction_definition.clone(),
            truth: booleans.truth.clone(),
            true_right: booleans.true_right.clone(),
        };
        let falsity_rules = FalsityRules {
            definition: falsity_definition.clone(),
            universal_definition: universal_definition.clone(),
            truth: booleans.truth.clone(),
        };
        let disjunction_rules = DisjunctionRules {
            definition: disjunction_definition.clone(),
            universal_definition: universal_definition.clone(),
            implication_rules: implication_rules.clone(),
            truth: booleans.truth.clone(),
            true_right: booleans.true_right.clone(),
        };
        let existential_rules = ExistentialRules {
            definition: existential_definition.clone(),
            universal_definition: universal_definition.clone(),
            implication_rules: implication_rules.clone(),
            truth: booleans.truth.clone(),
            true_right: booleans.true_right.clone(),
        };
        let negation_rules = NegationRules {
            definition: negation_definition.clone(),
            implication_rules: implication_rules.clone(),
            falsity_rules: falsity_rules.clone(),
        };

        Ok(LogicBootstrap {
            truth: booleans.truth.clone(),
            true_const: booleans.true_const,
            falsity_const: self.constant(theory, "F", None)?,
            conjunction_const: self.constant(theory, "∧", None)?,
            universal_const: self.constant(theory, "∀", None)?,
            implication_const: self.constant(theory, "⇒", None)?,
            disjunction_const: self.constant(theory, "∨", None)?,
            existential_const: self.constant(theory, "∃", None)?,
            negation_const: self.constant(theory, "¬", None)?,
            truth_definition: booleans.definition.clone(),
            conjunction_definition,
            universal_definition,
            implication_definition,
            falsity_definition,
            disjunction_definition,
            existential_definition,
            negation_definition,
            implication_rules,
            falsity_rules,
            disjunction_rules,
            existential_rules,
            negation_rules,
            booleans,
        })
    }

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
