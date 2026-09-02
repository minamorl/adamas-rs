//! Negation, defined through implication and falsity.
//!
//! Ported directly from adamas's `lib/adamas/logic/negation.rb`. Folding,
//! unfolding, and the equality-with-falsity rules use only already-derived
//! rules and the ten kernel primitives.

use crate::kernel::{Error, Kernel, Result, Term, TheoryId, Thm, Ty};

use super::falsity::FalsityRules;
use super::implication::ImplicationRules;

/// The theorems used by negation's derived rules.
#[derive(Clone)]
pub struct NegationRules {
    /// `⊢ ¬ = (λp. p ⇒ F)`.
    pub definition: Thm,
    /// The derived rules for implication.
    pub implication_rules: ImplicationRules,
    /// The derived rules for falsity.
    pub falsity_rules: FalsityRules,
}

impl Kernel {
    /// Define `¬` as `λp. p ⇒ F` using `new_basic_definition`.
    pub fn define_negation(&mut self, theory: TheoryId) -> Result<Thm> {
        let ty = self.negation_type()?;
        let lhs = self.term_var("¬", ty)?;
        let rhs = self.negation_rhs(theory)?;
        let equation = self.term_eq(lhs, rhs)?;
        self.new_basic_definition(theory, equation)
    }

    /// `Γ ⊢ ¬p` gives `Γ ⊢ p ⇒ F`.
    pub fn not_elim(&mut self, theory: TheoryId, rules: &NegationRules, thm: &Thm) -> Result<Thm> {
        let proposition = self.dest_neg(thm.concl()).ok_or_else(|| {
            Error::Rule(format!(
                "NOT_ELIM: {} is not a negation",
                self.term_to_string(thm.concl())
            ))
        })?;
        let unfolded = self.negation_unfolded(theory, &rules.definition, proposition)?;
        self.eq_mp(theory, &unfolded, thm)
    }

    /// `Γ ⊢ p ⇒ F` gives `Γ ⊢ ¬p`.
    pub fn not_intro(&mut self, theory: TheoryId, rules: &NegationRules, thm: &Thm) -> Result<Thm> {
        let Some((proposition, consequent)) = self.dest_imp(thm.concl()) else {
            return Err(Error::Rule(format!(
                "NOT_INTRO: {} is not an implication",
                self.term_to_string(thm.concl())
            )));
        };
        let falsity = self.constant(theory, "F", None)?;
        if consequent != falsity {
            return Err(Error::Rule(format!(
                "NOT_INTRO: {} is not {}",
                self.term_to_string(consequent),
                self.term_to_string(falsity)
            )));
        }

        let unfolded = self.negation_unfolded(theory, &rules.definition, proposition)?;
        let backwards = self.sym(theory, &unfolded)?;
        self.eq_mp(theory, &backwards, thm)
    }

    /// `Γ ⊢ ¬p` gives `Γ ⊢ p = F`.
    pub fn eqf_intro(&mut self, theory: TheoryId, rules: &NegationRules, thm: &Thm) -> Result<Thm> {
        let proposition = self.dest_neg(thm.concl()).ok_or_else(|| {
            Error::Rule(format!(
                "EQF_INTRO: {} is not a negation",
                self.term_to_string(thm.concl())
            ))
        })?;
        let implication = self.not_elim(theory, rules, thm)?;
        let falsity = self.undisch(theory, &rules.implication_rules, &implication)?;
        let false_const = self.constant(theory, "F", None)?;
        let assumed_false = self.assume(theory, false_const)?;
        let from_falsity = self.contr(theory, &rules.falsity_rules, &assumed_false, proposition)?;
        self.deduct_antisym_rule(theory, &from_falsity, &falsity)
    }

    /// `Γ ⊢ p = F` gives `Γ ⊢ ¬p`.
    pub fn eqf_elim(&mut self, theory: TheoryId, rules: &NegationRules, thm: &Thm) -> Result<Thm> {
        let Some((proposition, right)) = self.dest_eq(thm.concl()) else {
            return Err(Error::Rule(format!(
                "EQF_ELIM: {} is not an equation",
                self.term_to_string(thm.concl())
            )));
        };
        let falsity = self.constant(theory, "F", None)?;
        if right != falsity {
            return Err(Error::Rule(format!(
                "EQF_ELIM: {} is not {}",
                self.term_to_string(right),
                self.term_to_string(falsity)
            )));
        }

        let assumed = self.assume(theory, proposition)?;
        let false_thm = self.eq_mp(theory, thm, &assumed)?;
        let implication = self.disch(theory, &rules.implication_rules, proposition, &false_thm)?;
        self.not_intro(theory, rules, &implication)
    }

    fn negation_type(&mut self) -> Result<Ty> {
        let bool_ty = self.bool_ty();
        self.ty_fun(bool_ty, bool_ty)
    }

    fn negation_rhs(&mut self, theory: TheoryId) -> Result<Term> {
        let bool_ty = self.bool_ty();
        let proposition = self.term_var("p", bool_ty)?;
        let falsity = self.constant(theory, "F", None)?;
        let implication = self.mk_imp(theory, proposition, falsity)?;
        self.term_abs(proposition, implication)
    }

    fn negation_unfolded(
        &mut self,
        theory: TheoryId,
        definition: &Thm,
        proposition: Term,
    ) -> Result<Thm> {
        let applied = self.ap_thm(theory, definition, proposition)?;
        self.beta_rule(theory, &applied)
    }
}
