//! Disjunction, defined through implication and universal quantification.
//!
//! This is the continuation encoding from adamas's
//! `lib/adamas/logic/disjunction.rb`: `p ∨ q` accepts both case proofs and
//! returns their common conclusion.

use crate::kernel::{Error, Kernel, Result, Term, TheoryId, Thm, Ty};

use super::implication::ImplicationRules;

/// The definitions and derived rules used by disjunction.
#[derive(Clone)]
pub struct DisjunctionRules {
    /// The definition of `∨`.
    pub definition: Thm,
    /// The definition of `∀`.
    pub universal_definition: Thm,
    /// The rules for implication.
    pub implication_rules: ImplicationRules,
    /// `⊢ T`.
    pub truth: Thm,
    /// `⊢ (p = T) = p`.
    pub true_right: Thm,
}

impl Kernel {
    /// Define `∨` by its universally quantified case eliminator.
    pub fn define_disjunction(&mut self, theory: TheoryId) -> Result<Thm> {
        let ty = self.disjunction_type()?;
        let lhs = self.term_var("∨", ty)?;
        let rhs = self.disjunction_rhs(theory)?;
        let equation = self.term_eq(lhs, rhs)?;
        self.new_basic_definition(theory, equation)
    }

    /// `Γ ⊢ p` gives `Γ ⊢ p ∨ q`.
    pub fn disj1(
        &mut self,
        theory: TheoryId,
        rules: &DisjunctionRules,
        thm: &Thm,
        right: Term,
    ) -> Result<Thm> {
        self.disjunction_intro(theory, rules, thm.concl(), right, thm, true)
    }

    /// `Γ ⊢ q` gives `Γ ⊢ p ∨ q`.
    pub fn disj2(
        &mut self,
        theory: TheoryId,
        rules: &DisjunctionRules,
        left: Term,
        thm: &Thm,
    ) -> Result<Thm> {
        self.disjunction_intro(theory, rules, left, thm.concl(), thm, false)
    }

    /// Eliminate `p ∨ q` with branches for `p` and `q` having one conclusion.
    pub fn disj_cases(
        &mut self,
        theory: TheoryId,
        rules: &DisjunctionRules,
        disjunction: &Thm,
        left_case: &Thm,
        right_case: &Thm,
    ) -> Result<Thm> {
        let Some((left, right)) = self.dest_disj(disjunction.concl()) else {
            return Err(Error::Rule(format!(
                "DISJ_CASES: {} is not a disjunction",
                self.term_to_string(disjunction.concl())
            )));
        };
        if right_case.concl() != left_case.concl() {
            return Err(Error::Rule(format!(
                "DISJ_CASES: {} is not {}",
                self.term_to_string(right_case.concl()),
                self.term_to_string(left_case.concl())
            )));
        }

        let cases = self.disjunction_cases_rule(theory, rules, left, right, left_case.concl())?;
        let left_implication_term = self.mk_imp(theory, left, left_case.concl())?;
        let right_implication_term = self.mk_imp(theory, right, left_case.concl())?;
        let left_assumed = self.assume(theory, left_implication_term)?;
        let right_assumed = self.assume(theory, right_implication_term)?;
        let left_applied = self.mp(theory, &rules.implication_rules, &cases, &left_assumed)?;
        let base = self.mp(
            theory,
            &rules.implication_rules,
            &left_applied,
            &right_assumed,
        )?;

        let left_imp = self.disch(theory, &rules.implication_rules, left, left_case)?;
        let right_imp = self.disch(theory, &rules.implication_rules, right, right_case)?;
        let without_left = self.prove_hyp(theory, &left_imp, &base)?;
        let without_right = self.prove_hyp(theory, &right_imp, &without_left)?;
        self.prove_hyp(theory, disjunction, &without_right)
    }

    fn disjunction_type(&mut self) -> Result<Ty> {
        let bool_ty = self.bool_ty();
        let inner = self.ty_fun(bool_ty, bool_ty)?;
        self.ty_fun(bool_ty, inner)
    }

    fn disjunction_rhs(&mut self, theory: TheoryId) -> Result<Term> {
        let bool_ty = self.bool_ty();
        let left = self.term_var("p", bool_ty)?;
        let right = self.term_var("q", bool_ty)?;
        let body = self.disjunction_body(theory, left, right)?;
        let inner = self.term_abs(right, body)?;
        self.term_abs(left, inner)
    }

    fn disjunction_body(&mut self, theory: TheoryId, left: Term, right: Term) -> Result<Term> {
        let conclusion = self.term_var("r", self.bool_ty())?;
        let left_case = self.mk_imp(theory, left, conclusion)?;
        let right_case = self.mk_imp(theory, right, conclusion)?;
        let inner = self.mk_imp(theory, right_case, conclusion)?;
        let cases = self.mk_imp(theory, left_case, inner)?;
        self.mk_forall(theory, conclusion, cases)
    }

    fn disjunction_intro(
        &mut self,
        theory: TheoryId,
        rules: &DisjunctionRules,
        left: Term,
        right: Term,
        proof: &Thm,
        use_left: bool,
    ) -> Result<Thm> {
        let conclusion = self.disjunction_conclusion_variable(left, right, proof.hyps())?;
        let left_case = self.mk_imp(theory, left, conclusion)?;
        let right_case = self.mk_imp(theory, right, conclusion)?;
        let assumed_left = self.assume(theory, left_case)?;
        let assumed_right = self.assume(theory, right_case)?;
        let consequent = if use_left {
            self.mp(theory, &rules.implication_rules, &assumed_left, proof)?
        } else {
            self.mp(theory, &rules.implication_rules, &assumed_right, proof)?
        };
        let inner = self.disch(theory, &rules.implication_rules, right_case, &consequent)?;
        let outer = self.disch(theory, &rules.implication_rules, left_case, &inner)?;
        let quantified = self.gen(
            theory,
            &rules.universal_definition,
            &rules.true_right,
            conclusion,
            &outer,
        )?;

        let unfolded = self.disjunction_unfolded(theory, &rules.definition, left, right)?;
        let backwards = self.sym(theory, &unfolded)?;
        self.eq_mp(theory, &backwards, &quantified)
    }

    fn disjunction_cases_rule(
        &mut self,
        theory: TheoryId,
        rules: &DisjunctionRules,
        left: Term,
        right: Term,
        goal: Term,
    ) -> Result<Thm> {
        let disjunction_term = self.mk_disj(theory, left, right)?;
        let assumed = self.assume(theory, disjunction_term)?;
        let unfolded = self.disjunction_unfolded(theory, &rules.definition, left, right)?;
        let expanded = self.eq_mp(theory, &unfolded, &assumed)?;
        self.spec(
            theory,
            &rules.universal_definition,
            &rules.truth,
            &expanded,
            goal,
        )
    }

    fn disjunction_unfolded(
        &mut self,
        theory: TheoryId,
        definition: &Thm,
        left: Term,
        right: Term,
    ) -> Result<Thm> {
        let applied_left = self.ap_thm(theory, definition, left)?;
        let applied_left = self.normalise(theory, applied_left)?;
        let applied_right = self.ap_thm(theory, &applied_left, right)?;
        self.normalise(theory, applied_right)
    }

    fn disjunction_conclusion_variable(
        &mut self,
        left: Term,
        right: Term,
        hyps: &[Term],
    ) -> Result<Term> {
        let mut avoid = self.frees(left).to_vec();
        avoid.extend_from_slice(self.frees(right));
        for hyp in hyps {
            avoid.extend_from_slice(self.frees(*hyp));
        }
        self.variant(&avoid, "r", self.bool_ty())
    }
}
