//! Implication, defined over conjunction.
//!
//! Ported from adamas's `lib/adamas/logic/implication.rb`. `p ⇒ q` says that
//! `p ∧ q` is `p` — so modus ponens is a projection, and discharging an
//! assumption is `DEDUCT_ANTISYM_RULE` between the two halves of that equation.

use crate::kernel::{Error, Kernel, Result, Term, TheoryId, Thm, Ty};

/// The theorems `⇒`'s rules reach for. Ruby carries these in a `Data` bundle;
/// here they are a struct so the signatures stay short.
#[derive(Clone)]
pub struct ImplicationRules {
    /// `⊢ ⇒ = (λp q. p ∧ q = p)`.
    pub definition: Thm,
    /// `⊢ ∧ = (λp q. (λf. f p q) = (λf. f T T))`.
    pub conjunction_definition: Thm,
    /// `⊢ T`.
    pub truth: Thm,
    /// `⊢ (p = T) = p`.
    pub true_right: Thm,
}

impl Kernel {
    /// `⊢ ⇒ = (λp q. p ∧ q = p)`.
    pub fn define_implication(&mut self, theory: TheoryId) -> Result<Thm> {
        let ty = self.implication_type()?;
        let lhs = self.term_var("⇒", ty)?;
        let rhs = self.implication_rhs(theory)?;
        let equation = self.term_eq(lhs, rhs)?;
        self.new_basic_definition(theory, equation)
    }

    /// `Γ ⊢ p ⇒ q` and `Δ ⊢ p` give `Γ ∪ Δ ⊢ q`.
    pub fn mp(
        &mut self,
        theory: TheoryId,
        rules: &ImplicationRules,
        implication: &Thm,
        antecedent: &Thm,
    ) -> Result<Thm> {
        let Some((left, right)) = self.dest_imp(implication.concl()) else {
            return Err(Error::Rule(format!(
                "MP: {} is not an implication",
                self.term_to_string(implication.concl())
            )));
        };
        if antecedent.concl() != left {
            return Err(Error::Rule(format!(
                "MP: {} is not {}",
                self.term_to_string(antecedent.concl()),
                self.term_to_string(left)
            )));
        }
        let unfolded = self.implication_unfolded(theory, &rules.definition, left, right)?;
        let equality = self.eq_mp(theory, &unfolded, implication)?;
        let backwards = self.sym(theory, &equality)?;
        let conjunction = self.eq_mp(theory, &backwards, antecedent)?;
        self.conjunct2(
            theory,
            &rules.conjunction_definition,
            &rules.truth,
            &conjunction,
        )
    }

    /// `Γ ⊢ q` gives `Γ - p ⊢ p ⇒ q`.
    pub fn disch(
        &mut self,
        theory: TheoryId,
        rules: &ImplicationRules,
        antecedent: Term,
        thm: &Thm,
    ) -> Result<Thm> {
        let implication = self.mk_imp(theory, antecedent, thm.concl())?;
        let equality = self.implication_equality(theory, rules, antecedent, thm)?;
        let unfolded =
            self.implication_unfolded(theory, &rules.definition, antecedent, thm.concl())?;
        let backwards = self.sym(theory, &unfolded)?;
        let proved = self.eq_mp(theory, &backwards, &equality)?;
        if proved.concl() != implication {
            return Err(Error::Rule(format!(
                "DISCH: failed to prove {}",
                self.term_to_string(implication)
            )));
        }
        Ok(proved)
    }

    /// `Γ ⊢ p ⇒ q` gives `Γ ∪ {p} ⊢ q`.
    pub fn undisch(
        &mut self,
        theory: TheoryId,
        rules: &ImplicationRules,
        thm: &Thm,
    ) -> Result<Thm> {
        let Some((left, _)) = self.dest_imp(thm.concl()) else {
            return Err(Error::Rule(format!(
                "UNDISCH: {} is not an implication",
                self.term_to_string(thm.concl())
            )));
        };
        let assumed = self.assume(theory, left)?;
        self.mp(theory, rules, thm, &assumed)
    }

    /// Discharge every hypothesis, the last-listed one innermost.
    pub fn disch_all(
        &mut self,
        theory: TheoryId,
        rules: &ImplicationRules,
        thm: &Thm,
    ) -> Result<Thm> {
        let mut discharged = thm.clone();
        for hyp in thm.hyps().to_vec().into_iter().rev() {
            discharged = self.disch(theory, rules, hyp, &discharged)?;
        }
        Ok(discharged)
    }

    /// `Γ ⊢ p = q` gives `Γ ⊢ p ⇒ q` and `Γ ⊢ q ⇒ p`.
    pub fn eq_imp_rule(
        &mut self,
        theory: TheoryId,
        rules: &ImplicationRules,
        thm: &Thm,
    ) -> Result<(Thm, Thm)> {
        let Some((left, right)) = self.dest_eq(thm.concl()) else {
            return Err(Error::Rule(format!(
                "EQ_IMP_RULE: {} is not an equation",
                self.term_to_string(thm.concl())
            )));
        };
        let forwards = self.disch_equality(theory, rules, thm, left)?;
        let symmetric = self.sym(theory, thm)?;
        let backwards = self.disch_equality(theory, rules, &symmetric, right)?;
        Ok((forwards, backwards))
    }

    /// `Γ ⊢ p ⇒ q` and `Δ ⊢ q ⇒ p` give `Γ ∪ Δ ⊢ p = q`.
    pub fn imp_antisym_rule(
        &mut self,
        theory: TheoryId,
        rules: &ImplicationRules,
        left: &Thm,
        right: &Thm,
    ) -> Result<Thm> {
        let from_right = self.undisch(theory, rules, right)?;
        let from_left = self.undisch(theory, rules, left)?;
        self.deduct_antisym_rule(theory, &from_right, &from_left)
    }

    /// `Γ ⊢ p ⇒ q` and `Δ ⊢ q ⇒ r` give `Γ ∪ Δ ⊢ p ⇒ r`.
    pub fn imp_trans(
        &mut self,
        theory: TheoryId,
        rules: &ImplicationRules,
        left: &Thm,
        right: &Thm,
    ) -> Result<Thm> {
        let Some((antecedent, _)) = self.dest_imp(left.concl()) else {
            return Err(Error::Rule(format!(
                "IMP_TRANS: {} is not an implication",
                self.term_to_string(left.concl())
            )));
        };
        let middle = self.undisch(theory, rules, left)?;
        let conclusion = self.mp(theory, rules, right, &middle)?;
        self.disch(theory, rules, antecedent, &conclusion)
    }

    // --- the encoding ------------------------------------------------------

    fn implication_type(&mut self) -> Result<Ty> {
        let bool_ty = self.bool_ty();
        let inner = self.ty_fun(bool_ty, bool_ty)?;
        self.ty_fun(bool_ty, inner)
    }

    fn implication_rhs(&mut self, theory: TheoryId) -> Result<Term> {
        let bool_ty = self.bool_ty();
        let p = self.term_var("p", bool_ty)?;
        let q = self.term_var("q", bool_ty)?;
        let conjunction = self.mk_conj(theory, p, q)?;
        let body = self.term_eq(conjunction, p)?;
        let inner = self.term_abs(q, body)?;
        self.term_abs(p, inner)
    }

    /// `⊢ (p ⇒ q) = (p ∧ q = p)`, the definition applied to both sides and
    /// beta-reduced.
    fn implication_unfolded(
        &mut self,
        theory: TheoryId,
        definition: &Thm,
        left: Term,
        right: Term,
    ) -> Result<Thm> {
        let half = self.ap_thm(theory, definition, left)?;
        let half = self.normalise(theory, half)?;
        let whole = self.ap_thm(theory, &half, right)?;
        self.normalise(theory, whole)
    }

    /// `⊢ (p ∧ q) = p`, each direction discharging the other's assumption.
    fn implication_equality(
        &mut self,
        theory: TheoryId,
        rules: &ImplicationRules,
        antecedent: Term,
        consequent: &Thm,
    ) -> Result<Thm> {
        let conjunction = self.mk_conj(theory, antecedent, consequent.concl())?;
        let assumed_conjunction = self.assume(theory, conjunction)?;
        let forwards = self.conjunct1(
            theory,
            &rules.conjunction_definition,
            &rules.truth,
            &assumed_conjunction,
        )?;
        let assumed_antecedent = self.assume(theory, antecedent)?;
        let backwards = self.conj(
            theory,
            &rules.conjunction_definition,
            &rules.true_right,
            &assumed_antecedent,
            consequent,
        )?;
        self.deduct_antisym_rule(theory, &backwards, &forwards)
    }

    /// `Γ ⊢ p = q` and an antecedent give `Γ ⊢ antecedent ⇒ ...`.
    fn disch_equality(
        &mut self,
        theory: TheoryId,
        rules: &ImplicationRules,
        thm: &Thm,
        antecedent: Term,
    ) -> Result<Thm> {
        let assumed = self.assume(theory, antecedent)?;
        let consequent = self.eq_mp(theory, thm, &assumed)?;
        self.disch(theory, rules, antecedent, &consequent)
    }
}
