//! Existential quantification, defined through implication and `∀`.
//!
//! Ported directly from adamas's `lib/adamas/logic/existential.rb`. `EXISTS`
//! builds the continuation encoding for a witness, while `CHOOSE` relies on
//! the kernel's `ABS` side condition for its eigenvariable refusals.

use std::collections::BTreeMap;

use crate::kernel::{Error, Kernel, Result, Term, TheoryId, Thm, Ty};

use super::implication::ImplicationRules;

/// The definitions and rules used by existential introduction and elimination.
#[derive(Clone)]
pub struct ExistentialRules {
    /// The polymorphic definition of `∃`.
    pub definition: Thm,
    /// The polymorphic definition of `∀`.
    pub universal_definition: Thm,
    /// The derived implication rules.
    pub implication_rules: ImplicationRules,
    /// `⊢ T`.
    pub truth: Thm,
    /// `⊢ (p = T) = p`.
    pub true_right: Thm,
}

impl Kernel {
    /// Define `∃` at the type variable `A` using `new_basic_definition`.
    pub fn define_existential(&mut self, theory: TheoryId) -> Result<Thm> {
        let element = self.ty_var("A")?;
        let ty = self.existential_type(element)?;
        let lhs = self.term_var("∃", ty)?;
        let rhs = self.existential_rhs(theory, element)?;
        let equation = self.term_eq(lhs, rhs)?;
        self.new_basic_definition(theory, equation)
    }

    /// From a proof of a witness instance, prove the requested existential.
    pub fn exists(
        &mut self,
        theory: TheoryId,
        rules: &ExistentialRules,
        existential: Term,
        witness: Term,
        thm: &Thm,
    ) -> Result<Thm> {
        let Some((var, body)) = self.dest_exists(existential) else {
            return Err(Error::Rule(format!(
                "EXISTS: {} is not an existential quantification",
                self.term_to_string(existential)
            )));
        };
        let instance = self.subst(&BTreeMap::from([(var, witness)]), body)?;
        if thm.concl() != instance {
            return Err(Error::Rule(format!(
                "EXISTS: {} is not {}",
                self.term_to_string(thm.concl()),
                self.term_to_string(instance)
            )));
        }

        let conclusion = self.existential_conclusion_variable(var, body, thm.hyps())?;
        let body_implication = self.mk_imp(theory, body, conclusion)?;
        let premise = self.mk_forall(theory, var, body_implication)?;
        let quantified =
            self.existential_prove_body(theory, rules, witness, thm, conclusion, premise)?;
        let predicate = self.term_abs(var, body)?;
        let unfolded =
            self.existential_unfolded(theory, &rules.definition, self.type_of(var), predicate)?;
        let backwards = self.sym(theory, &unfolded)?;
        self.eq_mp(theory, &backwards, &quantified)
    }

    /// `Γ ⊢ p[x]` gives `Γ ⊢ ∃x. p[x]`, using `x` as the witness.
    pub fn simple_exists(
        &mut self,
        theory: TheoryId,
        rules: &ExistentialRules,
        var: Term,
        thm: &Thm,
    ) -> Result<Thm> {
        let existential = self.mk_exists(theory, var, thm.concl())?;
        self.exists(theory, rules, existential, var, thm)
    }

    /// `Γ ⊢ ∃x. p[x]` and `Δ ⊢ q` give `(Γ ∪ Δ) - p[x] ⊢ q` when `x` is
    /// free in neither the conclusion nor the surviving hypotheses.
    pub fn choose(
        &mut self,
        theory: TheoryId,
        rules: &ExistentialRules,
        existential: &Thm,
        body: &Thm,
    ) -> Result<Thm> {
        let Some((var, witness_body)) = self.dest_exists(existential.concl()) else {
            return Err(Error::Rule(format!(
                "CHOOSE: {} is not an existential quantification",
                self.term_to_string(existential.concl())
            )));
        };
        if self.free_in(var, body.concl()) {
            return Err(Error::Rule(format!(
                "CHOOSE: {} is free in the conclusion",
                self.term_to_string(var)
            )));
        }

        let selected = self.existential_choose_rule(
            theory,
            rules,
            existential,
            var,
            witness_body,
            body.concl(),
        )?;
        let branch = self.disch(theory, &rules.implication_rules, witness_body, body)?;
        let branch_with_existential_hyps = self.prove_hyp(theory, existential, &branch)?;
        let generalized = self.gen(
            theory,
            &rules.universal_definition,
            &rules.true_right,
            var,
            &branch_with_existential_hyps,
        )?;
        self.mp(theory, &rules.implication_rules, &selected, &generalized)
    }

    fn existential_type(&mut self, element: Ty) -> Result<Ty> {
        let bool_ty = self.bool_ty();
        let predicate = self.ty_fun(element, bool_ty)?;
        self.ty_fun(predicate, bool_ty)
    }

    fn existential_rhs(&mut self, theory: TheoryId, element: Ty) -> Result<Term> {
        let bool_ty = self.bool_ty();
        let predicate_ty = self.ty_fun(element, bool_ty)?;
        let predicate = self.term_var("P", predicate_ty)?;
        let body = self.existential_body(theory, element, predicate)?;
        self.term_abs(predicate, body)
    }

    fn existential_body(&mut self, theory: TheoryId, element: Ty, predicate: Term) -> Result<Term> {
        let conclusion = self.term_var("q", self.bool_ty())?;
        let witness = self.term_var("x", element)?;
        let instance = self.term_comb(predicate, witness)?;
        let implication = self.mk_imp(theory, instance, conclusion)?;
        let universal = self.mk_forall(theory, witness, implication)?;
        let body = self.mk_imp(theory, universal, conclusion)?;
        self.mk_forall(theory, conclusion, body)
    }

    fn existential_prove_body(
        &mut self,
        theory: TheoryId,
        rules: &ExistentialRules,
        witness: Term,
        thm: &Thm,
        conclusion: Term,
        premise: Term,
    ) -> Result<Thm> {
        let assumed = self.assume(theory, premise)?;
        let implication = self.spec(
            theory,
            &rules.universal_definition,
            &rules.truth,
            &assumed,
            witness,
        )?;
        let proved = self.mp(theory, &rules.implication_rules, &implication, thm)?;
        let discharged = self.disch(theory, &rules.implication_rules, premise, &proved)?;
        self.gen(
            theory,
            &rules.universal_definition,
            &rules.true_right,
            conclusion,
            &discharged,
        )
    }

    fn existential_choose_rule(
        &mut self,
        theory: TheoryId,
        rules: &ExistentialRules,
        existential: &Thm,
        var: Term,
        witness_body: Term,
        goal: Term,
    ) -> Result<Thm> {
        let predicate = self.term_abs(var, witness_body)?;
        let unfolded =
            self.existential_unfolded(theory, &rules.definition, self.type_of(var), predicate)?;
        let expanded = self.eq_mp(theory, &unfolded, existential)?;
        self.spec(
            theory,
            &rules.universal_definition,
            &rules.truth,
            &expanded,
            goal,
        )
    }

    fn existential_unfolded(
        &mut self,
        theory: TheoryId,
        definition: &Thm,
        element: Ty,
        predicate: Term,
    ) -> Result<Thm> {
        let instance = self.existential_instance(theory, definition, element)?;
        let applied = self.ap_thm(theory, &instance, predicate)?;
        self.beta_rule(theory, &applied)
    }

    fn existential_instance(
        &mut self,
        theory: TheoryId,
        definition: &Thm,
        element: Ty,
    ) -> Result<Thm> {
        let Some((lhs, _)) = self.dest_eq(definition.concl()) else {
            return Err(Error::Rule(format!(
                "EXISTS_DEF: {} is not an equation",
                self.term_to_string(definition.concl())
            )));
        };
        let wanted = self.existential_type(element)?;
        if self.type_of(lhs) == wanted {
            return Ok(definition.clone());
        }
        let a = self.ty_var("A")?;
        self.inst_type(theory, &BTreeMap::from([(a, element)]), definition)
    }

    fn existential_conclusion_variable(
        &mut self,
        var: Term,
        body: Term,
        hyps: &[Term],
    ) -> Result<Term> {
        let mut avoid = self.frees(body).to_vec();
        avoid.push(var);
        for hyp in hyps {
            avoid.extend_from_slice(self.frees(*hyp));
        }
        self.variant(&avoid, "q", self.bool_ty())
    }
}
