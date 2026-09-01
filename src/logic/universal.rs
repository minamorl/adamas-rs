//! Universal quantification, defined over the frozen kernel.
//!
//! Ported from adamas's `lib/adamas/logic/universal.rb`. `∀P` says that `P` is
//! the constantly-true predicate, so specialisation is application and
//! generalisation is abstraction — with `eqt_intro` and `eqt_elim` doing the
//! translation between `p` and `p = T` at each end.

use std::collections::BTreeMap;

use crate::kernel::{Error, Kernel, Result, Term, TheoryId, Thm, Ty};

impl Kernel {
    /// `⊢ ∀ = (λP. P = (λx. T))`, at the type variable `A`.
    pub fn define_universal(&mut self, theory: TheoryId, truth: &Thm) -> Result<Thm> {
        let a = self.ty_var("A")?;
        let ty = self.universal_type(a)?;
        let lhs = self.term_var("∀", ty)?;
        let rhs = self.universal_rhs(a, truth.concl())?;
        let equation = self.term_eq(lhs, rhs)?;
        self.new_basic_definition(theory, equation)
    }

    /// `Γ ⊢ ∀x. p[x]` gives `Γ ⊢ p[t]`.
    pub fn spec(
        &mut self,
        theory: TheoryId,
        definition: &Thm,
        truth: &Thm,
        thm: &Thm,
        term: Term,
    ) -> Result<Thm> {
        let Some((var, body)) = self.dest_forall(thm.concl()) else {
            return Err(Error::Rule(format!(
                "SPEC: {} is not a universal quantification",
                self.term_to_string(thm.concl())
            )));
        };
        let predicate = self.term_abs(var, body)?;
        let element = self.type_of(var);
        let unfolded = self.universal_unfolded(theory, definition, element, predicate)?;
        let expanded = self.eq_mp(theory, &unfolded, thm)?;
        let applied = self.ap_thm(theory, &expanded, term)?;
        let reduced = self.beta_rule(theory, &applied)?;
        self.eqt_elim(theory, truth, &reduced)
    }

    /// `Γ ⊢ p[x]` gives `Γ ⊢ ∀x. p[x]`, provided `x` is free in no hypothesis.
    ///
    /// That proviso is not checked here: the abstraction below is the kernel's
    /// `ABS`, which refuses it.
    pub fn gen(
        &mut self,
        theory: TheoryId,
        definition: &Thm,
        true_right: &Thm,
        var: Term,
        thm: &Thm,
    ) -> Result<Thm> {
        let predicate = self.term_abs(var, thm.concl())?;
        let pointwise = self.eqt_intro(theory, true_right, thm)?;
        let equality = self.abs(theory, var, &pointwise)?;
        let element = self.type_of(var);
        let unfolded = self.universal_unfolded(theory, definition, element, predicate)?;
        let backwards = self.sym(theory, &unfolded)?;
        self.eq_mp(theory, &backwards, &equality)
    }

    // --- the encoding ------------------------------------------------------

    fn universal_type(&mut self, element: Ty) -> Result<Ty> {
        let bool_ty = self.bool_ty();
        let predicate = self.ty_fun(element, bool_ty)?;
        self.ty_fun(predicate, bool_ty)
    }

    fn universal_rhs(&mut self, element: Ty, true_const: Term) -> Result<Term> {
        let bool_ty = self.bool_ty();
        let predicate_ty = self.ty_fun(element, bool_ty)?;
        let predicate = self.term_var("P", predicate_ty)?;
        let witness = self.term_var("x", element)?;
        let constantly_true = self.term_abs(witness, true_const)?;
        let body = self.term_eq(predicate, constantly_true)?;
        self.term_abs(predicate, body)
    }

    /// The definition at `element`'s type. `∀` is declared at `A`, so every use
    /// at another type is an `INST_TYPE` away — and at `A` itself, none.
    fn universal_instance(
        &mut self,
        theory: TheoryId,
        definition: &Thm,
        element: Ty,
    ) -> Result<Thm> {
        let Some((lhs, _)) = self.dest_eq(definition.concl()) else {
            return Err(Error::Rule(format!(
                "FORALL_DEF: {} is not an equation",
                self.term_to_string(definition.concl())
            )));
        };
        let wanted = self.universal_type(element)?;
        if self.type_of(lhs) == wanted {
            return Ok(definition.clone());
        }
        let a = self.ty_var("A")?;
        self.inst_type(theory, &BTreeMap::from([(a, element)]), definition)
    }

    /// `⊢ ∀P = (P = (λx. T))` at `element`'s type, for this `P`.
    fn universal_unfolded(
        &mut self,
        theory: TheoryId,
        definition: &Thm,
        element: Ty,
        predicate: Term,
    ) -> Result<Thm> {
        let instance = self.universal_instance(theory, definition, element)?;
        let applied = self.ap_thm(theory, &instance, predicate)?;
        self.beta_rule(theory, &applied)
    }
}
