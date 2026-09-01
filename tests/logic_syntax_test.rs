//! The syntax half of the logic layer: how the connectives are spelled, and
//! how they come apart again.
//!
//! Nothing here proves anything, so nothing here needs a definition — the
//! fixture declares the six constants outright and the tests are about term
//! shape only. Assertions compare terms, never printed strings.

use adamas::{Kernel, Result, Term, TheoryId, Ty};

struct Fixture {
    k: Kernel,
    th: TheoryId,
    bool_ty: Ty,
    a: Ty,
    p: Term,
    q: Term,
}

impl Fixture {
    fn new() -> Result<Self> {
        let mut k = Kernel::new();
        let th = k.new_theory("syntax");
        let bool_ty = k.bool_ty();
        let a = k.ty_var("A")?;

        let binary = {
            let inner = k.ty_fun(bool_ty, bool_ty)?;
            k.ty_fun(bool_ty, inner)?
        };
        for name in ["∧", "⇒", "∨"] {
            k.new_constant(th, name, binary)?;
        }
        let unary = k.ty_fun(bool_ty, bool_ty)?;
        k.new_constant(th, "¬", unary)?;
        let quantifier = {
            let predicate = k.ty_fun(a, bool_ty)?;
            k.ty_fun(predicate, bool_ty)?
        };
        for name in ["∀", "∃"] {
            k.new_constant(th, name, quantifier)?;
        }

        let p = k.term_var("p", bool_ty)?;
        let q = k.term_var("q", bool_ty)?;
        Ok(Fixture {
            k,
            th,
            bool_ty,
            a,
            p,
            q,
        })
    }

    /// `c left right`, assembled by hand rather than by the code under test.
    fn binary(&mut self, name: &str, left: Term, right: Term) -> Result<Term> {
        let inner = self.k.ty_fun(self.bool_ty, self.bool_ty)?;
        let ty = self.k.ty_fun(self.bool_ty, inner)?;
        let c = self.k.constant(self.th, name, Some(ty))?;
        let half = self.k.term_comb(c, left)?;
        self.k.term_comb(half, right)
    }

    /// `c (λvar. body)`, assembled by hand.
    fn quantified(&mut self, name: &str, var: Term, body: Term) -> Result<Term> {
        let element = self.k.type_of(var);
        let predicate = self.k.ty_fun(element, self.bool_ty)?;
        let ty = self.k.ty_fun(predicate, self.bool_ty)?;
        let c = self.k.constant(self.th, name, Some(ty))?;
        let lam = self.k.term_abs(var, body)?;
        self.k.term_comb(c, lam)
    }
}

// --- the binary connectives -----------------------------------------------

#[test]
fn the_binary_connectives_are_curried_applications() -> Result<()> {
    let mut fx = Fixture::new()?;
    let (p, q) = (fx.p, fx.q);

    let conj = fx.k.mk_conj(fx.th, p, q)?;
    assert_eq!(conj, fx.binary("∧", p, q)?);
    let imp = fx.k.mk_imp(fx.th, p, q)?;
    assert_eq!(imp, fx.binary("⇒", p, q)?);
    let disj = fx.k.mk_disj(fx.th, p, q)?;
    assert_eq!(disj, fx.binary("∨", p, q)?);
    Ok(())
}

#[test]
fn the_binary_connectives_come_apart_again() -> Result<()> {
    let mut fx = Fixture::new()?;
    let (p, q) = (fx.p, fx.q);

    let conj = fx.k.mk_conj(fx.th, p, q)?;
    assert_eq!(fx.k.dest_conj(conj), Some((p, q)));
    let imp = fx.k.mk_imp(fx.th, p, q)?;
    assert_eq!(fx.k.dest_imp(imp), Some((p, q)));
    let disj = fx.k.mk_disj(fx.th, p, q)?;
    assert_eq!(fx.k.dest_disj(disj), Some((p, q)));
    Ok(())
}

#[test]
fn a_destructor_refuses_the_wrong_connective() -> Result<()> {
    let mut fx = Fixture::new()?;
    let (p, q) = (fx.p, fx.q);
    let conj = fx.k.mk_conj(fx.th, p, q)?;

    assert_eq!(fx.k.dest_imp(conj), None);
    assert_eq!(fx.k.dest_disj(conj), None);
    assert_eq!(fx.k.dest_neg(conj), None);
    assert_eq!(fx.k.dest_conj(p), None);
    Ok(())
}

#[test]
fn negation_is_a_single_application() -> Result<()> {
    let mut fx = Fixture::new()?;
    let p = fx.p;

    let neg = fx.k.mk_neg(fx.th, p)?;
    let unary = fx.k.ty_fun(fx.bool_ty, fx.bool_ty)?;
    let c = fx.k.constant(fx.th, "¬", Some(unary))?;
    assert_eq!(neg, fx.k.term_comb(c, p)?);
    assert_eq!(fx.k.dest_neg(neg), Some(p));
    assert_eq!(fx.k.dest_neg(p), None);
    Ok(())
}

#[test]
fn excluded_middle_is_a_term_not_a_theorem() -> Result<()> {
    let mut fx = Fixture::new()?;
    let p = fx.p;

    let em = fx.k.excluded_middle(fx.th, p)?;
    let neg = fx.k.mk_neg(fx.th, p)?;
    assert_eq!(em, fx.k.mk_disj(fx.th, p, neg)?);
    Ok(())
}

// --- the quantifiers ------------------------------------------------------

#[test]
fn a_quantifier_wraps_an_abstraction_at_the_bound_variables_type() -> Result<()> {
    let mut fx = Fixture::new()?;
    let x = fx.k.term_var("x", fx.a)?;
    let body = fx.p;

    let all = fx.k.mk_forall(fx.th, x, body)?;
    assert_eq!(all, fx.quantified("∀", x, body)?);
    let some = fx.k.mk_exists(fx.th, x, body)?;
    assert_eq!(some, fx.quantified("∃", x, body)?);
    Ok(())
}

#[test]
fn a_quantifier_instantiates_its_constant_to_the_element_type() -> Result<()> {
    let mut fx = Fixture::new()?;
    let x = fx.k.term_var("x", fx.bool_ty)?;
    let body = fx.k.term_eq(x, x)?;

    let all = fx.k.mk_forall(fx.th, x, body)?;
    assert_eq!(all, fx.quantified("∀", x, body)?);
    Ok(())
}

#[test]
fn the_quantifiers_come_apart_again() -> Result<()> {
    let mut fx = Fixture::new()?;
    let x = fx.k.term_var("x", fx.bool_ty)?;
    let body = fx.k.term_eq(x, x)?;

    let all = fx.k.mk_forall(fx.th, x, body)?;
    assert_eq!(fx.k.dest_forall(all), Some((x, body)));
    let some = fx.k.mk_exists(fx.th, x, body)?;
    assert_eq!(fx.k.dest_exists(some), Some((x, body)));

    assert_eq!(fx.k.dest_forall(some), None);
    assert_eq!(fx.k.dest_exists(all), None);
    let p = fx.p;
    assert_eq!(fx.k.dest_forall(p), None);
    Ok(())
}

#[test]
fn the_syntax_layer_asserts_nothing() -> Result<()> {
    let mut fx = Fixture::new()?;
    let (p, q) = (fx.p, fx.q);
    fx.k.mk_conj(fx.th, p, q)?;
    fx.k.mk_neg(fx.th, p)?;

    assert!(fx.k.axioms(fx.th).is_empty());
    assert!(fx.k.definitions(fx.th).is_empty());
    Ok(())
}
