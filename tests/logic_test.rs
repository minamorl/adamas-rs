//! The logic layer: `T`, the theorem `⊢ T`, and the derived rules that the
//! connectives are built out of.
//!
//! Every test here asserts on *terms*, not on printed strings: a `Term` is its
//! rank in the intern table, so `==` is exact and no printer convention can
//! make a wrong theorem look right.
//!
//! Two guards run in every test that installs anything. `axioms` must stay
//! empty and `definitions` must hold exactly what was defined — the whole
//! claim of this layer is that it asserts nothing, and a theorem obtained by
//! asserting it would otherwise pass every other assertion here.

use adamas::{Kernel, Result, Term, TheoryId, Ty};

struct Fixture {
    k: Kernel,
    th: TheoryId,
    bool_ty: Ty,
    p: Term,
    q: Term,
    f: Term,
}

impl Fixture {
    fn new() -> Result<Self> {
        let mut k = Kernel::new();
        let th = k.new_theory("logic");
        let bool_ty = k.bool_ty();
        let p = k.term_var("p", bool_ty)?;
        let q = k.term_var("q", bool_ty)?;
        let fun_ty = k.ty_fun(bool_ty, bool_ty)?;
        let f = k.term_var("f", fun_ty)?;
        Ok(Fixture {
            k,
            th,
            bool_ty,
            p,
            q,
            f,
        })
    }

    /// `λx:bool. body(x)`, with `x` the variable handed to `body`.
    fn lambda(
        &mut self,
        name: &str,
        body: impl FnOnce(&mut Kernel, Term) -> Result<Term>,
    ) -> Result<Term> {
        let v = self.k.term_var(name, self.bool_ty)?;
        let b = body(&mut self.k, v)?;
        self.k.term_abs(v, b)
    }
}

// --- T, and the three equations about equality ----------------------------

#[test]
fn truth_is_defined_as_the_identity_being_itself() -> Result<()> {
    let mut fx = Fixture::new()?;
    let b = fx.k.install_booleans(fx.th)?;

    let t = fx.k.constant(fx.th, "T", None)?;
    assert_eq!(b.true_const, t);

    let identity = fx.lambda("p", |_k, v| Ok(v))?;
    let rhs = fx.k.term_eq(identity, identity)?;
    let expected = fx.k.term_eq(t, rhs)?;
    assert_eq!(b.definition.concl(), expected);
    assert!(b.definition.hyps().is_empty());
    Ok(())
}

#[test]
fn truth_is_a_theorem_with_no_hypotheses() -> Result<()> {
    let mut fx = Fixture::new()?;
    let b = fx.k.install_booleans(fx.th)?;

    let t = fx.k.constant(fx.th, "T", None)?;
    assert_eq!(b.truth.concl(), t);
    assert!(b.truth.hyps().is_empty());
    Ok(())
}

#[test]
fn reflexivity_is_true() -> Result<()> {
    let mut fx = Fixture::new()?;
    let b = fx.k.install_booleans(fx.th)?;

    let a = fx.k.ty_var("A")?;
    let x = fx.k.term_var("x", a)?;
    let xx = fx.k.term_eq(x, x)?;
    let t = fx.k.constant(fx.th, "T", None)?;
    let expected = fx.k.term_eq(xx, t)?;

    assert_eq!(b.refl_is_true.concl(), expected);
    assert!(b.refl_is_true.hyps().is_empty());
    Ok(())
}

#[test]
fn true_on_the_left_and_on_the_right() -> Result<()> {
    let mut fx = Fixture::new()?;
    let b = fx.k.install_booleans(fx.th)?;
    let t = fx.k.constant(fx.th, "T", None)?;

    let t_eq_p = fx.k.term_eq(t, fx.p)?;
    let left = fx.k.term_eq(t_eq_p, fx.p)?;
    assert_eq!(b.true_left.concl(), left);
    assert!(b.true_left.hyps().is_empty());

    let p_eq_t = fx.k.term_eq(fx.p, t)?;
    let right = fx.k.term_eq(p_eq_t, fx.p)?;
    assert_eq!(b.true_right.concl(), right);
    assert!(b.true_right.hyps().is_empty());
    Ok(())
}

#[test]
fn installing_the_booleans_asserts_nothing() -> Result<()> {
    let mut fx = Fixture::new()?;
    fx.k.install_booleans(fx.th)?;

    assert!(
        fx.k.axioms(fx.th).is_empty(),
        "the boolean layer must derive, never assert"
    );
    assert_eq!(
        fx.k.definitions(fx.th).len(),
        1,
        "T is the only thing defined here"
    );
    Ok(())
}

// --- beta for an arbitrary argument ---------------------------------------

#[test]
fn a_beta_redex_is_recognised() -> Result<()> {
    let mut fx = Fixture::new()?;
    let identity = fx.lambda("x", |_k, v| Ok(v))?;
    let redex = fx.k.term_comb(identity, fx.q)?;

    assert!(fx.k.is_beta_redex(redex));
    assert!(!fx.k.is_beta_redex(identity));
    assert!(!fx.k.is_beta_redex(fx.q));
    let applied = fx.k.term_comb(fx.f, fx.q)?;
    assert!(!fx.k.is_beta_redex(applied));
    Ok(())
}

#[test]
fn beta_conv_substitutes_an_arbitrary_argument() -> Result<()> {
    let mut fx = Fixture::new()?;
    let f = fx.f;
    let body = fx.lambda("x", move |k, v| k.term_comb(f, v))?;
    let redex = fx.k.term_comb(body, fx.q)?;

    let thm = fx.k.beta_conv(fx.th, redex)?;

    let fq = fx.k.term_comb(fx.f, fx.q)?;
    let expected = fx.k.term_eq(redex, fq)?;
    assert_eq!(thm.concl(), expected);
    assert!(thm.hyps().is_empty());
    Ok(())
}

#[test]
fn beta_conv_refuses_a_term_that_is_not_a_redex() -> Result<()> {
    let mut fx = Fixture::new()?;
    let applied = fx.k.term_comb(fx.f, fx.q)?;
    assert!(fx.k.beta_conv(fx.th, applied).is_err());
    Ok(())
}

#[test]
fn beta_reduce_descends_into_a_subterm() -> Result<()> {
    let mut fx = Fixture::new()?;
    let identity = fx.lambda("x", |_k, v| Ok(v))?;
    let redex = fx.k.term_comb(identity, fx.q)?;
    let outer = fx.k.term_comb(fx.f, redex)?;

    let thm = fx.k.beta_reduce(fx.th, outer)?;

    let fq = fx.k.term_comb(fx.f, fx.q)?;
    let expected = fx.k.term_eq(outer, fq)?;
    assert_eq!(thm.concl(), expected);
    assert!(thm.hyps().is_empty());
    Ok(())
}

#[test]
fn beta_reduce_reaches_the_normal_form_of_a_nested_redex() -> Result<()> {
    let mut fx = Fixture::new()?;
    let f = fx.f;
    let apply_f = fx.lambda("x", move |k, v| k.term_comb(f, v))?;
    let identity = fx.lambda("y", |_k, v| Ok(v))?;
    let inner = fx.k.term_comb(identity, fx.q)?;
    let term = fx.k.term_comb(apply_f, inner)?;

    let thm = fx.k.beta_reduce(fx.th, term)?;

    let fq = fx.k.term_comb(fx.f, fx.q)?;
    let expected = fx.k.term_eq(term, fq)?;
    assert_eq!(thm.concl(), expected);
    Ok(())
}

#[test]
fn beta_reduce_of_a_normal_term_is_reflexivity() -> Result<()> {
    let mut fx = Fixture::new()?;
    let fq = fx.k.term_comb(fx.f, fx.q)?;

    let thm = fx.k.beta_reduce(fx.th, fq)?;

    let expected = fx.k.term_eq(fq, fq)?;
    assert_eq!(thm.concl(), expected);
    Ok(())
}

#[test]
fn beta_rule_normalises_a_conclusion_and_keeps_the_hypotheses() -> Result<()> {
    let mut fx = Fixture::new()?;
    let identity = fx.lambda("x", |_k, v| Ok(v))?;
    let redex = fx.k.term_comb(identity, fx.q)?;
    let assumed = fx.k.assume(fx.th, redex)?;

    let thm = fx.k.beta_rule(fx.th, &assumed)?;

    assert_eq!(thm.concl(), fx.q);
    assert_eq!(thm.hyps(), &[redex]);
    Ok(())
}

// --- p ⟹ p = T -------------------------------------------------------------

#[test]
fn eqt_intro_turns_a_theorem_into_an_equation_with_truth() -> Result<()> {
    let mut fx = Fixture::new()?;
    let b = fx.k.install_booleans(fx.th)?;
    let assumed = fx.k.assume(fx.th, fx.p)?;

    let thm = fx.k.eqt_intro(fx.th, &b.true_right, &assumed)?;

    let t = fx.k.constant(fx.th, "T", None)?;
    let expected = fx.k.term_eq(fx.p, t)?;
    assert_eq!(thm.concl(), expected);
    assert_eq!(thm.hyps(), &[fx.p]);
    assert!(fx.k.axioms(fx.th).is_empty());
    Ok(())
}

#[test]
fn eqt_elim_is_the_inverse_of_eqt_intro() -> Result<()> {
    let mut fx = Fixture::new()?;
    let b = fx.k.install_booleans(fx.th)?;
    let assumed = fx.k.assume(fx.th, fx.q)?;

    let equation = fx.k.eqt_intro(fx.th, &b.true_right, &assumed)?;
    let back = fx.k.eqt_elim(fx.th, &b.truth, &equation)?;

    assert_eq!(back.concl(), fx.q);
    assert_eq!(back.hyps(), &[fx.q]);
    Ok(())
}
