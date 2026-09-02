//! Opt-in classical logic from ETA and SELECT.
//!
//! These are Term-level ports of Ruby `origin/main`'s classical install tests.
//! In particular, excluded middle is checked as a derived theorem, not merely
//! by its printed shape.

use std::collections::BTreeMap;

use adamas::logic::classical;
use adamas::{ClassicalBundle, Kernel, LogicBootstrap, Result, Term, TheoryId, Ty};

struct Fixture {
    k: Kernel,
    th: TheoryId,
    boot: LogicBootstrap,
    classical: ClassicalBundle,
}

impl Fixture {
    fn new() -> Result<Self> {
        let mut k = Kernel::new();
        let th = k.new_theory("classical");
        let boot = k.install_logic(th)?;
        let classical = classical::install(&mut k, th, &boot)?;
        Ok(Self {
            k,
            th,
            boot,
            classical,
        })
    }
}

fn eta_axiom(k: &mut Kernel, th: TheoryId) -> Result<Term> {
    let a = k.ty_var("A")?;
    let b = k.ty_var("B")?;
    let function_ty = k.ty_fun(a, b)?;
    let function = k.term_var("t", function_ty)?;
    let argument = k.term_var("x", a)?;
    let application = k.term_comb(function, argument)?;
    let expansion = k.term_abs(argument, application)?;
    let equality = k.term_eq(expansion, function)?;
    k.mk_forall(th, function, equality)
}

fn select_axiom(k: &mut Kernel, th: TheoryId) -> Result<Term> {
    let a = k.ty_var("A")?;
    let bool_ty = k.bool_ty();
    let predicate_ty = k.ty_fun(a, bool_ty)?;
    let predicate = k.term_var("P", predicate_ty)?;
    let witness = k.term_var("x", a)?;
    let select_ty = classical::select_type(k, a)?;
    let select = k.constant(th, "@", Some(select_ty))?;
    let choice = k.term_comb(select, predicate)?;
    let selected = k.term_comb(predicate, choice)?;
    let instance = k.term_comb(predicate, witness)?;
    let body = k.mk_imp(th, instance, selected)?;
    let inner = k.mk_forall(th, witness, body)?;
    k.mk_forall(th, predicate, inner)
}

#[test]
fn a_fresh_theory_is_constructive_by_default() {
    let mut k = Kernel::new();
    let th = k.new_theory("constructive");

    assert!(k.axioms(th).is_empty());
    assert!(!k.has_constant(th, "@"));
}

#[test]
fn installing_logic_alone_is_constructive() -> Result<()> {
    let mut k = Kernel::new();
    let th = k.new_theory("constructive logic");

    k.install_logic(th)?;

    assert!(k.axioms(th).is_empty());
    assert!(!k.has_constant(th, "@"));
    Ok(())
}

#[test]
fn install_adds_exactly_eta_then_select() -> Result<()> {
    let mut fx = Fixture::new()?;

    assert_eq!(fx.k.axioms(fx.th).len(), 2);
    assert_eq!(fx.k.axioms(fx.th)[0], fx.classical.eta_ax);
    assert_eq!(fx.k.axioms(fx.th)[1], fx.classical.select_ax);
    assert_eq!(fx.classical.eta_ax.concl(), eta_axiom(&mut fx.k, fx.th)?);
    assert_eq!(
        fx.classical.select_ax.concl(),
        select_axiom(&mut fx.k, fx.th)?
    );

    let declared = fx.k.ty_var("A")?;
    let instance = fx.k.ty_var("X")?;
    let instantiated = fx.k.inst_type_term(
        &BTreeMap::from([(declared, instance)]),
        fx.classical.select_const,
    )?;
    let select_ty = classical::select_type(&mut fx.k, instance)?;
    assert_eq!(instantiated, fx.k.constant(fx.th, "@", Some(select_ty))?);
    Ok(())
}

#[test]
fn excluded_middle_is_derived_without_hypotheses() -> Result<()> {
    let mut fx = Fixture::new()?;
    let proposition = fx.k.term_var("t", fx.k.bool_ty())?;
    let instance = fx.k.excluded_middle(fx.th, proposition)?;
    let expected = fx.k.mk_forall(fx.th, proposition, instance)?;

    assert!(fx.classical.excluded_middle.hyps().is_empty());
    assert_eq!(fx.classical.excluded_middle.concl(), expected);
    assert_eq!(fx.k.axioms(fx.th).len(), 2);
    assert!(fx
        .k
        .axioms(fx.th)
        .iter()
        .all(|axiom| axiom.concl() != fx.classical.excluded_middle.concl()));
    Ok(())
}

#[test]
fn excluded_middle_function_repeats_the_derivation_exactly() -> Result<()> {
    let mut fx = Fixture::new()?;

    let derived = classical::excluded_middle(&mut fx.k, fx.th, &fx.classical, &fx.boot)?;

    assert_eq!(derived, fx.classical.excluded_middle);
    assert_eq!(fx.k.axioms(fx.th).len(), 2);
    Ok(())
}

#[test]
fn em_specializes_excluded_middle() -> Result<()> {
    let mut fx = Fixture::new()?;
    let proposition = fx.k.term_var("p", fx.k.bool_ty())?;

    let theorem = classical::em(&mut fx.k, fx.th, &fx.classical, &fx.boot, proposition)?;

    assert!(theorem.hyps().is_empty());
    assert_eq!(theorem.concl(), fx.k.excluded_middle(fx.th, proposition)?);
    Ok(())
}

#[test]
fn select_rule_eliminates_an_existential_and_preserves_hypotheses() -> Result<()> {
    let mut fx = Fixture::new()?;
    let a = fx.k.ty_var("A")?;
    let predicate_ty = fx.k.ty_fun(a, fx.k.bool_ty())?;
    let predicate = fx.k.term_var("P", predicate_ty)?;
    let witness = fx.k.term_var("x", a)?;
    let instance = fx.k.term_comb(predicate, witness)?;
    let target = fx.k.mk_exists(fx.th, witness, instance)?;
    let assumed = fx.k.assume(fx.th, instance)?;
    let existential =
        fx.k.exists(fx.th, &fx.boot.existential_rules, target, witness, &assumed)?;

    let theorem = classical::select_rule(&mut fx.k, fx.th, &fx.classical, &fx.boot, &existential)?;

    let select_ty = classical::select_type(&mut fx.k, a)?;
    let select = fx.k.constant(fx.th, "@", Some(select_ty))?;
    let choice = fx.k.term_comb(select, predicate)?;
    let expected = fx.k.term_comb(predicate, choice)?;
    assert_eq!(theorem.concl(), expected);
    assert_eq!(theorem.hyps(), &[instance]);
    Ok(())
}

#[test]
fn select_rule_refuses_a_non_existential_theorem() -> Result<()> {
    let mut fx = Fixture::new()?;
    let proposition = fx.k.term_var("p", fx.k.bool_ty())?;
    let theorem = fx.k.assume(fx.th, proposition)?;

    assert!(classical::select_rule(&mut fx.k, fx.th, &fx.classical, &fx.boot, &theorem,).is_err());
    Ok(())
}

#[test]
fn select_type_is_predicate_to_element() -> Result<()> {
    let mut k = Kernel::new();
    let a: Ty = k.ty_var("A")?;
    let predicate = k.ty_fun(a, k.bool_ty())?;
    let expected = k.ty_fun(predicate, a)?;

    assert_eq!(classical::select_type(&mut k, a)?, expected);
    Ok(())
}
