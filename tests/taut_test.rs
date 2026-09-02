//! Ruby `origin/main`'s proof-producing propositional tautology tests.

use adamas::logic::{classical, taut};
use adamas::{ClassicalBundle, Kernel, LogicBootstrap, Result, Term, TheoryId};

struct Fixture {
    k: Kernel,
    th: TheoryId,
    boot: LogicBootstrap,
    classical: ClassicalBundle,
    p: Term,
    q: Term,
}

impl Fixture {
    fn new() -> Result<Self> {
        let mut k = Kernel::new();
        let th = k.new_theory("taut");
        let boot = k.install_logic(th)?;
        let classical = classical::install(&mut k, th, &boot)?;
        let p = k.term_var("p", k.bool_ty())?;
        let q = k.term_var("q", k.bool_ty())?;
        Ok(Self {
            k,
            th,
            boot,
            classical,
            p,
            q,
        })
    }
}

#[test]
fn proves_a_tautology_without_hypotheses() -> Result<()> {
    let mut fx = Fixture::new()?;
    let not_p = fx.k.mk_neg(fx.th, fx.p)?;
    let formula = fx.k.mk_disj(fx.th, fx.p, not_p)?;

    let theorem = taut::prove(&mut fx.k, fx.th, &fx.boot, &fx.classical, formula)?
        .expect("excluded middle is a tautology");

    assert!(theorem.hyps().is_empty());
    assert_eq!(theorem.concl(), formula);
    Ok(())
}

#[test]
fn treats_boolean_equality_as_a_biconditional() -> Result<()> {
    let mut fx = Fixture::new()?;
    let left = fx.k.mk_disj(fx.th, fx.p, fx.q)?;
    let right = fx.k.mk_disj(fx.th, fx.q, fx.p)?;
    let formula = fx.k.term_eq(left, right)?;

    let theorem = taut::prove(&mut fx.k, fx.th, &fx.boot, &fx.classical, formula)?
        .expect("commutativity is a tautology");

    assert!(theorem.hyps().is_empty());
    assert_eq!(theorem.concl(), formula);
    Ok(())
}

#[test]
fn refuses_a_non_tautology() -> Result<()> {
    let mut fx = Fixture::new()?;

    assert!(taut::prove(&mut fx.k, fx.th, &fx.boot, &fx.classical, fx.p)?.is_none());
    Ok(())
}

#[test]
fn atom_limit_is_explicit_and_enforced() -> Result<()> {
    let mut fx = Fixture::new()?;
    let formula = fx.k.mk_disj(fx.th, fx.p, fx.q)?;

    let error =
        taut::prove_with_limit(&mut fx.k, fx.th, &fx.boot, &fx.classical, formula, 1).unwrap_err();

    assert!(
        error.to_string().contains("2 atoms exceed the limit of 1"),
        "{error}"
    );
    assert_eq!(taut::MAX_ATOMS, 12);
    Ok(())
}

#[test]
fn only_classical_install_contributes_axioms() -> Result<()> {
    let mut fx = Fixture::new()?;
    let formula = fx.k.mk_imp(fx.th, fx.p, fx.p)?;

    let theorem = taut::prove(&mut fx.k, fx.th, &fx.boot, &fx.classical, formula)?
        .expect("identity implication is a tautology");

    assert!(theorem.hyps().is_empty());
    assert_eq!(fx.k.axioms(fx.th).len(), 2);
    Ok(())
}
