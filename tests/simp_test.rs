//! Ruby `origin/main`'s complete logical simp set, checked as terms.

use adamas::{Kernel, LogicBootstrap, Ordering, Result, Term, TheoryId};

struct Fixture {
    k: Kernel,
    th: TheoryId,
    boot: LogicBootstrap,
    p: Term,
}

impl Fixture {
    fn new() -> Result<Self> {
        let mut k = Kernel::new();
        let th = k.new_theory("simp");
        let boot = k.install_logic(th)?;
        let p = k.term_var("p", k.bool_ty())?;
        Ok(Self { k, th, boot, p })
    }

    fn assert_rule(&mut self, name: &str, lhs: Term, rhs: Term) -> Result<()> {
        let rule = self.boot.rules.fetch(name)?;
        let expected = self.k.term_eq(lhs, rhs)?;
        assert_eq!(rule.thm.concl(), expected, "wrong conclusion for {name}");
        assert!(rule.thm.hyps().is_empty(), "{name} carries hypotheses");
        Ok(())
    }
}

#[test]
fn install_registers_the_sixteen_rules_in_ruby_order() -> Result<()> {
    let fx = Fixture::new()?;

    assert_eq!(
        fx.boot.rules.names(),
        vec![
            "refl",
            "true_left",
            "true_right",
            "conj_true_left",
            "conj_true_right",
            "conj_false_left",
            "conj_idempotent",
            "imp_true_left",
            "imp_true_right",
            "imp_false_left",
            "disj_true_left",
            "disj_true_right",
            "disj_false_left",
            "neg_true",
            "neg_false",
            "forall_true",
        ]
    );
    assert_eq!(fx.boot.rules.len(), 16);
    Ok(())
}

#[test]
fn every_installed_rule_is_hypothesis_free() -> Result<()> {
    let fx = Fixture::new()?;

    for rule in fx.boot.rules.iter() {
        assert!(
            rule.thm.hyps().is_empty(),
            "{} carries hypotheses",
            rule.name
        );
    }
    Ok(())
}

#[test]
fn the_thirteen_simp_additions_have_the_ruby_conclusions() -> Result<()> {
    let mut fx = Fixture::new()?;
    let t = fx.boot.true_const;
    let f = fx.boot.falsity_const;
    let p = fx.p;

    let lhs = fx.k.mk_conj(fx.th, t, p)?;
    fx.assert_rule("conj_true_left", lhs, p)?;
    let lhs = fx.k.mk_conj(fx.th, p, t)?;
    fx.assert_rule("conj_true_right", lhs, p)?;
    let lhs = fx.k.mk_conj(fx.th, f, p)?;
    fx.assert_rule("conj_false_left", lhs, f)?;
    let lhs = fx.k.mk_conj(fx.th, p, p)?;
    fx.assert_rule("conj_idempotent", lhs, p)?;
    let lhs = fx.k.mk_imp(fx.th, t, p)?;
    fx.assert_rule("imp_true_left", lhs, p)?;
    let lhs = fx.k.mk_imp(fx.th, p, t)?;
    fx.assert_rule("imp_true_right", lhs, t)?;
    let lhs = fx.k.mk_imp(fx.th, f, p)?;
    fx.assert_rule("imp_false_left", lhs, t)?;
    let lhs = fx.k.mk_disj(fx.th, t, p)?;
    fx.assert_rule("disj_true_left", lhs, t)?;
    let lhs = fx.k.mk_disj(fx.th, p, t)?;
    fx.assert_rule("disj_true_right", lhs, t)?;
    let lhs = fx.k.mk_disj(fx.th, f, p)?;
    fx.assert_rule("disj_false_left", lhs, p)?;
    let lhs = fx.k.mk_neg(fx.th, t)?;
    fx.assert_rule("neg_true", lhs, f)?;
    let lhs = fx.k.mk_neg(fx.th, f)?;
    fx.assert_rule("neg_false", lhs, t)?;
    let a = fx.k.ty_var("A")?;
    let x = fx.k.term_var("x", a)?;
    let lhs = fx.k.mk_forall(fx.th, x, t)?;
    fx.assert_rule("forall_true", lhs, t)?;
    Ok(())
}

#[test]
fn logic_install_with_simp_still_asserts_no_axioms() -> Result<()> {
    let fx = Fixture::new()?;

    assert!(fx.k.axioms(fx.th).is_empty());
    Ok(())
}

#[test]
fn simp_rewriter_emits_a_certificate_that_replay_reconstructs() -> Result<()> {
    let mut fx = Fixture::new()?;
    let term = fx.k.mk_conj(fx.th, fx.boot.true_const, fx.p)?;

    let certificate = fx.k.rewrite(
        term,
        &fx.boot.rules,
        adamas::DEFAULT_LIMIT,
        Ordering::Unordered,
    )?;
    assert_eq!(certificate.result, fx.p);
    assert!(certificate.complete);
    assert!(!certificate.is_empty());

    let theorem =
        fx.k.prove_certificate(fx.th, &certificate, &fx.boot.rules)?;
    assert_eq!(theorem.concl(), fx.k.term_eq(term, fx.p)?);
    assert!(theorem.hyps().is_empty());
    Ok(())
}

#[test]
fn rewriter_closes_a_term_using_every_m1_connective_and_replay_reconstructs() -> Result<()> {
    let mut fx = Fixture::new()?;
    let a = fx.k.ty_var("A")?;
    let x = fx.k.term_var("x", a)?;
    let truth = fx.boot.true_const;
    let falsity = fx.boot.falsity_const;

    let existential = fx.k.mk_exists(fx.th, x, truth)?;
    let implication = fx.k.mk_imp(fx.th, existential, truth)?;
    let disjunction = fx.k.mk_disj(fx.th, falsity, implication)?;
    let negation = fx.k.mk_neg(fx.th, falsity)?;
    let universal = fx.k.mk_forall(fx.th, x, truth)?;
    let right = fx.k.mk_conj(fx.th, disjunction, negation)?;
    let term = fx.k.mk_conj(fx.th, universal, right)?;

    let certificate = fx.k.rewrite(
        term,
        &fx.boot.rules,
        adamas::DEFAULT_LIMIT,
        Ordering::Unordered,
    )?;
    assert_eq!(certificate.result, truth);
    assert!(certificate.complete);

    let theorem =
        fx.k.prove_certificate(fx.th, &certificate, &fx.boot.rules)?;
    assert_eq!(theorem.concl(), fx.k.term_eq(term, truth)?);
    assert!(theorem.hyps().is_empty());
    Ok(())
}
