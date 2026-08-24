//! Certificate replay. Ported from adamas's replay tests.
//!
//! A certificate is a *plan*, not a proof, so the tests that matter are the
//! refusals. Anyone can write a checker that accepts true certificates; the
//! whole value of this layer is that a rewriter which lied about a position, a
//! substitution, which rule fired, or where it ended up gets no theorem.

use std::collections::BTreeMap;

use adamas::{Certificate, Condition, Kernel, PathStep, Result, RuleSet, Step, Term, TheoryId, Ty};

/// A theory with `T` defined, constants `a b c : bool`, `f g : bool → bool`,
/// and the rules a certificate can name.
struct Fixture {
    k: Kernel,
    th: TheoryId,
    rules: RuleSet,
    bool_ty: Ty,
    a: Term,
    b: Term,
    c: Term,
    f: Term,
    g: Term,
    truth: Term,
}

impl Fixture {
    fn new() -> Result<Self> {
        let mut k = Kernel::new();
        let th = k.new_theory("replay");
        let bool_ty = k.bool_ty();
        let fun_ty = k.ty_fun(bool_ty, bool_ty)?;

        // T = ((λx. x) = (λx. x)), so conditions have something to discharge to.
        let x = k.term_var("x", bool_ty)?;
        let idf = k.term_abs(x, x)?;
        let rhs = k.term_eq(idf, idf)?;
        let t_var = k.term_var("T", bool_ty)?;
        let defn = k.term_eq(t_var, rhs)?;
        k.new_basic_definition(th, defn)?;
        let truth = k.constant(th, "T", None)?;

        let a = k.new_constant(th, "a", bool_ty)?;
        let b = k.new_constant(th, "b", bool_ty)?;
        let c = k.new_constant(th, "c", bool_ty)?;
        let f = k.new_constant(th, "f", fun_ty)?;
        let g = k.new_constant(th, "g", fun_ty)?;

        let mut rules = RuleSet::new();

        // ab: ⊢ a = b
        let ab_term = k.term_eq(a, b)?;
        let ab = k.new_axiom(th, ab_term)?;
        rules.add(&k, "ab", ab)?;

        // fg: ⊢ f = g
        let fg_term = k.term_eq(f, g)?;
        let fg = k.new_axiom(th, fg_term)?;
        rules.add(&k, "fg", fg)?;

        // fx: ⊢ f x = x, a rule with a variable the certificate must instantiate
        let v = k.term_var("v", bool_ty)?;
        let fv = k.term_comb(f, v)?;
        let fx_term = k.term_eq(fv, v)?;
        let fx = k.new_axiom(th, fx_term)?;
        rules.add(&k, "fx", fx)?;

        // ct: ⊢ c = T, so a condition can be discharged
        let ct_term = k.term_eq(c, truth)?;
        let ct = k.new_axiom(th, ct_term)?;
        rules.add(&k, "ct", ct)?;

        // cond: c ⊢ a = b, a conditional rule.
        // Built from ⊢ c = (a = b) and ASSUME c, so the hypothesis is real.
        let inner = k.term_eq(a, b)?;
        let implication = k.term_eq(c, inner)?;
        let axiom = k.new_axiom(th, implication)?;
        let assumed = k.assume(th, c)?;
        let cond = k.eq_mp(th, &axiom, &assumed)?;
        assert_eq!(k.thm_to_string(&cond), "c ⊢ a = b");
        rules.add(&k, "cond", cond)?;

        Ok(Fixture {
            k,
            th,
            rules,
            bool_ty,
            a,
            b,
            c,
            f,
            g,
            truth,
        })
    }

    fn prove(&mut self, cert: &Certificate) -> Result<String> {
        let thm = self.k.prove_certificate(self.th, cert, &self.rules)?;
        Ok(self.k.thm_to_string(&thm))
    }
}

// --- the certificate holds up ----------------------------------------------

#[test]
fn an_empty_certificate_is_reflexivity() -> Result<()> {
    let mut f = Fixture::new()?;
    let cert = Certificate::new(f.a, vec![], f.a, true);
    assert_eq!(f.prove(&cert)?, "⊢ a = a");
    Ok(())
}

#[test]
fn a_step_at_the_root_is_the_rule_itself() -> Result<()> {
    let mut f = Fixture::new()?;
    let cert = Certificate::new(f.a, vec![Step::new(vec![], "ab")], f.b, true);
    assert_eq!(f.prove(&cert)?, "⊢ a = b");
    Ok(())
}

#[test]
fn a_step_under_rand_comes_back_up_with_mk_comb() -> Result<()> {
    let mut f = Fixture::new()?;
    let fa = f.k.term_comb(f.f, f.a)?;
    let fb = f.k.term_comb(f.f, f.b)?;
    let cert = Certificate::new(fa, vec![Step::new(vec![PathStep::Rand], "ab")], fb, true);
    assert_eq!(f.prove(&cert)?, "⊢ f a = f b");
    Ok(())
}

#[test]
fn a_step_under_rator_comes_back_up_with_mk_comb() -> Result<()> {
    let mut f = Fixture::new()?;
    let fa = f.k.term_comb(f.f, f.a)?;
    let ga = f.k.term_comb(f.g, f.a)?;
    let cert = Certificate::new(fa, vec![Step::new(vec![PathStep::Rator], "fg")], ga, true);
    assert_eq!(f.prove(&cert)?, "⊢ f a = g a");
    Ok(())
}

#[test]
fn a_step_under_a_binder_comes_back_up_with_abs() -> Result<()> {
    let mut f = Fixture::new()?;
    let x = f.k.term_var("x", f.bool_ty)?;
    let lam_a = f.k.term_abs(x, f.a)?; // λx. a
    let lam_b = f.k.term_abs(x, f.b)?; // λx. b
    let cert = Certificate::new(
        lam_a,
        vec![Step::new(vec![PathStep::Body], "ab")],
        lam_b,
        true,
    );
    assert_eq!(f.prove(&cert)?, "⊢ (λx. a) = (λx. b)");
    Ok(())
}

#[test]
fn steps_are_chained_with_trans() -> Result<()> {
    let mut f = Fixture::new()?;
    let fa = f.k.term_comb(f.f, f.a)?;
    let gb = f.k.term_comb(f.g, f.b)?;
    let cert = Certificate::new(
        fa,
        vec![
            Step::new(vec![PathStep::Rand], "ab"),  // f a → f b
            Step::new(vec![PathStep::Rator], "fg"), // f b → g b
        ],
        gb,
        true,
    );
    assert_eq!(f.prove(&cert)?, "⊢ f a = g b");
    Ok(())
}

#[test]
fn a_step_carries_its_own_term_substitution() -> Result<()> {
    let mut f = Fixture::new()?;
    // fx: ⊢ f v = v, instantiated at v ↦ a, applied to `f a`.
    let v = f.k.term_var("v", f.bool_ty)?;
    let fa = f.k.term_comb(f.f, f.a)?;
    let step = Step::new(vec![], "fx").with_terms(BTreeMap::from([(v, f.a)]));
    let cert = Certificate::new(fa, vec![step], f.a, true);
    assert_eq!(f.prove(&cert)?, "⊢ f a = a");
    Ok(())
}

// --- the certificate does not hold up --------------------------------------

#[test]
fn a_lie_about_the_result_is_refused() -> Result<()> {
    let mut f = Fixture::new()?;
    // The rule gives b; the certificate claims c.
    let cert = Certificate::new(f.a, vec![Step::new(vec![], "ab")], f.c, true);
    let err = f.prove(&cert).unwrap_err().to_string();
    assert!(err.contains("the certificate claims c"), "{err}");
    assert!(err.contains("but the rules give b"), "{err}");
    Ok(())
}

#[test]
fn a_lie_about_the_position_is_refused() -> Result<()> {
    let mut f = Fixture::new()?;
    // `ab` rewrites `a`, but the path points at `f`.
    let fa = f.k.term_comb(f.f, f.a)?;
    let fb = f.k.term_comb(f.f, f.b)?;
    let cert = Certificate::new(fa, vec![Step::new(vec![PathStep::Rator], "ab")], fb, true);
    let err = f.prove(&cert).unwrap_err().to_string();
    assert!(err.contains("ab instantiates to a"), "{err}");
    assert!(err.contains("rator holds f"), "{err}");
    Ok(())
}

#[test]
fn a_position_that_does_not_exist_is_refused() -> Result<()> {
    let mut f = Fixture::new()?;
    // `a` is a constant; it has no rand.
    let cert = Certificate::new(f.a, vec![Step::new(vec![PathStep::Rand], "ab")], f.b, true);
    let err = f.prove(&cert).unwrap_err().to_string();
    assert!(err.contains("takes rand of a, which has no rand"), "{err}");
    Ok(())
}

#[test]
fn an_unknown_rule_is_refused() -> Result<()> {
    let mut f = Fixture::new()?;
    let cert = Certificate::new(f.a, vec![Step::new(vec![], "nonesuch")], f.b, true);
    let err = f.prove(&cert).unwrap_err().to_string();
    assert!(err.contains("no such rule: nonesuch"), "{err}");
    Ok(())
}

#[test]
fn a_wrong_substitution_is_refused() -> Result<()> {
    let mut f = Fixture::new()?;
    // fx at v ↦ b instantiates to `f b = b`, but the position holds `f a`.
    let v = f.k.term_var("v", f.bool_ty)?;
    let fa = f.k.term_comb(f.f, f.a)?;
    let step = Step::new(vec![], "fx").with_terms(BTreeMap::from([(v, f.b)]));
    let cert = Certificate::new(fa, vec![step], f.a, true);
    let err = f.prove(&cert).unwrap_err().to_string();
    assert!(err.contains("fx instantiates to f b"), "{err}");
    Ok(())
}

#[test]
fn a_certificate_cannot_smuggle_a_step_past_the_chain() -> Result<()> {
    let mut f = Fixture::new()?;
    // Two steps that are individually fine, but the second starts from a term
    // the first did not produce: after `a → b`, there is no `f` to rewrite.
    let cert = Certificate::new(
        f.a,
        vec![
            Step::new(vec![], "ab"),
            Step::new(vec![PathStep::Rator], "fg"),
        ],
        f.b,
        true,
    );
    // The refusal comes from the path, not from a vague failure: after `a → b`
    // the term is the constant `b`, which has no rator to take.
    let err = f.prove(&cert).unwrap_err().to_string();
    assert!(
        err.contains("takes rator of b, which has no rator"),
        "{err}"
    );
    Ok(())
}

// --- conditions ------------------------------------------------------------

#[test]
fn an_assumed_condition_survives_as_a_hypothesis() -> Result<()> {
    let mut f = Fixture::new()?;
    // `cond` is `c ⊢ a = b`. Left assumed, the hypothesis rides along.
    let step = Step::new(vec![], "cond").with_conditions(vec![Condition::Assumed]);
    let cert = Certificate::new(f.a, vec![step], f.b, true);
    assert_eq!(f.prove(&cert)?, "c ⊢ a = b");
    Ok(())
}

#[test]
fn a_discharged_condition_leaves_no_hypothesis() -> Result<()> {
    let mut f = Fixture::new()?;
    // The nested certificate proves `c = T`, so `c` is discharged and the
    // theorem comes out unconditional.
    let proof_of_c = Certificate::new(f.c, vec![Step::new(vec![], "ct")], f.truth, true);
    let step = Step::new(vec![], "cond").with_conditions(vec![Condition::Discharged(proof_of_c)]);
    let cert = Certificate::new(f.a, vec![step], f.b, true);
    assert_eq!(f.prove(&cert)?, "⊢ a = b");
    Ok(())
}

#[test]
fn a_condition_certificate_for_the_wrong_hypothesis_is_refused() -> Result<()> {
    let mut f = Fixture::new()?;
    // The certificate proves something about `a`, not about the hypothesis `c`.
    let wrong = Certificate::new(f.a, vec![Step::new(vec![], "ab")], f.b, true);
    let step = Step::new(vec![], "cond").with_conditions(vec![Condition::Discharged(wrong)]);
    let cert = Certificate::new(f.a, vec![step], f.b, true);
    let err = f.prove(&cert).unwrap_err().to_string();
    assert!(
        err.contains("condition certificate is for a, not c"),
        "{err}"
    );
    Ok(())
}

#[test]
fn a_condition_certificate_that_does_not_reach_t_is_refused() -> Result<()> {
    let mut f = Fixture::new()?;
    // Proves `c = c`, which is true and useless: it does not reach T.
    let useless = Certificate::new(f.c, vec![], f.c, true);
    let step = Step::new(vec![], "cond").with_conditions(vec![Condition::Discharged(useless)]);
    let cert = Certificate::new(f.a, vec![step], f.b, true);
    let err = f.prove(&cert).unwrap_err().to_string();
    assert!(err.contains("condition certificate proves"), "{err}");
    Ok(())
}

#[test]
fn the_wrong_number_of_conditions_is_refused() -> Result<()> {
    let mut f = Fixture::new()?;
    // `cond` has one hypothesis; the step offers none.
    let cert = Certificate::new(f.a, vec![Step::new(vec![], "cond")], f.b, true);
    let err = f.prove(&cert).unwrap_err().to_string();
    assert!(
        err.contains("0 condition certificates for 1 hypotheses"),
        "{err}"
    );
    Ok(())
}

// --- paths -----------------------------------------------------------------

#[test]
fn a_position_under_a_binder_is_opened_by_position_not_by_name() -> Result<()> {
    let mut f = Fixture::new()?;
    // Whatever the binder is displayed as, the opener is `_0`: a certificate
    // must mean the same thing in the process that replays it.
    let z = f.k.term_var("zebra", f.bool_ty)?;
    let lam = f.k.term_abs(z, z)?;
    let opened = f.k.subterm(lam, &[PathStep::Body])?;
    assert_eq!(f.k.term_to_string(opened), "_0");
    Ok(())
}

#[test]
fn replace_rebuilds_under_the_binders_own_display_name() -> Result<()> {
    let mut f = Fixture::new()?;
    let x = f.k.term_var("x", f.bool_ty)?;
    let lam = f.k.term_abs(x, f.a)?; // λx. a
    let replaced = f.k.replace(lam, &[PathStep::Body], f.b)?;
    assert_eq!(f.k.term_to_string(replaced), "λx. b");
    Ok(())
}

#[test]
fn every_position_is_enumerated_outermost_first() -> Result<()> {
    let mut f = Fixture::new()?;
    let fa = f.k.term_comb(f.f, f.a)?;
    let found = f.k.positions(fa)?;
    let rendered: Vec<String> = found
        .iter()
        .map(|(path, t)| {
            format!(
                "{} = {}",
                adamas::path_to_string(path),
                f.k.term_to_string(*t)
            )
        })
        .collect();
    assert_eq!(
        rendered,
        vec!["the whole term = f a", "rator = f", "rand = a"]
    );
    Ok(())
}

// --- the untrusted layer really is untrusted -------------------------------

#[test]
fn replay_reaches_the_kernel_only_through_the_ten_rules() -> Result<()> {
    // Not an assertion but a demonstration: this file is outside `kernel`, and
    // the `compile_fail` doctests on `Thm` show what that costs an attacker.
    // What it buys is that `prove_certificate` — which trusts nothing it is
    // handed — cannot manufacture a theorem even by accident.
    let mut f = Fixture::new()?;
    let cert = Certificate::new(f.a, vec![Step::new(vec![], "ab")], f.b, true);
    let thm = f.k.prove_certificate(f.th, &cert, &f.rules)?;
    assert_eq!(thm.theory(), f.th);
    assert!(thm.hyps().is_empty());
    Ok(())
}
