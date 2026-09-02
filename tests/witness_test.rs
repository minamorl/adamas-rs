use adamas::conversion;
use adamas::witness::{Steps, Theorem};
use adamas::{Kernel, PathStep, Result, RuleSet, Term, TheoryId};

fn conditional_refl_rules(
    k: &mut Kernel,
    th: TheoryId,
    base: &RuleSet,
    proposition: Term,
) -> Result<RuleSet> {
    let subject = k.term_eq(proposition, proposition)?;
    let rule = base.fetch("refl")?.clone();
    let matched = k
        .match_pattern(rule.lhs, subject, &rule.variables)
        .expect("refl matches");
    let mut theorem = k.inst_type(th, &matched.type_subst, &rule.thm)?;
    if !matched.term_subst.is_empty() {
        let mut theta = std::collections::BTreeMap::new();
        for (var, value) in &matched.term_subst {
            theta.insert(k.inst_type_term(&matched.type_subst, *var)?, *value);
        }
        theorem = k.inst(th, &theta, &theorem)?;
    }
    let assumed = k.assume(th, proposition)?;
    let conditional = k.prove_hyp(th, &assumed, &theorem)?;
    let mut rules = RuleSet::new();
    rules.add(k, "conditional_refl", conditional)?;
    Ok(rules)
}

#[test]
fn theorem_and_steps_witnesses_agree_and_replay() -> Result<()> {
    let mut k = Kernel::new();
    let th = k.new_theory("witness agreement");
    let logic = k.install_logic(th)?;
    let q = k.term_var("q", k.bool_ty())?;
    let subject = k.term_eq(q, q)?;
    let conv = conversion::rewr(&logic.rules, "refl");

    let theorem = conv.prove(&mut k, th, subject)?;
    let certificate = conv.certify(&mut k, subject)?;
    let replayed = k.prove_certificate(th, &certificate, &logic.rules)?;
    assert_eq!(theorem.concl(), replayed.concl());
    assert_eq!(certificate.result, logic.true_const);
    Ok(())
}

#[test]
fn steps_prefix_paths_and_preserve_binder_shape() -> Result<()> {
    let mut k = Kernel::new();
    let th = k.new_theory("witness traversal");
    let logic = k.install_logic(th)?;
    let a = k.ty_var("A")?;
    let x = k.term_var("x", a)?;
    let body = k.term_eq(x, x)?;
    let abstraction = k.term_abs_named("chosen", x, body)?;
    let conv = conversion::first_redex(conversion::rewrites(&logic.rules));
    let witness = conv
        .call(&mut k, &Steps::new(), abstraction, 0)?
        .expect("body rewrites");

    assert_eq!(witness.steps[0].path, vec![PathStep::Body]);
    let expected = k.term_abs_named("chosen", x, logic.true_const)?;
    assert_eq!(witness.result, expected);
    Ok(())
}

#[test]
fn builders_are_public_witness_algebras() -> Result<()> {
    let mut k = Kernel::new();
    let th = k.new_theory("witness builders");
    let q = k.term_var("q", k.bool_ty())?;
    let conv = conversion::all_conv();

    let steps = conv
        .call(&mut k, &Steps::new(), q, 0)?
        .expect("steps witness");
    assert!(steps.thm.is_none());
    let theorem = conv
        .call(&mut k, &Theorem::new(th), q, 0)?
        .expect("theorem witness");
    assert_eq!(
        theorem.thm.as_ref().expect("theorem").concl(),
        k.term_eq(q, q)?
    );
    Ok(())
}

#[test]
fn sub_is_reflexive_on_a_leaf() -> Result<()> {
    let mut k = Kernel::new();
    let th = k.new_theory("sub leaf");
    let logic = k.install_logic(th)?;
    let q: Term = k.term_var("q", k.bool_ty())?;
    let witness = conversion::sub(conversion::rewrites(&logic.rules))
        .call(&mut k, &Steps::new(), q, 0)?
        .expect("SUB_CONV is total");
    assert_eq!(witness.result, q);
    assert!(witness.steps.is_empty());
    Ok(())
}

#[test]
fn abs_conv_allows_only_hypotheses_free_of_the_opened_binder() -> Result<()> {
    let mut k = Kernel::new();
    let th = k.new_theory("abs hypotheses");
    let logic = k.install_logic(th)?;
    let q = k.term_var("q", k.bool_ty())?;
    let z = k.term_var("z", k.bool_ty())?;
    let rules = conditional_refl_rules(&mut k, th, &logic.rules, q)?;
    let qq = k.term_eq(q, q)?;
    let safe = k.term_abs(z, qq)?;
    let theorem = conversion::abs_conv(conversion::rewr(&rules, "conditional_refl"))
        .prove(&mut k, th, safe)?;
    assert_eq!(theorem.hyps(), &[q]);

    let blocked = k.term_abs(q, qq)?;
    let error = conversion::abs_conv(conversion::rewr(&rules, "conditional_refl"))
        .prove(&mut k, th, blocked)
        .unwrap_err();
    assert!(error.to_string().contains("free in"), "{error}");
    Ok(())
}

#[test]
fn first_redex_refuses_any_theorem_hypothesis_under_a_binder() -> Result<()> {
    let mut k = Kernel::new();
    let th = k.new_theory("first redex hypotheses");
    let logic = k.install_logic(th)?;
    let q = k.term_var("q", k.bool_ty())?;
    let z = k.term_var("z", k.bool_ty())?;
    let rules = conditional_refl_rules(&mut k, th, &logic.rules, q)?;
    let qq = k.term_eq(q, q)?;
    let abstraction = k.term_abs(z, qq)?;
    let error = conversion::first_redex(conversion::rewr(&rules, "conditional_refl"))
        .prove(&mut k, th, abstraction)
        .unwrap_err();
    assert!(
        error
            .to_string()
            .contains("cannot abstract a conversion with hypotheses"),
        "{error}"
    );
    Ok(())
}
