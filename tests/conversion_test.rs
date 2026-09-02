use adamas::conversion::{self, Conv, RepeatReason};
use adamas::witness::{Steps, Witness};
use adamas::{Condition, Error, Kernel, Ordering, PathStep, Result, RuleSet, Term, TheoryId};

struct Fixture {
    k: Kernel,
    th: TheoryId,
    rules: RuleSet,
    truth: Term,
    q: Term,
    r: Term,
}

impl Fixture {
    fn new() -> Result<Self> {
        let mut k = Kernel::new();
        let th = k.new_theory("conversion");
        let logic = k.install_logic(th)?;
        let truth = logic.true_const;
        let q = k.term_var("q", k.bool_ty())?;
        let r = k.term_var("r", k.bool_ty())?;
        Ok(Self {
            k,
            th,
            rules: logic.rules,
            truth,
            q,
            r,
        })
    }

    fn target(&mut self) -> Result<Term> {
        let left = self.k.term_eq(self.q, self.q)?;
        let right = self.k.term_eq(self.r, self.r)?;
        self.k.term_eq(left, right)
    }

    fn leaf(&self) -> Conv {
        conversion::rewrites(&self.rules)
    }
}

fn summary(witness: &Witness) -> Vec<(Vec<PathStep>, &str)> {
    witness
        .steps
        .iter()
        .map(|step| (step.path.clone(), step.rule.as_str()))
        .collect()
}

#[test]
fn all_and_no_conv_are_success_and_failure_values() -> Result<()> {
    let mut fx = Fixture::new()?;
    let all = conversion::all_conv()
        .call(&mut fx.k, &Steps::new(), fx.q, 3)?
        .expect("ALL_CONV succeeds");
    assert_eq!(all.result, fx.q);
    assert!(all.steps.is_empty());
    assert!(conversion::no_conv()
        .call(&mut fx.k, &Steps::new(), fx.q, 0)?
        .is_none());
    Ok(())
}

#[test]
fn then_c_runs_on_the_first_result_and_or_else_only_handles_failure() -> Result<()> {
    let mut fx = Fixture::new()?;
    let subject = fx.k.term_eq(fx.q, fx.q)?;
    let subject_eq_t = fx.k.term_eq(subject, fx.truth)?;
    let conv =
        conversion::rewr(&fx.rules, "true_right").then_c(conversion::rewr(&fx.rules, "refl"));
    let witness = conv
        .call(&mut fx.k, &Steps::new(), subject_eq_t, 0)?
        .expect("both rules apply");
    assert_eq!(
        summary(&witness),
        vec![(vec![], "true_right"), (vec![], "refl")]
    );
    assert_eq!(witness.result, fx.truth);

    let erroring = Conv::new(|_, _, _, _| Err(Error::Rule("conversion exploded".into())));
    let err = erroring
        .or_else(conversion::all_conv())
        .call(&mut fx.k, &Steps::new(), fx.q, 0)
        .unwrap_err();
    assert_eq!(err, Error::Rule("conversion exploded".into()));

    let missing = conversion::rewr(&fx.rules, "not_registered")
        .or_else(conversion::all_conv())
        .call(&mut fx.k, &Steps::new(), fx.q, 0)
        .unwrap_err();
    assert!(matches!(missing, Error::RuleSet(_)));
    Ok(())
}

#[test]
fn repeat_distinguishes_nil_from_budget_and_burns_reflexive_successes() -> Result<()> {
    let mut fx = Fixture::new()?;
    let subject = fx.k.term_eq(fx.q, fx.q)?;
    let one = conversion::repeat(conversion::rewr(&fx.rules, "refl"), 3).run(
        &mut fx.k,
        &Steps::new(),
        subject,
        0,
    )?;
    assert_eq!(one.reason, RepeatReason::Nil);
    assert_eq!(one.witness.steps.len(), 1);

    let reflexive = Conv::new(|kernel, build, term, _| Ok(Some(build.refl(kernel, term)?)));
    let exhausted = conversion::repeat(reflexive, 3).run(&mut fx.k, &Steps::new(), fx.q, 0)?;
    assert_eq!(exhausted.reason, RepeatReason::Limit);
    assert!(exhausted.witness.steps.is_empty());

    let zero =
        conversion::repeat(conversion::no_conv(), 0).run(&mut fx.k, &Steps::new(), fx.q, 0)?;
    assert_eq!(zero.reason, RepeatReason::Limit);
    assert_eq!(zero.witness.result, fx.q);
    Ok(())
}

#[test]
fn repeat_is_itself_a_composable_conversion_value() -> Result<()> {
    let mut fx = Fixture::new()?;
    let subject = fx.k.term_eq(fx.q, fx.q)?;
    let repeated = conversion::repeat(conversion::rewr(&fx.rules, "refl"), 3);
    let certificate = repeated.certify(&mut fx.k, subject)?;
    assert_eq!(certificate.result, fx.truth);
    assert!(certificate.complete);

    let composed = repeated.then_c(conversion::all_conv());
    let witness = composed
        .call(&mut fx.k, &Steps::new(), subject, 0)?
        .expect("repeat is a conversion");
    assert_eq!(witness.result, fx.truth);
    Ok(())
}

#[test]
fn once_depth_is_per_branch_but_first_redex_is_one_position_total() -> Result<()> {
    let mut fx = Fixture::new()?;
    let target = fx.target()?;
    let once = conversion::once_depth(fx.leaf())
        .call(&mut fx.k, &Steps::new(), target, 0)?
        .expect("descendants match");
    assert_eq!(
        summary(&once),
        vec![
            (vec![PathStep::Rator, PathStep::Rand], "refl"),
            (vec![PathStep::Rand], "refl")
        ]
    );

    let first = conversion::first_redex(fx.leaf())
        .call(&mut fx.k, &Steps::new(), target, 0)?
        .expect("a descendant matches");
    assert_eq!(
        summary(&first),
        vec![(vec![PathStep::Rator, PathStep::Rand], "refl")]
    );
    assert!(conversion::first_redex(fx.leaf())
        .call(&mut fx.k, &Steps::new(), fx.q, 0)?
        .is_none());
    Ok(())
}

#[test]
fn comb_and_abs_conversions_fail_on_the_wrong_term_shape() -> Result<()> {
    let mut fx = Fixture::new()?;
    assert!(conversion::comb_conv(fx.leaf())
        .call(&mut fx.k, &Steps::new(), fx.q, 0)?
        .is_none());
    assert!(conversion::abs_conv(fx.leaf())
        .call(&mut fx.k, &Steps::new(), fx.q, 0)?
        .is_none());
    Ok(())
}

#[test]
fn top_down_rewrites_a_parent_before_its_children() -> Result<()> {
    let mut fx = Fixture::new()?;
    let qq = fx.k.term_eq(fx.q, fx.q)?;
    let subject = fx.k.term_eq(qq, fx.truth)?;
    let certificate = conversion::top_down(fx.leaf(), 10).certify(&mut fx.k, subject)?;
    assert_eq!(
        certificate
            .steps
            .iter()
            .map(|step| step.rule.as_str())
            .collect::<Vec<_>>(),
        vec!["true_right", "refl"]
    );
    assert_eq!(certificate.result, fx.truth);
    Ok(())
}

#[test]
fn depth_spends_its_repeat_budget_even_on_reflexivity() -> Result<()> {
    use std::cell::Cell;
    use std::rc::Rc;

    let mut fx = Fixture::new()?;
    let calls = Rc::new(Cell::new(0usize));
    let observed = calls.clone();
    let reflexive = Conv::new(move |kernel, build, term, _| {
        observed.set(observed.get() + 1);
        Ok(Some(build.refl(kernel, term)?))
    });
    let witness = conversion::depth(reflexive, 3)
        .call(&mut fx.k, &Steps::new(), fx.q, 0)?
        .expect("DEPTH_CONV is total");
    assert_eq!(calls.get(), 3);
    assert!(witness.steps.is_empty());
    Ok(())
}

#[test]
fn no_conv_certifies_empty_complete_reflexivity() -> Result<()> {
    let mut fx = Fixture::new()?;
    let certificate = conversion::no_conv().certify(&mut fx.k, fx.q)?;
    assert_eq!(certificate.term, fx.q);
    assert_eq!(certificate.result, fx.q);
    assert!(certificate.steps.is_empty());
    assert!(certificate.complete);
    Ok(())
}

#[test]
fn depth_redepth_and_top_down_replay_their_certificates() -> Result<()> {
    let mut fx = Fixture::new()?;
    let target = fx.target()?;
    let strategies = [
        conversion::depth(fx.leaf(), 10),
        conversion::redepth(fx.leaf()),
        conversion::repeat(conversion::top_down(fx.leaf(), 10), 10).as_conv(),
    ];
    for strategy in strategies {
        let certificate = strategy.certify(&mut fx.k, target)?;
        let theorem = fx.k.prove_certificate(fx.th, &certificate, &fx.rules)?;
        assert_eq!(certificate.result, fx.truth);
        assert_eq!(theorem.concl(), fx.k.term_eq(target, fx.truth)?);
    }
    Ok(())
}

#[test]
fn strategy_injection_keeps_first_redex_as_the_default() -> Result<()> {
    let mut fx = Fixture::new()?;
    let target = fx.target()?;
    let implicit = fx.k.rewrite(target, &fx.rules, 1, Ordering::Unordered)?;
    let explicit = fx.k.rewrite_with_strategy(
        target,
        &fx.rules,
        1,
        Ordering::Unordered,
        conversion::first_redex,
    )?;
    assert_eq!(implicit, explicit);

    let branchwise = fx.k.rewrite_with_strategy(
        target,
        &fx.rules,
        1,
        Ordering::Unordered,
        conversion::once_depth,
    )?;
    assert_ne!(implicit.steps, branchwise.steps);
    assert_eq!(branchwise.steps.len(), 2);
    Ok(())
}

#[test]
fn rewrites_ordering_only_guards_permutative_rules() -> Result<()> {
    let mut k = Kernel::new();
    let th = k.new_theory("ordered nonpermutative");
    let bool_ty = k.bool_ty();
    let fun_ty = k.ty_fun(bool_ty, bool_ty)?;
    let a = k.new_constant(th, "a", bool_ty)?;
    let f = k.new_constant(th, "f", fun_ty)?;
    let fa = k.term_comb(f, a)?;
    let equation = k.term_eq(a, fa)?;
    let assumed = k.assume(th, equation)?;
    let mut rules = RuleSet::new();
    rules.add(&k, "grow", assumed)?;

    assert!(!k.is_permutative(rules.fetch("grow")?));
    let set_witness =
        conversion::rewrites_with(&rules, None, true).call(&mut k, &Steps::new(), a, 0)?;
    assert!(
        set_witness.is_some(),
        "nonpermutative rules are not guarded"
    );
    let named_witness =
        conversion::ordered_rewr(&rules, "grow").call(&mut k, &Steps::new(), a, 0)?;
    assert!(
        named_witness.is_none(),
        "ORDERED_REWR_CONV guards every match"
    );
    Ok(())
}

#[test]
fn conditional_rewrite_records_discharged_or_assumed() -> Result<()> {
    let mut fx = Fixture::new()?;
    let p = fx.k.term_var("p", fx.k.bool_ty())?;
    let pp = fx.k.term_eq(p, p)?;
    let refl = fx.rules.fetch("refl")?.clone();
    let matched =
        fx.k.match_pattern(refl.lhs, pp, &refl.variables)
            .expect("refl matches");
    let mut theorem = fx.k.inst_type(fx.th, &matched.type_subst, &refl.thm)?;
    if !matched.term_subst.is_empty() {
        let mut theta = std::collections::BTreeMap::new();
        for (var, value) in &matched.term_subst {
            theta.insert(fx.k.inst_type_term(&matched.type_subst, *var)?, *value);
        }
        theorem = fx.k.inst(fx.th, &theta, &theorem)?;
    }
    let assumed_p = fx.k.assume(fx.th, p)?;
    let conditional = fx.k.prove_hyp(fx.th, &assumed_p, &theorem)?;
    let mut rules = RuleSet::new();
    rules.add(&fx.k, "conditional_refl", conditional)?;
    let conv =
        conversion::rewr_with_conditions(&rules, "conditional_refl", Some(conversion::all_conv()));

    let tt = fx.k.term_eq(fx.truth, fx.truth)?;
    let discharged = conv.certify(&mut fx.k, tt)?;
    assert!(matches!(
        discharged.steps[0].conditions.as_slice(),
        [Condition::Discharged(_)]
    ));
    let proved = conv.prove(&mut fx.k, fx.th, tt)?;
    assert!(proved.hyps().is_empty());

    let qq = fx.k.term_eq(fx.q, fx.q)?;
    let assumed = conv.certify(&mut fx.k, qq)?;
    assert_eq!(assumed.steps[0].conditions, vec![Condition::Assumed]);
    let proved = conv.prove(&mut fx.k, fx.th, qq)?;
    assert_eq!(proved.hyps(), &[fx.q]);
    Ok(())
}

#[test]
fn malicious_steps_conversion_cannot_produce_a_false_theorem() -> Result<()> {
    let mut fx = Fixture::new()?;
    let subject = fx.k.term_eq(fx.q, fx.q)?;
    let malicious =
        Conv::new(move |_, _, term, _| Ok(Some(Witness::steps(term, Vec::new(), fx.r))));
    let certificate = malicious.certify(&mut fx.k, subject)?;
    let error =
        fx.k.prove_certificate(fx.th, &certificate, &fx.rules)
            .unwrap_err();
    assert!(matches!(error, Error::Certificate(_)));
    Ok(())
}
