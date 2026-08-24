//! The rewriter: the untrusted half that *produces* certificates.
//!
//! The load-bearing assertion in this file is not "the rewriter got the right
//! answer" — it is that **every certificate it emits is accepted by replay**.
//! A rewriter that is merely wrong produces a certificate replay refuses; a
//! rewriter that is wrong *and* whose output replay accepts would mean the
//! kernel had a hole. So each test below rewrites and then proves.

use adamas::{Certificate, Kernel, Ordering, PathStep, Result, RuleSet, Term, TheoryId, Ty};

/// Peano-shaped arithmetic: `z`, `s`, `add`, and the two defining equations.
struct Fixture {
    k: Kernel,
    th: TheoryId,
    rules: RuleSet,
    num: Ty,
    z: Term,
    s: Term,
    add: Term,
}

impl Fixture {
    fn new(with_commutativity: bool) -> Result<Self> {
        let mut k = Kernel::new();
        let th = k.new_theory("arith");
        k.new_type("num", 0)?;
        let num = k.ty_con("num", &[])?;
        let num_num = k.ty_fun(num, num)?;
        let binop = k.ty_fun(num, num_num)?;

        let z = k.new_constant(th, "z", num)?;
        let s = k.new_constant(th, "s", num_num)?;
        let add = k.new_constant(th, "add", binop)?;

        let m = k.term_var("m", num)?;
        let n = k.term_var("n", num)?;

        let mut rules = RuleSet::new();

        if with_commutativity {
            // add m n = add n m — permutative, and a loop without ordering.
            let am = k.term_comb(add, m)?;
            let amn = k.term_comb(am, n)?;
            let an = k.term_comb(add, n)?;
            let anm = k.term_comb(an, m)?;
            let eq = k.term_eq(amn, anm)?;
            let thm = k.new_axiom(th, eq)?;
            rules.add(&k, "add_comm", thm)?;
        }

        // add z n = n
        let az = k.term_comb(add, z)?;
        let azn = k.term_comb(az, n)?;
        let eq = k.term_eq(azn, n)?;
        let thm = k.new_axiom(th, eq)?;
        rules.add(&k, "add_z", thm)?;

        // add (s m) n = s (add m n)
        let sm = k.term_comb(s, m)?;
        let asm = k.term_comb(add, sm)?;
        let asmn = k.term_comb(asm, n)?;
        let am = k.term_comb(add, m)?;
        let amn = k.term_comb(am, n)?;
        let s_amn = k.term_comb(s, amn)?;
        let eq = k.term_eq(asmn, s_amn)?;
        let thm = k.new_axiom(th, eq)?;
        rules.add(&k, "add_s", thm)?;

        Ok(Fixture {
            k,
            th,
            rules,
            num,
            z,
            s,
            add,
        })
    }

    fn add_of(&mut self, left: Term, right: Term) -> Result<Term> {
        let partial = self.k.term_comb(self.add, left)?;
        self.k.term_comb(partial, right)
    }

    fn succ(&mut self, of: Term) -> Result<Term> {
        self.k.term_comb(self.s, of)
    }

    /// Rewrite, then **prove the certificate**. Returns the printed theorem and
    /// the certificate, so a test can check both what was claimed and that the
    /// kernel accepted it.
    fn rewrite_and_prove(
        &mut self,
        term: Term,
        limit: usize,
        ordering: Ordering,
    ) -> Result<(Certificate, String)> {
        let cert = self.k.rewrite(term, &self.rules, limit, ordering)?;
        let thm = self.k.prove_certificate(self.th, &cert, &self.rules)?;
        let rendered = self.k.thm_to_string(&thm);
        Ok((cert, rendered))
    }
}

// --- rewriting, and the certificate holding up -----------------------------

#[test]
fn a_term_with_nothing_to_do_certifies_reflexivity() -> Result<()> {
    let mut f = Fixture::new(false)?;
    let (cert, thm) = f.rewrite_and_prove(f.z, adamas::DEFAULT_LIMIT, Ordering::Unordered)?;
    assert!(cert.is_empty());
    assert!(cert.complete);
    assert_eq!(thm, "⊢ z = z");
    Ok(())
}

#[test]
fn one_plus_zero_reduces_and_the_certificate_replays() -> Result<()> {
    let mut f = Fixture::new(false)?;
    let sz = f.succ(f.z)?;
    let term = f.add_of(sz, f.z)?;
    let (cert, thm) = f.rewrite_and_prove(term, adamas::DEFAULT_LIMIT, Ordering::Unordered)?;

    assert_eq!(f.k.term_to_string(cert.result), "s z");
    assert!(cert.complete, "nothing else applied");
    // add_s at the root, then add_z under the successor.
    let taken: Vec<String> = cert.steps.iter().map(|s| s.describe()).collect();
    assert_eq!(taken, vec!["the whole term: add_s", "rand: add_z"]);
    assert_eq!(thm, "⊢ add (s z) z = s z");
    Ok(())
}

#[test]
fn two_plus_two_reduces_and_the_certificate_replays() -> Result<()> {
    let mut f = Fixture::new(false)?;
    let sz = f.succ(f.z)?;
    let ssz = f.succ(sz)?;
    let term = f.add_of(ssz, ssz)?;
    let (cert, thm) = f.rewrite_and_prove(term, adamas::DEFAULT_LIMIT, Ordering::Unordered)?;
    assert_eq!(f.k.term_to_string(cert.result), "s (s (s (s z)))");
    assert!(cert.complete);
    assert_eq!(thm, "⊢ add (s (s z)) (s (s z)) = s (s (s (s z)))");
    Ok(())
}

#[test]
fn a_redex_under_a_binder_is_found_and_replays() -> Result<()> {
    let mut f = Fixture::new(false)?;
    let x = f.k.term_var("x", f.num)?;
    let inner = f.add_of(f.z, x)?; // add z x
    let lam = f.k.term_abs(x, inner)?; // λx. add z x
    let (cert, thm) = f.rewrite_and_prove(lam, adamas::DEFAULT_LIMIT, Ordering::Unordered)?;

    let taken: Vec<String> = cert.steps.iter().map(|s| s.describe()).collect();
    assert_eq!(taken, vec!["body: add_z"]);
    assert_eq!(thm, "⊢ (λx. add z «0») = (λx. «0»)");
    Ok(())
}

#[test]
fn the_traversal_is_leftmost_outermost() -> Result<()> {
    let mut f = Fixture::new(false)?;
    // add (add z z) (add z z): the outer `add` has no rule, so the leftmost
    // inner one goes first — under `rator.rand`, not under `rand`.
    let inner = f.add_of(f.z, f.z)?;
    let term = f.add_of(inner, inner)?;
    let cert = f.k.rewrite(term, &f.rules, 1, Ordering::Unordered)?;
    let taken: Vec<String> = cert.steps.iter().map(|s| s.describe()).collect();
    assert_eq!(taken, vec!["rator.rand: add_z"]);
    // Even a budget-truncated certificate has to replay.
    let thm = f.k.prove_certificate(f.th, &cert, &f.rules)?;
    assert_eq!(
        f.k.thm_to_string(&thm),
        "⊢ add (add z z) (add z z) = add z (add z z)"
    );
    Ok(())
}

// --- the budget ------------------------------------------------------------

#[test]
fn a_zero_budget_reports_that_it_gave_up() -> Result<()> {
    let mut f = Fixture::new(false)?;
    let sz = f.succ(f.z)?;
    let term = f.add_of(sz, f.z)?;
    let (cert, thm) = f.rewrite_and_prove(term, 0, Ordering::Unordered)?;
    assert!(cert.is_empty());
    assert!(
        !cert.complete,
        "complete is 'nothing else applied', not 'untouched'"
    );
    assert_eq!(thm, "⊢ add (s z) z = add (s z) z");
    Ok(())
}

#[test]
fn a_truncated_certificate_is_still_a_true_one() -> Result<()> {
    let mut f = Fixture::new(false)?;
    let sz = f.succ(f.z)?;
    let ssz = f.succ(sz)?;
    let term = f.add_of(ssz, ssz)?;
    let (cert, thm) = f.rewrite_and_prove(term, 1, Ordering::Unordered)?;
    assert_eq!(cert.len(), 1);
    assert!(!cert.complete);
    assert_eq!(thm, "⊢ add (s (s z)) (s (s z)) = s (add (s z) (s (s z)))");
    Ok(())
}

// --- permutative rules -----------------------------------------------------

#[test]
fn commutativity_is_recognised_as_permutative() -> Result<()> {
    let f = Fixture::new(true)?;
    let comm = f.rules.fetch("add_comm")?;
    let add_z = f.rules.fetch("add_z")?;
    assert!(f.k.is_permutative(comm));
    assert!(!f.k.is_permutative(add_z));
    Ok(())
}

#[test]
fn commutativity_unordered_runs_to_the_budget() -> Result<()> {
    let mut f = Fixture::new(true)?;
    let sz = f.succ(f.z)?;
    let term = f.add_of(f.z, sz)?;
    let (cert, _) = f.rewrite_and_prove(term, 12, Ordering::Unordered)?;
    assert_eq!(cert.len(), 12);
    assert!(!cert.complete, "it swaps forever and never settles");
    Ok(())
}

#[test]
fn commutativity_ordered_settles() -> Result<()> {
    let mut f = Fixture::new(true)?;
    let sz = f.succ(f.z)?;
    let term = f.add_of(f.z, sz)?;
    let (cert, thm) = f.rewrite_and_prove(term, adamas::DEFAULT_LIMIT, Ordering::Ordered)?;
    assert!(
        cert.complete,
        "ordered, a permutative rule may only shrink the term, so it stops"
    );
    assert_eq!(thm, "⊢ add z (s z) = s z");
    Ok(())
}

#[test]
fn the_term_order_reads_structure_not_the_intern_table() -> Result<()> {
    // `Term` derives `Ord` over its rank, which is an intern-table insertion
    // counter. Using it for the term order would make the same two terms
    // compare differently in two processes, and a certificate written by one
    // rewriter would stop replaying in another.
    //
    // So: build the *same* comparison in two kernels whose intern order puts
    // the two constants the opposite way round, and require the same verdict.
    // Under a rank-based order these two lines disagree.
    let verdict = |z_first: bool| -> Result<(bool, bool)> {
        let mut k = Kernel::new();
        let th = k.new_theory("t");
        k.new_type("num", 0)?;
        let num = k.ty_con("num", &[])?;
        let (z, w) = if z_first {
            let z = k.new_constant(th, "z", num)?;
            let w = k.new_constant(th, "w", num)?;
            (z, w)
        } else {
            let w = k.new_constant(th, "w", num)?;
            let z = k.new_constant(th, "z", num)?;
            (z, w)
        };
        // The rank order really is opposite between the two runs...
        let rank_says = z < w;
        Ok((k.term_greater(z, w), rank_says))
    };
    let (structural_a, rank_a) = verdict(true)?;
    let (structural_b, rank_b) = verdict(false)?;

    assert_ne!(
        rank_a, rank_b,
        "the two runs must disagree on rank, or this proves nothing"
    );
    assert_eq!(
        structural_a, structural_b,
        "the term order must not depend on intern order"
    );
    assert!(structural_a, "z > w by name, in both processes");
    Ok(())
}

// --- registration ----------------------------------------------------------

#[test]
fn a_bare_variable_on_the_left_is_refused() -> Result<()> {
    let mut f = Fixture::new(false)?;
    let n = f.k.term_var("n", f.num)?;
    let eq = f.k.term_eq(n, f.z)?;
    let thm = f.k.new_axiom(f.th, eq)?;
    let err = f.rules.add(&f.k, "bad", thm).unwrap_err().to_string();
    assert!(err.contains("the left side is a bare variable"), "{err}");
    Ok(())
}

#[test]
fn a_right_side_the_left_cannot_determine_is_refused() -> Result<()> {
    let mut f = Fixture::new(false)?;
    let n = f.k.term_var("n", f.num)?;
    let zz = f.add_of(f.z, f.z)?;
    let eq = f.k.term_eq(zz, n)?;
    let thm = f.k.new_axiom(f.th, eq)?;
    let err = f.rules.add(&f.k, "bad", thm).unwrap_err().to_string();
    assert!(
        err.contains("n on the right is not determined by the left"),
        "{err}"
    );
    Ok(())
}

#[test]
fn a_duplicate_name_is_refused() -> Result<()> {
    let mut f = Fixture::new(false)?;
    let existing = f.rules.fetch("add_z")?.thm.clone();
    let err = f
        .rules
        .add(&f.k, "add_z", existing)
        .unwrap_err()
        .to_string();
    assert!(err.contains("already registered"), "{err}");
    Ok(())
}

#[test]
fn a_non_equation_is_refused() -> Result<()> {
    let mut f = Fixture::new(false)?;
    let bool_ty = f.k.bool_ty();
    let p = f.k.new_constant(f.th, "p", bool_ty)?;
    let thm = f.k.new_axiom(f.th, p)?;
    let err = f.rules.add(&f.k, "bad", thm).unwrap_err().to_string();
    assert!(err.contains("not an equation"), "{err}");
    Ok(())
}

// --- the two halves meet ---------------------------------------------------

#[test]
fn every_certificate_the_rewriter_emits_is_accepted_by_replay() -> Result<()> {
    // The whole arrangement in one assertion: the untrusted half proposes, the
    // kernel disposes, and over a spread of inputs the kernel never refuses
    // what this rewriter wrote.
    let mut f = Fixture::new(false)?;
    let sz = f.succ(f.z)?;
    let ssz = f.succ(sz)?;
    let sssz = f.succ(ssz)?;

    let mut cases = Vec::new();
    for (l, r) in [
        (f.z, f.z),
        (f.z, sz),
        (sz, f.z),
        (sz, sz),
        (ssz, sz),
        (sssz, ssz),
    ] {
        cases.push(f.add_of(l, r)?);
    }
    // A nested one, and one under a binder.
    let nested_inner = f.add_of(sz, sz)?;
    cases.push(f.add_of(nested_inner, ssz)?);
    let x = f.k.term_var("x", f.num)?;
    let under = f.add_of(f.z, x)?;
    cases.push(f.k.term_abs(x, under)?);

    for (limit, ordering) in [
        (adamas::DEFAULT_LIMIT, Ordering::Unordered),
        (adamas::DEFAULT_LIMIT, Ordering::Ordered),
        (1, Ordering::Unordered),
        (2, Ordering::Unordered),
    ] {
        for term in &cases {
            let cert = f.k.rewrite(*term, &f.rules, limit, ordering)?;
            let thm = f
                .k
                .prove_certificate(f.th, &cert, &f.rules)
                .unwrap_or_else(|e| panic!("replay refused the rewriter's own certificate: {e}"));
            // And what it proves is exactly what the certificate claimed.
            let (lhs, rhs) = f.k.dest_eq(thm.concl()).expect("a theorem about equality");
            assert_eq!(lhs, *term);
            assert_eq!(rhs, cert.result);
        }
    }
    Ok(())
}

#[test]
fn a_path_the_rewriter_wrote_means_the_same_thing_to_replay() -> Result<()> {
    // Binders are opened by position on both sides. If the rewriter opened by
    // display name and replay by position (or the reverse), this is where it
    // would show.
    let mut f = Fixture::new(false)?;
    let zebra = f.k.term_var("zebra", f.num)?;
    let inner = f.add_of(f.z, zebra)?;
    let lam = f.k.term_abs(zebra, inner)?;
    let cert =
        f.k.rewrite(lam, &f.rules, adamas::DEFAULT_LIMIT, Ordering::Unordered)?;
    assert_eq!(cert.steps[0].path, vec![PathStep::Body]);
    let thm = f.k.prove_certificate(f.th, &cert, &f.rules)?;
    assert_eq!(
        f.k.thm_to_string(&thm),
        "⊢ (λzebra. add z «0») = (λzebra. «0»)"
    );
    Ok(())
}
