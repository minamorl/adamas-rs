//! Rules derived from the ten. Ported from `lib/adamas/derived.rb`.
//!
//! Nothing here is trusted. Every function is a composition of the primitives,
//! so a mistake in this file is a failed proof, never a false theorem — and
//! because it lives outside `kernel`, the compiler enforces that: these
//! functions cannot reach `Thm`'s fields any more than a stranger's code can.

use std::collections::BTreeMap;

use crate::kernel::Term;
use crate::kernel::{Error, Kernel, Result, TermNode, TheoryId, Thm};

impl Kernel {
    /// `Γ ⊢ b = a` from `Γ ⊢ a = b`.
    pub fn sym(&mut self, theory: TheoryId, thm: &Thm) -> Result<Thm> {
        let Some((lhs, _)) = self.dest_eq(thm.concl()) else {
            return Err(Error::Rule(format!(
                "SYM: {} is not an equation",
                self.term_to_string(thm.concl())
            )));
        };
        // The `=` at the operand type, dug out of the conclusion itself.
        let TermNode::Comb { rator: inner, .. } = self.term_node(thm.concl()).clone() else {
            return Err(Error::Rule("SYM: malformed equation".into()));
        };
        let TermNode::Comb {
            rator: equality, ..
        } = self.term_node(inner).clone()
        else {
            return Err(Error::Rule("SYM: malformed equation".into()));
        };
        let reflexive = self.refl(theory, lhs)?;
        let eq_refl = self.refl(theory, equality)?;
        let half = self.mk_comb(theory, &eq_refl, thm)?;
        let congruence = self.mk_comb(theory, &half, &reflexive)?;
        self.eq_mp(theory, &congruence, &reflexive)
    }

    /// `Γ ⊢ f x = f y` from `Γ ⊢ x = y`.
    pub fn ap_term(&mut self, theory: TheoryId, func: Term, thm: &Thm) -> Result<Thm> {
        let r = self.refl(theory, func)?;
        self.mk_comb(theory, &r, thm)
    }

    /// `Γ ⊢ f x = g x` from `Γ ⊢ f = g`.
    pub fn ap_thm(&mut self, theory: TheoryId, thm: &Thm, arg: Term) -> Result<Thm> {
        let r = self.refl(theory, arg)?;
        self.mk_comb(theory, thm, &r)
    }

    /// Discharge `p` from `Δ ⊢ q` given `Γ ⊢ p`: `Γ ∪ (Δ - p) ⊢ q`.
    pub fn prove_hyp(&mut self, theory: TheoryId, proof: &Thm, consequence: &Thm) -> Result<Thm> {
        let deduced = self.deduct_antisym_rule(theory, proof, consequence)?;
        self.eq_mp(theory, &deduced, proof)
    }

    /// `Γ ⊢ p = T` ⟹ `Γ ⊢ p`.
    pub fn eqt_elim(&mut self, theory: TheoryId, truth: &Thm, thm: &Thm) -> Result<Thm> {
        let symmetric = self.sym(theory, thm)?;
        self.eq_mp(theory, &symmetric, truth)
    }

    /// True when `term` is a beta-redex, `(λx. t) s`.
    pub fn is_beta_redex(&self, term: Term) -> bool {
        let TermNode::Comb { rator, .. } = *self.term_node(term) else {
            return false;
        };
        matches!(self.term_node(rator), TermNode::Abs { .. })
    }

    /// Beta for an arbitrary argument: `⊢ (λx. t) s = t[x := s]`.
    ///
    /// The kernel's [`Kernel::beta`] only relates `(λx. t) v` to `t` for a
    /// variable `v`, just as `fusion.ml` does. The general case is this:
    /// beta-reduce against a fresh variable, then instantiate that variable to
    /// the real argument.
    pub fn beta_conv(&mut self, theory: TheoryId, term: Term) -> Result<Thm> {
        let TermNode::Comb {
            rator: abstraction,
            rand,
        } = *self.term_node(term)
        else {
            return Err(Error::Rule(format!(
                "BETA_CONV: not a beta-redex: {}",
                self.term_to_string(term)
            )));
        };
        let TermNode::Abs {
            binder_name,
            binder_type,
            ..
        } = self.term_node(abstraction).clone()
        else {
            return Err(Error::Rule(format!(
                "BETA_CONV: not a beta-redex: {}",
                self.term_to_string(term)
            )));
        };
        let avoid = self.frees(term).to_vec();
        let fresh = self.variant(&avoid, &binder_name, binder_type)?;
        let redex = self.term_comb(abstraction, fresh)?;
        let base = self.beta(theory, redex)?;
        self.inst(theory, &BTreeMap::from([(fresh, rand)]), &base)
    }

    /// `⊢ t = t'` where `t'` is `t` with every beta-redex reduced, outermost
    /// first. Built by congruence out of [`Kernel::beta_conv`], so it is a
    /// proof, not a rewrite someone has to be trusted about.
    pub fn beta_reduce(&mut self, theory: TheoryId, term: Term) -> Result<Thm> {
        if !self.is_beta_redex(term) {
            return self.congruence(theory, term);
        }
        let step = self.beta_conv(theory, term)?;
        let (_, right) = self.dest_eq(step.concl()).ok_or_else(|| {
            Error::Rule(format!(
                "BETA_REDUCE: {} is not an equation",
                self.term_to_string(step.concl())
            ))
        })?;
        let right_step = self.beta_reduce(theory, right)?;
        self.trans(theory, &step, &right_step)
    }

    /// `Γ ⊢ p` ⟹ `Γ ⊢ p'`, where `p'` is the beta-normal form of `p`.
    pub fn beta_rule(&mut self, theory: TheoryId, thm: &Thm) -> Result<Thm> {
        let equation = self.beta_reduce(theory, thm.concl())?;
        self.eq_mp(theory, &equation, thm)
    }

    /// `Γ ⊢ p` ⟹ `Γ ⊢ p = T`, using an instance of `⊢ (p = T) = p`.
    pub fn eqt_intro(&mut self, theory: TheoryId, true_right: &Thm, thm: &Thm) -> Result<Thm> {
        let rule = self.instantiate_true_right(theory, true_right, thm.concl())?;
        let symmetric = self.sym(theory, &rule)?;
        self.eq_mp(theory, &symmetric, thm)
    }

    /// `⊢ t = t` refined by reducing inside `t`.
    fn congruence(&mut self, theory: TheoryId, term: Term) -> Result<Thm> {
        match self.term_node(term).clone() {
            TermNode::Comb { rator, rand } => {
                let r = self.beta_reduce(theory, rator)?;
                let s = self.beta_reduce(theory, rand)?;
                self.mk_comb(theory, &r, &s)
            }
            TermNode::Abs { .. } => {
                let (var, body) = self.dest_abs(term)?;
                let reduced = self.beta_reduce(theory, body)?;
                self.abs(theory, var, &reduced)
            }
            _ => self.refl(theory, term),
        }
    }

    /// Helper for [`Kernel::eqt_intro`].
    fn instantiate_true_right(
        &mut self,
        theory: TheoryId,
        true_right: &Thm,
        proposition: Term,
    ) -> Result<Thm> {
        let (_, rhs) = self.dest_eq(true_right.concl()).ok_or_else(|| {
            Error::Rule(format!(
                "EQT_INTRO: {} is not an equation",
                self.term_to_string(true_right.concl())
            ))
        })?;
        let rule = if self.is_var(rhs) {
            self.inst(theory, &BTreeMap::from([(rhs, proposition)]), true_right)?
        } else {
            true_right.clone()
        };
        let (lhs, rhs) = self.dest_eq(rule.concl()).ok_or_else(|| {
            Error::Rule(format!(
                "EQT_INTRO: {} is not an equation",
                self.term_to_string(rule.concl())
            ))
        })?;
        let Some((eq_lhs, _)) = self.dest_eq(lhs) else {
            return Err(Error::Rule(format!(
                "EQT_INTRO: {} is not a true-right rule",
                self.term_to_string(rule.concl())
            )));
        };
        if rhs != proposition {
            return Err(Error::Rule(format!(
                "EQT_INTRO: {} is not {}",
                self.term_to_string(rhs),
                self.term_to_string(proposition)
            )));
        }
        if eq_lhs != proposition {
            return Err(Error::Rule(format!(
                "EQT_INTRO: {} is not {}",
                self.term_to_string(eq_lhs),
                self.term_to_string(proposition)
            )));
        }
        Ok(rule)
    }
}
