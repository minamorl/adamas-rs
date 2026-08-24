//! The term layer. Ported from `lib/adamas/term.rb`.
//!
//! Every term is built here, and every constructor type-checks, so an ill-typed
//! term does not exist to be reasoned about. This is one half of the LCF
//! discipline; [`super::Thm`] is the other.

use std::collections::BTreeMap;

use super::types::canonical_name;
use super::{Error, Kernel, Result, Ty};

pub(super) const EQ_NAME: &str = "=";

/// A hash-consed term: its rank in the intern table.
#[derive(Clone, Copy, PartialEq, Eq, Hash, Debug, PartialOrd, Ord)]
pub struct Term(pub(super) u32);

#[derive(Clone, PartialEq, Eq, Debug)]
pub enum TermNode {
    /// A free variable. Its identity is the pair (name, type): `x:bool` and
    /// `x:A` are two different variables that happen to be spelled alike.
    Var { name: String, ty: Ty },
    /// A de Bruijn index, counting binders outwards from its own position. It
    /// carries its own type so that `type_of` stays O(1) and needs no
    /// environment.
    Bound { index: u32, ty: Ty },
    /// A constant. Which names are legal, and at which types, is the theory's
    /// business.
    Const { name: String, ty: Ty },
    /// Application, `rator rand`.
    Comb { rator: Term, rand: Term },
    /// Abstraction, `λbinder_name:binder_type. body`, where `body` refers to
    /// the binder as `Bound(0)`.
    ///
    /// `binder_name` is *display only*: it is deliberately left out of the
    /// intern key, so `λx. x` and `λy. y` are not merely equal, they are the
    /// same node. Alpha-equivalence therefore costs one word comparison.
    Abs {
        binder_name: String,
        binder_type: Ty,
        body: Term,
    },
}

#[derive(PartialEq, Eq, Hash)]
pub(super) enum TermKey {
    Var(String, Ty),
    Bound(u32, Ty),
    Const(String, Ty),
    Comb(Term, Term),
    /// The binder's name is absent on purpose: that is what makes
    /// alpha-equivalent terms identical nodes.
    Abs(Ty, Term),
}

/// Derived data cached on each node at intern time.
pub(super) struct Info {
    pub ty: Ty,
    /// One more than the largest dangling de Bruijn index, so 0 means "no
    /// dangling index", i.e. this term is safe to hand to a user.
    pub loose: u32,
    /// The term's free variables, sorted by rank.
    pub frees: Vec<Term>,
}

fn merge_frees(left: &[Term], right: &[Term]) -> Vec<Term> {
    if left.is_empty() {
        return right.to_vec();
    }
    if right.is_empty() {
        return left.to_vec();
    }
    let mut all = Vec::with_capacity(left.len() + right.len());
    all.extend_from_slice(left);
    all.extend_from_slice(right);
    all.sort_unstable();
    all.dedup();
    all
}

impl Kernel {
    // --- inspection --------------------------------------------------------

    pub fn term_node(&self, term: Term) -> &TermNode {
        self.terms.node(term.0)
    }

    pub fn type_of(&self, term: Term) -> Ty {
        self.terms.aux(term.0).ty
    }

    pub fn frees(&self, term: Term) -> &[Term] {
        &self.terms.aux(term.0).frees
    }

    pub fn loose(&self, term: Term) -> u32 {
        self.terms.aux(term.0).loose
    }

    pub fn closed(&self, term: Term) -> bool {
        self.loose(term) == 0
    }

    pub fn free_in(&self, var: Term, term: Term) -> bool {
        self.frees(term).binary_search(&var).is_ok()
    }

    pub fn is_var(&self, term: Term) -> bool {
        matches!(self.term_node(term), TermNode::Var { .. })
    }

    /// The type variables of a term.
    pub fn term_type_vars(&self, term: Term) -> Vec<Ty> {
        match self.term_node(term) {
            TermNode::Var { ty, .. } | TermNode::Const { ty, .. } | TermNode::Bound { ty, .. } => {
                self.ty_vars(*ty).to_vec()
            }
            TermNode::Comb { rator, rand } => {
                let mut all = self.term_type_vars(*rator);
                all.extend(self.term_type_vars(*rand));
                all.sort_unstable();
                all.dedup();
                all
            }
            TermNode::Abs {
                binder_type, body, ..
            } => {
                let mut all = self.ty_vars(*binder_type).to_vec();
                all.extend(self.term_type_vars(*body));
                all.sort_unstable();
                all.dedup();
                all
            }
        }
    }

    /// Terms handed to or taken from user code must have no dangling index.
    fn require_closed(&self, term: Term) -> Result<Term> {
        if self.closed(term) {
            return Ok(term);
        }
        Err(Error::Type(format!(
            "term has a dangling de Bruijn index: {}",
            self.term_to_string(term)
        )))
    }

    // --- construction ------------------------------------------------------

    pub fn term_var(&mut self, name: &str, ty: Ty) -> Result<Term> {
        let name = canonical_name(name)?;
        let key = TermKey::Var(name.clone(), ty);
        let rank = self.terms.intern(key, |rank| {
            (
                TermNode::Var { name, ty },
                Info {
                    ty,
                    loose: 0,
                    frees: vec![Term(rank)],
                },
            )
        });
        Ok(Term(rank))
    }

    pub fn term_comb(&mut self, rator: Term, rand: Term) -> Result<Term> {
        self.require_closed(rator)?;
        self.require_closed(rand)?;
        self.comb_raw(rator, rand)
    }

    pub fn term_abs(&mut self, var: Term, body: Term) -> Result<Term> {
        let (name, ty) = self.dest_var(var, "a binder")?;
        self.require_closed(body)?;
        let bound = self.bind(body, var, 0)?;
        self.abs_raw(name, ty, bound)
    }

    /// [`Kernel::term_abs`], but displayed with `name` instead of the bound
    /// variable's own. Best effort, and necessarily so: display names are
    /// outside the intern key, so if this abstraction already exists it keeps
    /// the name it was first built with.
    pub fn term_abs_named(&mut self, name: &str, var: Term, body: Term) -> Result<Term> {
        let (_, ty) = self.dest_var(var, "a binder")?;
        self.require_closed(body)?;
        let name = canonical_name(name)?;
        let bound = self.bind(body, var, 0)?;
        self.abs_raw(name, ty, bound)
    }

    /// `lhs = rhs`. Equality is the kernel's only primitive constant, and it is
    /// polymorphic: each use is `=` at the type of its operands.
    pub fn term_eq(&mut self, lhs: Term, rhs: Term) -> Result<Term> {
        let ty = self.type_of(lhs);
        if ty != self.type_of(rhs) {
            return Err(Error::Type(format!(
                "cannot equate {}:{} with {}:{}",
                self.term_to_string(lhs),
                self.ty_to_string(ty),
                self.term_to_string(rhs),
                self.ty_to_string(self.type_of(rhs))
            )));
        }
        let bool_ty = self.bool_ty;
        let inner = self.ty_fun(ty, bool_ty)?;
        let eq_ty = self.ty_fun(ty, inner)?;
        let eq = self.const_raw(EQ_NAME, eq_ty)?;
        let applied = self.comb_raw(eq, lhs)?;
        self.comb_raw(applied, rhs)
    }

    /// `(lhs, rhs)` if `term` is an equation, otherwise `None`.
    pub fn dest_eq(&self, term: Term) -> Option<(Term, Term)> {
        let TermNode::Comb { rator, rand: rhs } = self.term_node(term) else {
            return None;
        };
        let TermNode::Comb {
            rator: head,
            rand: lhs,
        } = self.term_node(*rator)
        else {
            return None;
        };
        match self.term_node(*head) {
            TermNode::Const { name, .. } if name == EQ_NAME => Some((*lhs, *rhs)),
            _ => None,
        }
    }

    fn dest_var(&self, term: Term, what: &str) -> Result<(String, Ty)> {
        match self.term_node(term) {
            TermNode::Var { name, ty } => Ok((name.clone(), *ty)),
            _ => Err(Error::Type(format!(
                "{what} must be a variable, got {}",
                self.term_to_string(term)
            ))),
        }
    }

    // --- abstractions ------------------------------------------------------

    /// Opens an abstraction with a variable fresh for its body, undoing what
    /// [`Kernel::term_abs`] did. Returns `(variable, body)`.
    pub fn dest_abs(&mut self, term: Term) -> Result<(Term, Term)> {
        let TermNode::Abs {
            binder_name,
            binder_type,
            ..
        } = self.term_node(term).clone()
        else {
            return Err(Error::Type(format!(
                "not an abstraction: {}",
                self.term_to_string(term)
            )));
        };
        let avoid = self.frees(term).to_vec();
        let v = self.variant(&avoid, &binder_name, binder_type)?;
        let body = self.open_abs(term, v)?;
        Ok((v, body))
    }

    /// The body of `term` with its bound index replaced by `replacement`. This
    /// is beta-reduction of a single redex, and it is *not* an inference rule:
    /// it says nothing about what is true. The rule that does is
    /// [`Kernel::beta`](super::Kernel::beta).
    pub fn open_abs(&mut self, term: Term, replacement: Term) -> Result<Term> {
        let TermNode::Abs {
            binder_type, body, ..
        } = self.term_node(term).clone()
        else {
            return Err(Error::Type(format!(
                "not an abstraction: {}",
                self.term_to_string(term)
            )));
        };
        if binder_type != self.type_of(replacement) {
            return Err(Error::Type(format!(
                "cannot open a {} binder with {}",
                self.ty_to_string(binder_type),
                self.term_to_string(replacement)
            )));
        }
        self.require_closed(replacement)?;
        self.subst_bound(body, replacement, 0)
    }

    /// A variable named like `name` but distinct from every variable in
    /// `avoid`.
    pub fn variant(&mut self, avoid: &[Term], name: &str, ty: Ty) -> Result<Term> {
        let taken: Vec<&str> = avoid
            .iter()
            .filter_map(|t| match self.term_node(*t) {
                TermNode::Var { name, .. } => Some(name.as_str()),
                _ => None,
            })
            .collect();
        let mut name = name.to_string();
        while taken.contains(&name.as_str()) {
            name.push('\'');
        }
        self.term_var(&name, ty)
    }

    // --- substitution ------------------------------------------------------

    /// Simultaneous substitution of terms for free variables.
    ///
    /// No renaming happens, and none is needed: a bound occurrence is an index,
    /// not a name, so nothing a substitution inserts can be captured.
    pub fn subst(&mut self, theta: &BTreeMap<Term, Term>, term: Term) -> Result<Term> {
        if theta.is_empty() || !theta.keys().any(|v| self.free_in(*v, term)) {
            return Ok(term);
        }
        match self.term_node(term).clone() {
            TermNode::Var { .. } => Ok(*theta.get(&term).unwrap_or(&term)),
            TermNode::Comb { rator, rand } => {
                let l = self.subst(theta, rator)?;
                let r = self.subst(theta, rand)?;
                self.comb_raw(l, r)
            }
            TermNode::Abs {
                binder_name,
                binder_type,
                body,
            } => {
                let b = self.subst(theta, body)?;
                self.abs_raw(binder_name, binder_type, b)
            }
            _ => Ok(term),
        }
    }

    /// A term substitution replaces free variables by terms of the same type.
    pub fn check_subst(&self, theta: &BTreeMap<Term, Term>) -> Result<()> {
        for (v, t) in theta {
            let TermNode::Var { ty, .. } = self.term_node(*v) else {
                return Err(Error::Type(format!(
                    "not a variable: {}",
                    self.term_to_string(*v)
                )));
            };
            self.require_closed(*t)?;
            if *ty != self.type_of(*t) {
                return Err(Error::Type(format!(
                    "cannot substitute {}:{} for {}:{}",
                    self.term_to_string(*t),
                    self.ty_to_string(self.type_of(*t)),
                    self.term_to_string(*v),
                    self.ty_to_string(*ty)
                )));
            }
        }
        Ok(())
    }

    /// Simultaneous substitution of types for type variables, throughout a
    /// term. Here bound variables have no names to collide, so there is no
    /// renaming to do.
    pub fn inst_type_term(&mut self, theta: &BTreeMap<Ty, Ty>, term: Term) -> Result<Term> {
        if theta.is_empty() {
            return Ok(term);
        }
        match self.term_node(term).clone() {
            TermNode::Var { name, ty } => {
                let ty = self.ty_subst(theta, ty)?;
                self.term_var(&name, ty)
            }
            TermNode::Const { name, ty } => {
                let ty = self.ty_subst(theta, ty)?;
                self.const_raw(&name, ty)
            }
            TermNode::Bound { index, ty } => {
                let ty = self.ty_subst(theta, ty)?;
                self.bound_raw(index, ty)
            }
            TermNode::Comb { rator, rand } => {
                let l = self.inst_type_term(theta, rator)?;
                let r = self.inst_type_term(theta, rand)?;
                self.comb_raw(l, r)
            }
            TermNode::Abs {
                binder_name,
                binder_type,
                body,
            } => {
                let bt = self.ty_subst(theta, binder_type)?;
                let b = self.inst_type_term(theta, body)?;
                self.abs_raw(binder_name, bt, b)
            }
        }
    }

    // --- internals ---------------------------------------------------------
    //
    // Below this line terms may carry dangling indices, because that is what it
    // means to be halfway through building or taking apart an abstraction.

    pub(super) fn const_raw(&mut self, name: &str, ty: Ty) -> Result<Term> {
        let name = canonical_name(name)?;
        let key = TermKey::Const(name.clone(), ty);
        let rank = self.terms.intern(key, |_| {
            (
                TermNode::Const { name, ty },
                Info {
                    ty,
                    loose: 0,
                    frees: Vec::new(),
                },
            )
        });
        Ok(Term(rank))
    }

    fn bound_raw(&mut self, index: u32, ty: Ty) -> Result<Term> {
        let key = TermKey::Bound(index, ty);
        let rank = self.terms.intern(key, |_| {
            (
                TermNode::Bound { index, ty },
                Info {
                    ty,
                    loose: index + 1,
                    frees: Vec::new(),
                },
            )
        });
        Ok(Term(rank))
    }

    fn comb_raw(&mut self, rator: Term, rand: Term) -> Result<Term> {
        let rator_ty = self.type_of(rator);
        let Some((dom, cod)) = self.dest_fun(rator_ty) else {
            return Err(Error::Type(format!(
                "{} has type {} and cannot be applied",
                self.term_to_string(rator),
                self.ty_to_string(rator_ty)
            )));
        };
        if dom != self.type_of(rand) {
            return Err(Error::Type(format!(
                "{} expects {}, but {} has type {}",
                self.term_to_string(rator),
                self.ty_to_string(dom),
                self.term_to_string(rand),
                self.ty_to_string(self.type_of(rand))
            )));
        }
        let info = Info {
            ty: cod,
            loose: self.loose(rator).max(self.loose(rand)),
            frees: merge_frees(self.frees(rator), self.frees(rand)),
        };
        let key = TermKey::Comb(rator, rand);
        let rank = self
            .terms
            .intern(key, |_| (TermNode::Comb { rator, rand }, info));
        Ok(Term(rank))
    }

    fn abs_raw(&mut self, binder_name: String, binder_type: Ty, body: Term) -> Result<Term> {
        let body_ty = self.type_of(body);
        let ty = self.ty_fun(binder_type, body_ty)?;
        let info = Info {
            ty,
            loose: self.loose(body).saturating_sub(1),
            frees: self.frees(body).to_vec(),
        };
        let key = TermKey::Abs(binder_type, body);
        let rank = self.terms.intern(key, |_| {
            (
                TermNode::Abs {
                    binder_name,
                    binder_type,
                    body,
                },
                info,
            )
        });
        Ok(Term(rank))
    }

    /// Free occurrences of `var` become the index `depth`.
    fn bind(&mut self, term: Term, var: Term, depth: u32) -> Result<Term> {
        if !self.free_in(var, term) {
            return Ok(term);
        }
        match self.term_node(term).clone() {
            TermNode::Var { ty, .. } => self.bound_raw(depth, ty),
            TermNode::Comb { rator, rand } => {
                let l = self.bind(rator, var, depth)?;
                let r = self.bind(rand, var, depth)?;
                self.comb_raw(l, r)
            }
            TermNode::Abs {
                binder_name,
                binder_type,
                body,
            } => {
                let b = self.bind(body, var, depth + 1)?;
                self.abs_raw(binder_name, binder_type, b)
            }
            _ => Ok(term),
        }
    }

    /// Occurrences of the index `depth` become `replacement`.
    fn subst_bound(&mut self, term: Term, replacement: Term, depth: u32) -> Result<Term> {
        if self.loose(term) <= depth {
            return Ok(term);
        }
        match self.term_node(term).clone() {
            TermNode::Bound { index, .. } => Ok(if index == depth { replacement } else { term }),
            TermNode::Comb { rator, rand } => {
                let l = self.subst_bound(rator, replacement, depth)?;
                let r = self.subst_bound(rand, replacement, depth)?;
                self.comb_raw(l, r)
            }
            TermNode::Abs {
                binder_name,
                binder_type,
                body,
            } => {
                let b = self.subst_bound(body, replacement, depth + 1)?;
                self.abs_raw(binder_name, binder_type, b)
            }
            _ => Ok(term),
        }
    }

    // --- printing ----------------------------------------------------------

    pub fn term_to_string(&self, term: Term) -> String {
        self.fmt(term, 0)
    }

    /// How tightly a node binds. A node is parenthesised when it appears where
    /// something tighter was required — that is the whole rule, and it is why
    /// `(λv. v = v) q` keeps its parentheses while `λv. v = v` alone does not.
    fn precedence(&self, term: Term) -> u8 {
        if self.dest_eq(term).is_some() {
            return 2;
        }
        match self.term_node(term) {
            TermNode::Abs { .. } => 1,
            TermNode::Comb { .. } => 3,
            _ => 4,
        }
    }

    fn fmt(&self, term: Term, required: u8) -> String {
        let rendered = self.fmt_bare(term);
        if self.precedence(term) < required {
            format!("({rendered})")
        } else {
            rendered
        }
    }

    fn fmt_bare(&self, term: Term) -> String {
        if let Some((lhs, rhs)) = self.dest_eq(term) {
            return format!("{} = {}", self.fmt(lhs, 3), self.fmt(rhs, 3));
        }
        match self.term_node(term) {
            TermNode::Var { name, .. } | TermNode::Const { name, .. } => name.clone(),
            TermNode::Bound { index, .. } => format!("«{index}»"),
            TermNode::Comb { rator, rand } => {
                format!("{} {}", self.fmt(*rator, 3), self.fmt(*rand, 4))
            }
            TermNode::Abs {
                binder_name, body, ..
            } => {
                format!("λ{binder_name}. {}", self.fmt(*body, 0))
            }
        }
    }

    pub fn thm_to_string(&self, thm: &super::Thm) -> String {
        let hyps: Vec<String> = thm.hyps().iter().map(|h| self.term_to_string(*h)).collect();
        if hyps.is_empty() {
            format!("⊢ {}", self.term_to_string(thm.concl()))
        } else {
            format!("{} ⊢ {}", hyps.join(", "), self.term_to_string(thm.concl()))
        }
    }
}
