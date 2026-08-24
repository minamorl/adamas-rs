//! The type layer. Ported from `lib/adamas/type.rb`.
//!
//! Every type that exists went through here, so every type is well-formed:
//! known constructor, right arity, hash-consed.

use std::collections::BTreeMap;

use super::{Error, Kernel, Result};

/// A hash-consed type: its rank in the intern table.
///
/// Equality is a machine-word comparison, and it *is* structural equality —
/// that is what the intern table buys.
#[derive(Clone, Copy, PartialEq, Eq, Hash, Debug, PartialOrd, Ord)]
pub struct Ty(pub(super) u32);

impl Ty {
    /// Only ever visible inside `Kernel::new`, between the struct literal and
    /// the bootstrap of `bool`. It is never returned to a caller.
    pub(super) const PLACEHOLDER: Ty = Ty(u32::MAX);
}

#[derive(Clone, PartialEq, Eq, Debug)]
pub enum TyNode {
    /// A type variable: the `A` in `A → A`. Two type variables are the same
    /// type exactly when they carry the same name.
    Var { name: String },
    /// A type constructor applied to its arguments.
    Con { name: String, args: Vec<Ty> },
}

#[derive(PartialEq, Eq, Hash)]
pub(super) enum TyKey {
    Var(String),
    Con(String, Vec<Ty>),
}

/// `-str` in Ruby, plus the empty-name refusal.
pub(super) fn canonical_name(name: &str) -> Result<String> {
    if name.is_empty() {
        return Err(Error::Type("name must not be empty".into()));
    }
    Ok(name.to_string())
}

impl Kernel {
    pub fn ty_node(&self, ty: Ty) -> &TyNode {
        self.types.node(ty.0)
    }

    /// The type variables of a type, cached at intern time. Sorted by rank, so
    /// the order is deterministic within a process.
    pub fn ty_vars(&self, ty: Ty) -> &[Ty] {
        self.types.aux(ty.0)
    }

    pub fn ty_var(&mut self, name: &str) -> Result<Ty> {
        let name = canonical_name(name)?;
        let key = TyKey::Var(name.clone());
        // A type variable's variable set is itself.
        let rank = self
            .types
            .intern(key, |rank| (TyNode::Var { name }, vec![Ty(rank)]));
        Ok(Ty(rank))
    }

    /// The gate. `fusion.ml`'s `new_type`: declare a constructor of the given
    /// arity, refusing a name already taken — including `bool` and `fun`.
    pub fn new_type(&mut self, name: &str, arity: usize) -> Result<String> {
        let name = canonical_name(name)?;
        if self.registry.contains_key(&name) {
            return Err(Error::Type(format!(
                "type constructor {name} is already declared"
            )));
        }
        self.registry.insert(name.clone(), arity);
        Ok(name)
    }

    pub fn type_declared(&self, name: &str) -> bool {
        self.registry.contains_key(name)
    }

    pub fn ty_con(&mut self, name: &str, args: &[Ty]) -> Result<Ty> {
        let name = canonical_name(name)?;
        let arity = *self.registry.get(&name).ok_or_else(|| {
            Error::Type(format!(
                "unknown type constructor {name:?} (declare it with new_type or \
                 new_basic_type_definition)"
            ))
        })?;
        if args.len() != arity {
            return Err(Error::Type(format!(
                "{name} takes {arity} argument(s), given {}",
                args.len()
            )));
        }
        let mut vars: Vec<Ty> = Vec::new();
        for arg in args {
            for v in self.ty_vars(*arg) {
                vars.push(*v);
            }
        }
        vars.sort_unstable();
        vars.dedup();
        let args_vec = args.to_vec();
        let key = TyKey::Con(name.clone(), args_vec.clone());
        let rank = self.types.intern(key, |_| {
            (
                TyNode::Con {
                    name,
                    args: args_vec,
                },
                vars,
            )
        });
        Ok(Ty(rank))
    }

    pub fn ty_fun(&mut self, dom: Ty, cod: Ty) -> Result<Ty> {
        self.ty_con("fun", &[dom, cod])
    }

    /// `(dom, cod)` if `ty` is a function type, otherwise `None`.
    pub fn dest_fun(&self, ty: Ty) -> Option<(Ty, Ty)> {
        match self.ty_node(ty) {
            TyNode::Con { name, args } if name == "fun" && args.len() == 2 => {
                Some((args[0], args[1]))
            }
            _ => None,
        }
    }

    pub fn is_ty_var(&self, ty: Ty) -> bool {
        matches!(self.ty_node(ty), TyNode::Var { .. })
    }

    /// Simultaneous substitution of types for type variables.
    pub fn ty_subst(&mut self, theta: &BTreeMap<Ty, Ty>, ty: Ty) -> Result<Ty> {
        if theta.is_empty() {
            return Ok(ty);
        }
        match self.ty_node(ty).clone() {
            TyNode::Var { .. } => Ok(*theta.get(&ty).unwrap_or(&ty)),
            TyNode::Con { name, args } => {
                let mut mapped = Vec::with_capacity(args.len());
                for arg in args {
                    mapped.push(self.ty_subst(theta, arg)?);
                }
                self.ty_con(&name, &mapped)
            }
        }
    }

    /// One-way matching: the substitution that turns `pattern` into `target`,
    /// or `None` if there is none.
    pub fn ty_match(
        &self,
        pattern: Ty,
        target: Ty,
        acc: BTreeMap<Ty, Ty>,
    ) -> Option<BTreeMap<Ty, Ty>> {
        match self.ty_node(pattern) {
            TyNode::Var { .. } => match acc.get(&pattern) {
                Some(&bound) if bound != target => None,
                _ => {
                    let mut acc = acc;
                    acc.insert(pattern, target);
                    Some(acc)
                }
            },
            TyNode::Con {
                name: pat_name,
                args: pat_args,
            } => match self.ty_node(target) {
                TyNode::Con {
                    name: tgt_name,
                    args: tgt_args,
                } if pat_name == tgt_name && pat_args.len() == tgt_args.len() => {
                    let mut acc = acc;
                    for (p, t) in pat_args.iter().zip(tgt_args.iter()) {
                        acc = self.ty_match(*p, *t, acc)?;
                    }
                    Some(acc)
                }
                _ => None,
            },
        }
    }

    /// A type substitution may only replace type *variables*, and only by
    /// types. The second half is free here: `Ty` cannot hold a non-type.
    pub fn check_ty_subst(&self, theta: &BTreeMap<Ty, Ty>) -> Result<()> {
        for key in theta.keys() {
            if !self.is_ty_var(*key) {
                return Err(Error::Type(format!(
                    "not a type variable: {}",
                    self.ty_to_string(*key)
                )));
            }
        }
        Ok(())
    }

    pub fn ty_to_string(&self, ty: Ty) -> String {
        match self.ty_node(ty) {
            TyNode::Var { name } => name.clone(),
            TyNode::Con { name, args } if name == "fun" && args.len() == 2 => {
                let dom = self.ty_to_string(args[0]);
                let dom = if self.dest_fun(args[0]).is_some() {
                    format!("({dom})")
                } else {
                    dom
                };
                format!("{dom} → {}", self.ty_to_string(args[1]))
            }
            TyNode::Con { name, args } if args.is_empty() => name.clone(),
            TyNode::Con { name, args } => {
                let inner: Vec<String> = args.iter().map(|a| self.ty_to_string(*a)).collect();
                format!("{name}({})", inner.join(", "))
            }
        }
    }
}
