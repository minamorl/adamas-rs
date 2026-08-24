//! A hash-cons table.
//!
//! Ported from `lib/adamas/interner.rb`. Keys are built from the *ranks* of
//! already-interned children rather than from the children themselves, so
//! hashing a key is O(1) in the size of the subtree. Ranks are allocated in
//! creation order and double as a total order on nodes, which the kernel uses
//! to keep hypothesis lists canonical.
//!
//! The table holds its nodes forever. That is deliberate — it is what makes a
//! rank stable — and it is the price of O(1) equality.
//!
//! Where Ruby had to bolt structural-equality-is-identity onto its nodes with
//! an `Interned` mixin that overrides `==`/`hash`/`eql?`, here a node *is* its
//! rank: a `u32` newtype whose `PartialEq` is a machine-word comparison by
//! construction. There is nothing to override and nothing to get wrong.

use std::collections::HashMap;
use std::hash::Hash;

pub struct Interner<K, N, A> {
    table: HashMap<K, u32>,
    nodes: Vec<N>,
    aux: Vec<A>,
}

impl<K: Eq + Hash, N, A> Interner<K, N, A> {
    pub fn new() -> Self {
        Interner {
            table: HashMap::new(),
            nodes: Vec::new(),
            aux: Vec::new(),
        }
    }

    /// The canonical rank for `key`, calling `make` only if this is the first
    /// time the key has been seen. `make` returns `(node, aux)`, where `aux` is
    /// derived data cached alongside the node — a term's type, a type's
    /// variables.
    ///
    /// `make` is handed the rank the node is about to receive. Ruby could not
    /// do this — its block ran before the rank existed — which is why
    /// `Type.var` had to have its own variable set filled in by a second pass.
    /// A type variable's variable set is itself, and here it can simply say so.
    pub fn intern(&mut self, key: K, make: impl FnOnce(u32) -> (N, A)) -> u32 {
        if let Some(&rank) = self.table.get(&key) {
            return rank;
        }
        let rank = self.nodes.len() as u32;
        let (node, aux) = make(rank);
        self.nodes.push(node);
        self.aux.push(aux);
        self.table.insert(key, rank);
        rank
    }

    pub fn node(&self, rank: u32) -> &N {
        &self.nodes[rank as usize]
    }

    pub fn aux(&self, rank: u32) -> &A {
        &self.aux[rank as usize]
    }

    /// How many distinct nodes the table holds. The kernel exposes this for
    /// diagnostics; nothing in the trusted path reads it.
    pub fn len(&self) -> usize {
        self.nodes.len()
    }
}

impl<K: Eq + Hash, N, A> Default for Interner<K, N, A> {
    fn default() -> Self {
        Self::new()
    }
}
