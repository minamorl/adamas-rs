//! The trusted core.
//!
//! Ported from `lib/adamas/{thm,type,term,theory}.rb` — 898 lines of Ruby.
//!
//! # Why this port exists
//!
//! adamas's README leads with *"Theorems you cannot forge"*, and then, under
//! **What the kernel does not guarantee**, says the first thing honestly:
//!
//! > **Ruby has no real privacy.** `send`, `Marshal` and `ObjectSpace` defeat
//! > any scheme, and Adamas does not pretend otherwise.
//!
//! `test/forgery_test.rb` carries a test named
//! `test_a_well_formed_forgery_is_only_stopped_by_the_privacy` — a sequent that
//! passes every invariant and is stopped by nothing but a porous
//! `private_class_method`.
//!
//! Here the boundary is the module system. [`Thm`]'s fields are private to
//! `kernel` and its children. Outside this module there is no constructor, no
//! reflective back door, and no `send`. A `Thm` that exists was derived. That
//! is the whole difference, and it is the reason the port is an improvement
//! rather than a translation.
//!
//! What the kernel still does *not* guarantee is unchanged from Ruby and worth
//! repeating: it is not verified, it is *small*; `bool` and `fun` are the whole
//! type language until `new_type` grows it; and consistency is the caller's
//! problem once `new_axiom` is called.

mod rules;
mod term;
mod types;

use std::collections::HashMap;

use crate::intern::Interner;

pub use term::{Term, TermNode};
pub use types::{Ty, TyNode};

// ---------------------------------------------------------------------------
// errors
// ---------------------------------------------------------------------------

/// Every recoverable refusal the kernel can make.
///
/// House style (`house_style_rust.pin`): a public fallible operation returns
/// `Result` with an explicit error representation, and never signals failure by
/// panicking. Ruby raised `TypeError` / `RuleError` / `TheoryError`; the three
/// survive as variants so a caller can still tell "that is not a term" from
/// "that rule does not apply".
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum Error {
    /// Ill-formed or ill-typed syntax: `Adamas::TypeError`.
    Type(String),
    /// A primitive rule refused: `Adamas::RuleError`.
    Rule(String),
    /// A theory-level gate refused: `Adamas::TheoryError`.
    Theory(String),
}

impl std::fmt::Display for Error {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            Error::Type(m) => write!(f, "type error: {m}"),
            Error::Rule(m) => write!(f, "rule error: {m}"),
            Error::Theory(m) => write!(f, "theory error: {m}"),
        }
    }
}

impl std::error::Error for Error {}

pub type Result<T> = std::result::Result<T, Error>;

// ---------------------------------------------------------------------------
// theorems
// ---------------------------------------------------------------------------

/// Which theory a theorem belongs to.
///
/// Ruby scoped theorems by object identity (`thm.theory.equal?(self)`). A
/// `TheoryId` is the same relation, made explicit: a theorem proved in one
/// theory is not a theorem in another, so an axiom asserted in one development
/// cannot leak into another that never accepted it.
#[derive(Clone, Copy, PartialEq, Eq, Hash, Debug, PartialOrd, Ord)]
pub struct TheoryId(u32);

/// A theorem: the sequent `hyps ⊢ concl`, in a particular theory.
///
/// This is the whole trusted interface of the library. **The fields are private
/// to `kernel`.** The only code that constructs one is [`Kernel::sequent`],
/// whose callers are the ten primitive rules and the definition mechanisms. A
/// value of this type is therefore not a claim someone made, it is a claim
/// something derived — and unlike the Ruby original, that is enforced by the
/// language rather than asserted in a comment.
///
/// The invariants hold for every `Thm` that exists, because `sequent` is the
/// only way in and it checks them:
///
/// * the conclusion and every hypothesis is a closed term of type `bool`;
/// * the hypothesis list is canonical — deduplicated, and sorted by rank, so
///   that two derivations of the same sequent are equal.
///
/// # The forgery boundary, checked by the compiler
///
/// Ruby's `forgery_test.rb` had to *assert* that forgery fails, and documented
/// one case that gets through. Here the same three attacks do not compile, and
/// these doctests fail the suite if that ever stops being true.
///
/// **The error code is pinned on purpose.** A bare `compile_fail` passes when
/// the snippet fails to compile for *any* reason, so a typo in it would read as
/// a closed door. Naming `E0451` / `E0616` makes the test assert that the
/// privacy is what stopped it. The positive control below compiles, so the
/// snippets are known to be otherwise valid.
///
/// A struct literal cannot name the private fields:
///
/// ```compile_fail,E0451
/// # use adamas::{Kernel, Thm};
/// let mut k = Kernel::new();
/// let th = k.new_theory("t");
/// let b = k.bool_ty();
/// let p = k.term_var("p", b).unwrap();
/// let forged = Thm { theory: th, hyps: vec![], concl: p };
/// ```
///
/// The fields cannot be read around the accessors, so no `Thm` can be taken
/// apart and reassembled with a different conclusion:
///
/// ```compile_fail,E0616
/// # use adamas::Kernel;
/// let mut k = Kernel::new();
/// let th = k.new_theory("t");
/// let b = k.bool_ty();
/// let p = k.term_var("p", b).unwrap();
/// let real = k.assume(th, p).unwrap();
/// let stolen = real.concl;
/// ```
///
/// And a `Thm` cannot be mutated after the fact, because there is no way to
/// obtain a mutable handle on its parts:
///
/// ```compile_fail,E0616
/// # use adamas::Kernel;
/// let mut k = Kernel::new();
/// let th = k.new_theory("t");
/// let b = k.bool_ty();
/// let p = k.term_var("p", b).unwrap();
/// let mut real = k.assume(th, p).unwrap();
/// real.hyps.clear();
/// ```
///
/// Positive control: the very same setup, reaching the same data through the
/// accessors, compiles and runs. Without this, the three refusals above could
/// all be typos.
///
/// ```
/// # use adamas::Kernel;
/// let mut k = Kernel::new();
/// let th = k.new_theory("t");
/// let b = k.bool_ty();
/// let p = k.term_var("p", b).unwrap();
/// let real = k.assume(th, p).unwrap();
/// assert_eq!(real.concl(), p);
/// assert_eq!(real.hyps(), &[p]);
/// assert_eq!(real.theory(), th);
/// ```
#[derive(Clone, PartialEq, Eq, Debug)]
pub struct Thm {
    theory: TheoryId,
    hyps: Vec<Term>,
    concl: Term,
}

impl Thm {
    pub fn theory(&self) -> TheoryId {
        self.theory
    }

    pub fn hyps(&self) -> &[Term] {
        &self.hyps
    }

    pub fn concl(&self) -> Term {
        self.concl
    }
}

/// What [`Kernel::new_basic_type_definition`] leaves in the ledger.
#[derive(Clone, PartialEq, Eq, Debug)]
pub struct TypeDefinition {
    pub type_name: String,
    pub abs_rep: Thm,
    pub rep_abs: Thm,
}

/// A theory: a table of declared constants, and the ledgers of everything
/// asserted into it.
struct TheoryData {
    name: String,
    constants: HashMap<String, Ty>,
    axioms: Vec<Thm>,
    definitions: Vec<Thm>,
    type_definitions: Vec<TypeDefinition>,
}

// ---------------------------------------------------------------------------
// the kernel
// ---------------------------------------------------------------------------

/// The intern tables, the type signature, and the theories.
///
/// Ruby kept the intern tables and the type registry in process-global
/// constants and gave each `Theory` its own object. Here one `Kernel` owns all
/// of it. The relation is the same — a type constructor name, once declared, is
/// taken for every theory that shares these tables — but it is now scoped to a
/// value instead of to the process, so two independent developments in one
/// program no longer collide.
pub struct Kernel {
    types: Interner<types::TyKey, TyNode, Vec<Ty>>,
    terms: Interner<term::TermKey, TermNode, term::Info>,
    registry: HashMap<String, usize>,
    theories: Vec<TheoryData>,
    bool_ty: Ty,
    eq_ty: Ty,
}

impl Kernel {
    pub fn new() -> Self {
        let mut kernel = Kernel {
            types: Interner::new(),
            terms: Interner::new(),
            registry: HashMap::from([("bool".to_string(), 0), ("fun".to_string(), 2)]),
            theories: Vec::new(),
            bool_ty: Ty::PLACEHOLDER,
            eq_ty: Ty::PLACEHOLDER,
        };
        // Bootstrapped last in Ruby too, because they run the factories above.
        // These cannot fail: `bool` and `fun` are in the registry by
        // construction and the arities match.
        let bool_ty = kernel
            .ty_con("bool", &[])
            .expect("bool is declared with arity 0");
        let a = kernel.ty_var("A").expect("A is a non-empty name");
        let inner = kernel
            .ty_fun(a, bool_ty)
            .expect("fun is declared with arity 2");
        let eq_ty = kernel
            .ty_fun(a, inner)
            .expect("fun is declared with arity 2");
        kernel.bool_ty = bool_ty;
        kernel.eq_ty = eq_ty;
        kernel
    }

    /// The type of propositions.
    pub fn bool_ty(&self) -> Ty {
        self.bool_ty
    }

    /// A fresh theory. `=` is the one constant a theory is born knowing; the
    /// kernel's own rules are stated in terms of it.
    pub fn new_theory(&mut self, name: &str) -> TheoryId {
        let id = TheoryId(self.theories.len() as u32);
        self.theories.push(TheoryData {
            name: name.to_string(),
            constants: HashMap::from([(term::EQ_NAME.to_string(), self.eq_ty)]),
            axioms: Vec::new(),
            definitions: Vec::new(),
            type_definitions: Vec::new(),
        });
        id
    }

    pub fn theory_name(&self, id: TheoryId) -> &str {
        &self.theories[id.0 as usize].name
    }

    pub fn axioms(&self, id: TheoryId) -> &[Thm] {
        &self.theories[id.0 as usize].axioms
    }

    pub fn definitions(&self, id: TheoryId) -> &[Thm] {
        &self.theories[id.0 as usize].definitions
    }

    pub fn type_definitions(&self, id: TheoryId) -> &[TypeDefinition] {
        &self.theories[id.0 as usize].type_definitions
    }

    // --- the only door into `Thm` -----------------------------------------
    //
    // Private to `kernel`. `rules.rs` is a child module and may call it; no
    // code outside this directory can.

    fn sequent(&mut self, theory: TheoryId, hyps: Vec<Term>, concl: Term) -> Result<Thm> {
        if !self.is_proposition(concl) {
            return Err(Error::Rule(format!(
                "a conclusion must be a proposition: {}",
                self.term_to_string(concl)
            )));
        }
        for &h in &hyps {
            if !self.is_proposition(h) {
                return Err(Error::Rule("every hypothesis must be a proposition".into()));
            }
        }
        let mut hyps = hyps;
        hyps.sort_unstable();
        hyps.dedup();
        Ok(Thm {
            theory,
            hyps,
            concl,
        })
    }

    fn is_proposition(&self, term: Term) -> bool {
        self.closed(term) && self.type_of(term) == self.bool_ty
    }

    /// A theorem of another theory is not a theorem here.
    fn own(&self, theory: TheoryId, thm: &Thm) -> Result<()> {
        if thm.theory == theory {
            return Ok(());
        }
        Err(Error::Rule(format!(
            "a theorem proved in {} is not a theorem in {}",
            self.theory_name(thm.theory),
            self.theory_name(theory)
        )))
    }
}

impl Default for Kernel {
    fn default() -> Self {
        Self::new()
    }
}

impl Kernel {
    /// How many distinct types and terms the intern tables hold. Diagnostics
    /// only — nothing in the trusted path reads it.
    pub fn intern_sizes(&self) -> (usize, usize) {
        (self.types.len(), self.terms.len())
    }
}
