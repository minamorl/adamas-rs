# adamas

[![CI](https://github.com/minamorl/adamas-rs/actions/workflows/ci.yml/badge.svg)](https://github.com/minamorl/adamas-rs/actions/workflows/ci.yml)
[![Rust 2021](https://img.shields.io/badge/Rust-2021-CE422B.svg)](https://www.rust-lang.org/)
[![License: MIT](https://img.shields.io/badge/License-MIT-blue.svg)](LICENSE)

**An LCF-style proof kernel. Theorems you cannot forge, terms you cannot mistype.**

A Rust port of the trusted core of [adamas](https://github.com/minamorl/adamas).

## Why this port exists

The Ruby original leads with *"Theorems you cannot forge"* — and then, in a
section called **What the kernel does not guarantee**, says the honest thing
first:

> **Ruby has no real privacy.** `send`, `Marshal` and `ObjectSpace` defeat any
> scheme, and Adamas does not pretend otherwise.

Its `test/forgery_test.rb` carries a test named
`test_a_well_formed_forgery_is_only_stopped_by_the_privacy`: a sequent that
passes every invariant the kernel checks, and is stopped by nothing but a
porous `private_class_method`.

Here the boundary is the module system. `Thm`'s fields are private to `kernel`
and its children. Outside that module there is no constructor and no reflective
back door. **A `Thm` that exists was derived.** The headline claim is true
rather than aspirational — that is the entire reason this port is an
improvement and not a translation.

The refusals are tested as `compile_fail` doctests with their **error codes
pinned** (`E0451`, `E0616`), because a bare `compile_fail` passes when the
snippet fails for *any* reason, and a typo would then read as a closed door. A
positive control compiles the same setup through the accessors, so the three
refusals are known to be otherwise valid code.

## What it is

`bool` and `fun`, simply-typed lambda terms with de Bruijn indices, and the ten
primitive rules of HOL Light's `fusion.ml`:

```
REFL   TRANS   MK_COMB   ABS   BETA
ASSUME   EQ_MP   DEDUCT_ANTISYM_RULE   INST   INST_TYPE
```

plus the five gates that make a theorem out of nothing: `new_constant`,
`new_axiom`, `new_basic_definition`, `new_type`, `new_basic_type_definition`.

```rust
use adamas::{Kernel, Result};

fn main() -> Result<()> {
    let mut k = Kernel::new();
    let th = k.new_theory("demo");
    let bool_ty = k.bool_ty();
    let v = k.term_var("v", bool_ty)?;
    let q = k.term_var("q", bool_ty)?;

    // BETA is primitive only for the trivial redex. The general case is
    // *derived* from BETA + INST rather than trusted.
    let body = k.term_eq(v, v)?;
    let lam = k.term_abs(v, body)?;
    let trivial = k.term_comb(lam, v)?;
    let base = k.beta(th, trivial)?;

    let theta = std::collections::BTreeMap::from([(v, q)]);
    let derived = k.inst(th, &theta, &base)?;
    assert_eq!(k.thm_to_string(&derived), "⊢ (λv. «0» = «0») q = (q = q)");
    Ok(())
}
```

### Terms are hash-consed

Alpha-equivalence is one machine-word comparison, not a recursive walk: the
binder's display name is deliberately outside the intern key, so `λx. x` and
`λy. y` are not merely equal, they are the same node.

Where Ruby had to bolt "structural equality is object identity" onto its nodes
with a mixin overriding `==`, `eql?` and `hash`, here a node *is* its rank in
the intern table — a `u32` newtype whose equality is a word comparison by
construction. There is nothing to override and nothing to get wrong.

## What the kernel does *not* guarantee

Being precise about this is part of the design, not a caveat bolted on. Three
of the Ruby original's four limitations survive unchanged; the first one is the
one this port removes.

* ~~Ruby has no real privacy.~~ **Closed.** See above.
* **The kernel is not verified**, it is small — 898 lines of Ruby became this.
  That is the entire argument for it, and it is the same argument HOL Light
  makes.
* **`bool` and `fun` are the whole type language** until `new_type` grows it.
* **Consistency is your problem once you call `new_axiom`.** The kernel will
  happily derive everything from a contradiction you asserted.

## Certificate replay

The point of a small kernel is that everything above it can be *untrusted*. A
rewriter emits a **certificate** — a starting term, a list of claimed steps, and
the term it says they reach — and `prove_certificate` rebuilds it out of the ten
primitives or refuses. On its own a certificate proves nothing; it is a plan.

```rust
# use adamas::*;
# use std::collections::BTreeMap;
// ⊢ f a = f b, from `ab: ⊢ a = b` applied under `rand`.
let cert = Certificate::new(fa, vec![Step::new(vec![PathStep::Rand], "ab")], fb, true);
let thm = k.prove_certificate(th, &cert, &rules)?;   // ⊢ f a = f b
# Ok::<(), Error>(())
```

Positions under a binder are opened with a variable named from the *position*
(`_0`, `_1`, …), never from the binder's display name — a display name is
whichever alpha-variant happened to be interned first in this process, and a
certificate has to mean the same thing wherever it is replayed.

The tests that matter are the refusals: lying about the result, about the
position, about the substitution, naming a rule that does not exist, taking a
path a term does not have, or offering the wrong number of condition
certificates. Each is checked for its specific message rather than for "some
error", and each was verified by mutation — deleting the corresponding check in
`replay.rs` turns exactly the relevant tests red and leaves the rest green.

One of those mutations is worth recording. With replay's own
"does the rule instantiate to what is actually at that position?" check deleted,
a bad certificate still produced no theorem: the kernel refused it at
`TRANS: f a and f b are not the same term`. **The untrusted layer being wrong
cannot make a false theorem — that is the entire LCF thesis, observed rather
than asserted.**

## The logic layer

`T`, `∧`, `⇒`, `∀`, `F`, `¬`, `∨` and `∃`, each a `new_basic_definition` and
nothing else, with their introduction and elimination rules derived from the
ten primitives. No axiom is asserted anywhere: `Kernel::axioms` stays empty
through the whole layer, and every connective's tests say so, because a theorem
obtained by asserting it would satisfy every other assertion those tests make.

Classical logic is deliberately separate. `logic::classical::install` declares
`@ : (A → bool) → A` and asserts exactly two opt-in axioms, ETA followed by
SELECT. It then derives `⊢ ∀p. p ∨ ¬p` from SELECT by Diaconescu's construction;
excluded middle is not a third axiom.

```rust
# use adamas::*;
# use adamas::logic::{classical, taut};
let mut k = Kernel::new();
let th = k.new_theory("logic");
let logic = k.install_logic(th)?;
assert!(k.axioms(th).is_empty());                       // constructive by default
assert!(!k.has_constant(th, "@"));
assert_eq!(logic.rules.len(), 16);                      // derived simp rules

let choice = classical::install(&mut k, th, &logic)?;  // ETA, then SELECT
let bool_ty = k.bool_ty();
let p = k.term_var("p", bool_ty)?;
let formula = k.excluded_middle(th, p)?;
let em = taut::prove(&mut k, th, &logic, &choice, formula)?
    .expect("excluded middle is a tautology");
assert_eq!(em.concl(), k.excluded_middle(th, p)?);       // ⊢ p ∨ ¬p
assert!(em.hyps().is_empty());
assert_eq!(k.axioms(th).len(), 2);                       // EM was derived
# Ok::<(), Error>(())
```

`∧` is HOL Light's pair-selector encoding, `⇒` is `p ∧ q = p`, and `∀P` is `P`
being the constantly-true predicate — so `MP` is a projection, `DISCH` is
`DEDUCT_ANTISYM_RULE` between the two halves of an equation, and `SPEC` is
application. Between `p` and `p = T` the traffic goes through `eqt_intro` and
`eqt_elim`, which is why `⊢ (p = T) = p` has to exist before any of it does.

`GEN`'s side condition — the variable must be free in no hypothesis — is not
checked in `gen`. It does not need to be: the abstraction it performs is the
kernel's `ABS`, which refuses.

`F` is `∀p. p`, negation is implication to `F`, and `∨` and `∃` use their
intuitionistic continuation encodings. `CONTR`, `DISJ_CASES`, and `CHOOSE` are
therefore derived rules too; in particular, `CHOOSE` inherits its
eigenvariable condition from the same kernel `ABS` check.

## The kernel frontier

There is one claim in this README that `cargo test` cannot check. Add a line
inside `src/kernel/` that hands out `Thm { theory, hyps, concl }` and every
behaviour test in the crate still passes, doctests included — measured. What
such a line breaks is a compile-time boundary, and a test observes values.

So `scripts/kernel-frontier.sh` reads the diff instead. A change under
`src/kernel/` has to be said out loud in a commit message:

```
kernel-frontier: <why>
```

Without that line it fails, however green the tests are. CI runs it on every
pull request. The kernel has not moved since the port: 1,608 lines.

## Status

Ported and tested: the kernel, certificate replay with conditional rewriting,
the proof-producing rewriter, the compile-time forgery boundary, and the full
constructive logic layer — `T`, `∧`, `⇒`, `∀`, `F`, `¬`, `∨`, and `∃`. Logic
installation now also derives Ruby's complete 16-rule `RuleSet` in registration
order; every member is hypothesis-free and the theory remains axiom-free.

The opt-in classical layer adds polymorphic choice, the ETA and SELECT axioms,
`SELECT_RULE`, and Diaconescu-derived excluded middle. On top of it, `taut`
proof-produces propositional tautologies by splitting at most 12 boolean atoms,
simplifying each leaf through the logical `RuleSet`, and replaying the emitted
certificates. A failed search returns `None`, not a theorem.

Not ported: the mathematics above the logic layer — `bridge/`, `service/`, and
the pattern layer. Those are the clever, heuristic, unverified part, which is
precisely why they can wait: a certificate from any of them is checkable by
what is already here.

## Building

Note for this machine: Homebrew's `rust` links against Homebrew's `libLLVM` and
SIGABRTs when `llvm` is upgraded out from under it. Use a rustup toolchain:

```sh
export PATH="$HOME/.rustup/toolchains/stable-aarch64-apple-darwin/bin:$PATH"
cargo test
```

## License

MIT.
