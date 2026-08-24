# adamas

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

## Status

The kernel is complete and tested (33 behaviour tests, 5 doctests). The layers
*above* the kernel in the Ruby original — the rewriter, the certificate replay,
`logic/`, `bridge/`, `service/` — are not ported yet. The next piece is
certificate replay, which is what makes an untrusted rewriter's claims checkable.

## Building

Note for this machine: Homebrew's `rust` links against Homebrew's `libLLVM` and
SIGABRTs when `llvm` is upgraded out from under it. Use a rustup toolchain:

```sh
export PATH="$HOME/.rustup/toolchains/stable-aarch64-apple-darwin/bin:$PATH"
cargo test
```

## License

MIT.
