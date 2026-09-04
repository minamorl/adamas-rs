#!/usr/bin/env python3
"""Seed the roadmap epic and its sub-issues on minamorl/adamas-rs.

Run once. Idempotent by title: an issue whose title already exists is skipped.
Every sub-issue carries exactly one `tier:*` label — that is the routing signal
paseo reads — plus a lane, a size, and `local-ready` when the spec already
contains everything a 30B local model needs (file excerpt, acceptance, timeout).
"""
import json
import subprocess
import sys

REPO = "minamorl/adamas-rs"

# (title, labels, body)
ISSUES = []


def issue(title, labels, body):
    ISSUES.append((title, labels, body.strip() + "\n"))


T = "tier:"
COMMON_LOCAL = """
### Local-model contract (applies because this is `tier:coder-local`)
- The dispatcher **must** paste the referenced Ruby/Rust excerpt with line numbers into the spec. The model must not need to grep.
- One file touched (plus its test file). If a second source file is needed, stop and emit `INCOMPLETE`.
- Hard cap: 40 tool calls or `gtimeout 1800`. On cap: print `INCOMPLETE: <what is left>` and stop.
- Done means: `cargo test` green, `cargo clippy -- -D warnings` green, `scripts/kernel-frontier.sh` untouched (no file under `src/kernel/`).
"""

# --------------------------------------------------------------------------
# R0 infra
# --------------------------------------------------------------------------
issue("R0-1 Certificate JSON codec (hand-rolled, zero deps)",
      [T + "coder-cloud", "lane:R0-infra", "size:M"], """
Ruby `Adamas::Service::Codec` (lib/adamas/service/codec.rb, 185 lines) serialises terms as
`{form: var|const|app|lam|eq|not|and|or|imp|forall|exists, ...}` and certificates as
`{term, steps:[{path, rule, theta, types, conditions}], result, complete}`.

Port the **certificate** half to `src/codec.rs`: `Certificate -> String` and `&str -> Certificate`.
No serde (Cargo.toml has zero dependencies and stays that way; write a ~150-line JSON reader).

Acceptance
- round trip on every certificate emitted in `tests/rewriter_test.rs` and `tests/conversion_test.rs`
- a certificate produced by the Ruby gem (`fixtures/ruby/*.json`, see R1-7) parses and replays
- malformed input returns `Error::Codec(..)`, never panics (fuzz with 200 random truncations)

Blocks: R1-7, R7-2.
""")

issue("R0-2 Term/Thm JSON form (the `form:` encoding), reader + writer",
      [T + "coder-cloud", "lane:R0-infra", "size:M"], """
Second half of `Service::Codec`: the term encoding with `form` discriminator. Writer is a fold over
`Kernel::term_view`; reader must **refuse a formula sent as a variable name** (Ruby #41) — a `var`
whose name contains a space or any of `=¬∧∨⇒∀∃λ.()` is `Error::Codec`.

Acceptance: round trip every term in `tests/logic_syntax_test.rs`; refusal test for #41 pinned by message.
Depends on R0-1 (shares the JSON reader).
""")

issue("R0-3 Bench harness: rewrite+replay latency, logic install time, intern sizes",
      [T + "coder-local", "lane:R0-infra", "size:S", "local-ready"], """
Add `benches/` (plain `#[test]` with `--ignored`, no criterion — zero deps) printing three numbers:
1. `install_logic` wall time (Ruby: ~3 s, and it cannot run twice in one process — check Rust *can*)
2. one `rewrites` + `prove_certificate` round on the `connectives_test` fixture (Ruby: 0.10–0.22 ms)
3. `Kernel::intern_sizes()` after install

Excerpt to ship: `src/kernel/mod.rs:241-300` (`Kernel::new`, `new_theory`, `intern_sizes`) and
`tests/replay_test.rs` first test. Output format: one line `BENCH name=… value=… unit=…` each.
""" + COMMON_LOCAL)

issue("R0-4 `#![deny(missing_docs)]` on the public API",
      [T + "coder-local", "lane:R0-infra", "size:S", "local-ready"], """
Add `#![deny(missing_docs)]` to `src/lib.rs` and write the one-line docs the compiler asks for.
No behaviour change, no file under `src/kernel/` may change **except** doc comments — the
frontier script counts bytes, so this PR needs `kernel-frontier: doc comments only` in its message.
""" + COMMON_LOCAL)

issue("R0-5 Mutation script for replay refusals",
      [T + "review", "lane:R0-infra", "size:M"], """
README claims each refusal in `src/replay.rs` was verified by mutation (delete the check, exactly one
test turns red). Make that a script: `scripts/mutate-replay.sh` comments out each `return Err(..)`
in `replay.rs` in turn, runs `cargo test --test replay_test`, and asserts **exactly one** failure
per mutant. CI-optional (slow). Report the current matrix in the PR.
""")

issue("R0-6 CI: nightly OpenTheory `bool-1.37` replay (blocked on R6-5)",
      [T + "coder-local", "lane:R0-infra", "size:S", "blocked"], """
A scheduled workflow that fetches the six `bool-1.37` articles (curl recipe in Ruby
`docs/a-import-dossier.md`), replays them, and asserts 137 theorems / `axioms.len()==3` / 0 minted.
Waits on R6-5.
""")

# --------------------------------------------------------------------------
# R1 untrusted port (no new mathematics)
# --------------------------------------------------------------------------
issue("R1-1 DiscriminationTree port (Ruby 108 lines)",
      [T + "coder-local", "lane:R1-untrusted-port", "size:S", "local-ready"], """
Port `lib/adamas/discrimination_tree.rb` to `src/discrimination_tree.rs`. Preorder token trie,
instantiable variables collapse to `*`, retrieval follows exact edge and `*` edge (skipping a whole
subterm). Insertion order preserved in results.

Acceptance: port `test/discrimination_tree_test.rb`; **plus** the invariant test from Ruby's
`IndexTest`: retrieval ⊇ linear-scan matches on 500 random (pattern, term) pairs.
Ship the full Ruby file in the spec.
""" + COMMON_LOCAL)

issue("R1-2 Index port (Ruby 87 lines) — RuleSet fronted by the tree",
      [T + "coder-local", "lane:R1-untrusted-port", "size:S", "blocked"], """
Port `lib/adamas/index.rb`: a `RuleSet` view that answers `candidates(term)` through
`DiscriminationTree`. Depends on R1-1. Acceptance: `rewrites` results identical with and without the
index on every existing rewriter test (add a parity test).
""" + COMMON_LOCAL)

issue("R1-3 Calc port (Ruby 92 lines) — calculational chains",
      [T + "coder-local", "lane:R1-untrusted-port", "size:S", "local-ready"], """
Port `lib/adamas/calc.rb`: `a = b` (by rule) `= c` (by rule) … folded with `trans`. Pure derived
layer, no kernel. Ship the Ruby file + `test/calc_test.rb`.
""" + COMMON_LOCAL)

issue("R1-4 Printer parity with Ruby #39 / #47",
      [T + "coder-local", "lane:R1-untrusted-port", "size:S", "local-ready"], """
Two Ruby printer fixes to mirror in `src/kernel/term.rs::fmt` (printing only — mark the PR
`kernel-frontier: printer only, no rule touched`):
- #39 `=` binds looser than the connectives: `p ∧ q = r` prints as `(p ∧ q) = r`
- #47 a type constructor keeps its arguments: `list A` not `list`

Excerpt: `src/kernel/term.rs:525-584`. Acceptance: a `tests/printer_parity_test.rs` with the 12
strings from Ruby `test/printer_test.rb`.
""" + COMMON_LOCAL)

issue("R1-5 Pattern layer: de_morgan / quantifier / classical (Ruby 362 lines)",
      [T + "coder-cloud", "lane:R1-untrusted-port", "size:M"], """
Port `lib/adamas/patterns/{de_morgan,quantifier,classical}.rb` and `pattern.rb`: named
transformation patterns that emit certificates over the logic `RuleSet`. This is math-monster's
vocabulary (M4). Each pattern's test asserts the certificate **replays**, not just that a term
came out. Classical patterns require `ClassicalBundle`.
""")

issue("R1-6 Rewriter limit + permutative-rule parity check against Ruby fixtures",
      [T + "review", "lane:R1-untrusted-port", "size:S"], """
Confirm `DEFAULT_LIMIT`, the ordered path (`rewrites_with(.., ordered=true)`) and `is_permutative`
agree with Ruby `conversion/ordered.rb` on the 9 semiring clauses: same step count, same result
term string. Produce a table in the PR; open follow-ups for any mismatch.
""")

issue("R1-7 Cross-replay: Ruby-emitted certificates replay in Rust",
      [T + "coder-cloud", "lane:R1-untrusted-port", "size:M", "blocked"], """
Add `fixtures/ruby/` with certificates dumped from the Ruby gem (`Adamas::Service::Codec`) for
the logic `RuleSet` and load them in `tests/cross_replay_test.rs`. This is the first evidence the
two kernels agree on **what a certificate means**. Depends on R0-1.
""")

# --------------------------------------------------------------------------
# R2 numbers — the eleventh rule already exists in Rust; this is derived work
# --------------------------------------------------------------------------
issue("R2-1 `ind` type, INFINITY axiom, ONE_ONE / ONTO definitions",
      [T + "coder-cloud", "lane:R2-numbers", "size:M"], """
Port Ruby `lib/adamas/logic/numbers.rb:16-90` (`install`, `define_one_one`, `define_onto`,
`infinity_axiom`). `ind` via the existing `new_type`; INFINITY is the **third named axiom** and
opt-in like ETA/SELECT. `Kernel::axioms(th).len()` must read 3 after install and 2 before.
No kernel change is expected — `new_basic_type_definition` is already in `src/kernel/rules.rs:138`.
""")

issue("R2-2 Derive IND_SUC / IND_0 from INFINITY (existence via SELECT)",
      [T + "coder-cloud", "lane:R2-numbers", "size:L", "blocked"], """
Port `numbers.rb:90-205` (`derive_existence`, `missing_value`, `choose_missing`,
`prove_no_preimage`, `contradict_absence`, `define_selected`). Follows HOL Light `nums.ml:1-55`.
This is the hardest derivation in the lane: it needs `ClassicalBundle` (SELECT), `∃`-elimination and
`¬∀` pushing. Acceptance: `⊢ ∀m n. IND_SUC m = IND_SUC n ⇔ m = n` and `⊢ ∀n. ¬(IND_SUC n = IND_0)`
as `Thm`, hypothesis-free. Depends on R2-1.
""")

issue("R2-3 NUM_REP and the carving of `num` (the M5 gate, replayed in Rust)",
      [T + "coder-cloud", "lane:R2-numbers", "size:M", "blocked"], """
Port `num_representation.rb` (121) + `num_carver.rb` (83): define the inductive predicate
`NUM_REP` (`nums.ml:56`), prove `NUM_REP IND_0`, call `new_basic_type_definition("num", ...)`
and derive `mk_num (dest_num n) = n` / `NUM_REP r = (dest_num (mk_num r) = r)`.
Ruby's M5 dossier (`docs/m5-gate-dossier.md`) is the design source; the gate was opened by the
owner 2026-08-12 and does **not** need re-opening: Rust's kernel already has the rule.
Depends on R2-2.
""")

issue("R2-4 `0`, `SUC`, and the three Peano theorems",
      [T + "coder-cloud", "lane:R2-numbers", "size:M", "blocked"], """
Port `peano_prover.rb` (102) + `num.rb` (71): `ZERO_DEF`, `SUC_DEF` (`nums.ml:65,68`), then
`⊢ ¬(SUC n = 0)`, `⊢ SUC m = SUC n ⇔ m = n`. Depends on R2-3.
""")

issue("R2-5 Induction on `num`",
      [T + "coder-cloud", "lane:R2-numbers", "size:M", "blocked"], """
Port `num_induction_prover.rb` (140): `⊢ ∀P. P 0 ∧ (∀n. P n ⇒ P (SUC n)) ⇒ ∀n. P n`
(`nums.ml:96`), plus the derived tactic-shaped helper `by_induction(var, goal, base, step)`.
Depends on R2-4.
""")

issue("R2-6 Primitive recursion theorem (num_Axiom / num_RECURSION)",
      [T + "coder-cloud", "lane:R2-numbers", "size:L", "blocked"], """
`nums.ml:116,169`: `⊢ ∀e f. ∃!fn. fn 0 = e ∧ ∀n. fn (SUC n) = f (fn n) n`. Ruby has this in
`arithmetic.rb` (front part of its 1018 lines) as the general scheme A3 stage 1 needed. It needs
unique existence (`∃!`) — define it here if `logic/` does not yet have it. Depends on R2-5.
""")

issue("R2-7 `+` and `*` by recursion, `2 + 2 = 4` by certificate",
      [T + "coder-cloud", "lane:R2-numbers", "size:M", "blocked"], """
Define `+` and `*` through R2-6, register the four clauses as rules, and prove `⊢ 2 + 2 = 4` with
unary numerals `1..4` by an emitted+replayed certificate — the A2 acceptance test from Ruby
`test/arithmetic/`. Depends on R2-6.
""")

issue("R2-8a Binary numerals: BIT0 / BIT1 definitions and the zero-discrimination lemmas",
      [T + "coder-cloud", "lane:R2-numbers", "size:S", "blocked"], """
Port the kernel-facing half of `arithmetic/binary.rb`: `⊢ BIT0 n = n + n`, `⊢ BIT1 n = SUC (n + n)`,
`zero_bit0`, `zero_bit1` (gap ledger N-01, N-02, N-09). Depends on R2-7.
""")

issue("R2-8b Numeral encode/decode (untrusted, pure function)",
      [T + "coder-local", "lane:R2-numbers", "size:S", "local-ready"], """
Pure functions only, no kernel: `encode(u64) -> Vec<Bit>` (LSB-first BIT0/BIT1 with `_0`
terminator) and `decode(&[Bit]) -> u64`, gap ledger N-03 (`12 = BIT0 (BIT0 (BIT1 (BIT1 _0)))`).
Ship Ruby `Numeral.encode/decode` from `arithmetic/binary.rb` as the excerpt. Property test:
`decode(encode(n)) == n` for 10_000 values. Can land **before** R2-8a; the term builder that
consumes it comes with R2-9.
""" + COMMON_LOCAL)

issue("R2-9 Numeral evaluator: `3 * 4 = 12`, `127 + 896 = 1023` as certificates",
      [T + "coder-cloud", "lane:R2-numbers", "size:M", "blocked"], """
Binary carry theorem list + evaluator conversion (gap ledger N-04, N-05; Ruby did N-04 in 9 steps,
N-05 in 8). Certificates must be linear in digit count. Depends on R2-8a, R2-8b.
""")

issue("R2-10 Parity lemma and EXP / EVEN / ODD (gap ledger N-06, N-08, N-10)",
      [T + "coder-cloud", "lane:R2-numbers", "size:L", "blocked", "ahead-of-ruby"], """
Ruby measured that N-08 and N-10 both hang on one lemma: `⊢ ¬(m + m = SUC (n + n))`, which is a
**two-variable nested induction** its one-variable `by_induction` cannot reach. Do the two-variable
form here, then `EXP` (num→num recursion, `natural-exp-def-1.35`) and `EVEN/ODD` (num→bool
recursion). Rust gets here before Ruby; keep the theorem statements identical to the ledger so the
two can be compared later. Depends on R2-9.
""")

issue("R2-11 Order: `≤`, `<`, antisymmetry, totality, monotonicity (gap ledger O-01..O-10)",
      [T + "coder-cloud", "lane:R2-numbers", "size:L", "blocked", "ahead-of-ruby"], """
`natural-order-def-1.33`. `⊢ m ≤ n ⇔ ∃d. m + d = n`, then O-02..O-10 as listed in Ruby
`docs/gap-ledger.md` §2.2. Totality needs the two-variable induction from R2-10. This is what
unlocks GAP-S (side conditions for division) later. Depends on R2-10.
""")

issue("R2-12 Ledger: axioms == 3, kernel still 1,608 lines, after all of R2",
      [T + "review", "lane:R2-numbers", "size:S", "blocked"], """
Close-out check for the lane. Assert in one test: `axioms.len()==3` after full install; run
`scripts/kernel-frontier.sh` against the R2 merge base and confirm the only kernel diffs are the
doc/printer commits from R0-4/R1-4. Write the two sentences into README §Status.
""")

# --------------------------------------------------------------------------
# R3 algebra
# --------------------------------------------------------------------------
issue("R3-1 Commutative semiring: 9 laws by ordered rewriting (Ruby semiring.rb 382)",
      [T + "coder-cloud", "lane:R3-algebra", "size:M", "blocked"], """
Ruby A3 stage 2 (#40): with `ORDERED_REWR_CONV` + `term_order`, 9 of the 10 semiring clauses drop
out hypothesis-free. Rust already has `rewrites_with(ordered=true)` and `term_greater`, so this
lane is definitions + proofs + a `Semiring::laws()` bundle. Depends on R2-7.
""")

issue("R3-2 Polynomial normal form (Ruby polynomial.rb 174)",
      [T + "coder-cloud", "lane:R3-algebra", "size:M", "blocked"], """
Port `logic/polynomial.rb`: canonical form over ℕ (`normalizer.ml:555` disables the negation
path, so a semiring suffices). Every normalisation returns a `Thm`. Depends on R3-1.
""")

issue("R3-3 Numeral-aware term order (gap ledger N-07)",
      [T + "coder-local", "lane:R3-algebra", "size:S", "local-ready"], """
Extend `src/order.rs::dyn_greater` so binary numerals compare by value before falling back to the
structural lexicographic order. Excerpt: `src/order.rs:40-172` in full. Test: `m + n = n + m` applied
to `3 + 5` orients to `3 + 5` once and stops (no loop). No kernel file is touched.
""" + COMMON_LOCAL)

issue("R3-4 Ordered-rewriting loop guard parity (200 steps) test",
      [T + "coder-local", "lane:R3-algebra", "size:S", "local-ready"], """
Ruby's untrusted ordered rewriter caps at 200 steps to avoid the AC loop. Add
`tests/ordered_loop_test.rs`: the commutativity rule alone on `a + b` terminates within
`DEFAULT_LIMIT`, and a deliberately unorderable rule pair returns `Error::Limit`, not a hang.
Excerpt: `src/rewriter.rs` in full and `src/conversion.rs:140-175`.
""" + COMMON_LOCAL)

# --------------------------------------------------------------------------
# R4 patterns (math-monster's fifteen)
# --------------------------------------------------------------------------
issue("R4-0 Decide the seven priced-but-unproved patterns (Ruby A4: 3 classical + 5 proved + 7 priced)",
      [T + "plan", "lane:R4-patterns", "size:S"], """
Ruby `docs/a4-coverage-notes.md` lists 15 patterns: 3 classical, 5 proved, 7 priced but not proved.
Read the notes, and for each of the 7 write one line: *port as-is / needs R2-11 order / needs GAP-S /
drop*. Output is a table appended to this issue and new sub-issues under R4 for the ones kept.
Plan only — no code.
""")

issue("R4-1 Formal differentiation (algebraic, Ruby differentiation.rb 253)",
      [T + "coder-cloud", "lane:R4-patterns", "size:M", "blocked"], """
Port the formal-derivative pattern: identity the kernel replays, not analysis. Depends on R3-2.
""")

issue("R4-2 2×2 matrices without a new type (Ruby matrix2.rb 233)",
      [T + "coder-cloud", "lane:R4-patterns", "size:M", "blocked"], """
Port `linear/matrix2.rb`: matrices as 4-tuples of `num` terms, multiplication and determinant
identities as certificates. Depends on R3-2.
""")

# --------------------------------------------------------------------------
# R5 scale
# --------------------------------------------------------------------------
issue("R5-1 Measure certificate generation complexity (Ruby: exponent 2.15)",
      [T + "review", "lane:R5-scale", "size:S", "blocked"], """
Ruby measured certificate *generation* quadratic in step count (~1500–2500 nodes reach 100 ms).
Reproduce the measurement in Rust with the R0-3 harness on 100/300/1000/3000-step rewrites and
report the fitted exponent. Open a fix issue only if > 1.3. Depends on R0-3.
""")

issue("R5-2 Deep-term stress: 10k-node terms through `descend`, `fmt`, `match_pattern`",
      [T + "coder-local", "lane:R5-scale", "size:S", "local-ready"], """
`replay.rs::descend` is iterative on purpose; `term.rs::fmt` and `matching.rs::match_pattern` may
not be. Add `tests/deep_term_test.rs` building a 10_000-deep right-nested comb and calling all
three. If one overflows the stack, report which (do not fix in this issue).
Excerpt: `src/kernel/term.rs:525-584`, `src/matching.rs:24-60`.
""" + COMMON_LOCAL)

issue("R5-3 Install-twice: two `install_logic` on two theories in one `Kernel`",
      [T + "coder-local", "lane:R5-scale", "size:S", "local-ready"], """
Ruby cannot install a theory twice in one process (the type registry refuses `ind` the second time).
Test whether Rust can: `k.new_theory("a")`, `install_logic`, `k.new_theory("b")`, `install_logic`.
If it fails, this issue records the error and R5-4 is opened; if it passes, add the test and close.
Excerpt: `src/logic/mod.rs:1-80`, `src/kernel/types.rs:60-100`.
""" + COMMON_LOCAL)

# --------------------------------------------------------------------------
# R6 import / bridge — the decision lives in the epic
# --------------------------------------------------------------------------
issue("R6-1 OpenTheory article tokenizer + stack machine skeleton (reader_commands)",
      [T + "coder-local", "lane:R6-import-bridge", "size:S", "local-ready"], """
Port Ruby `import/article/reader_commands.rb` (54 lines) + the loop in `import/article.rb`: read
one command per line, dispatch `num`, `name`, `nil`, `cons`, `def`, `ref`, `remove`, `pop`,
`version`. No kernel calls yet — the stack holds `Object::{Num, Name, List, ...}` only.
Ship both Ruby files. Test: the 30-line article in Ruby `test/import/` parses to the expected stack.
""" + COMMON_LOCAL)

issue("R6-2 OpenTheory construction commands (types, terms, vars, consts)",
      [T + "coder-cloud", "lane:R6-import-bridge", "size:M", "blocked"], """
Port `import/article/construction_commands.rb` (46) + `name.rb` (64) + `signature.rb` (26):
`varType`, `opType`, `var`, `const`, `constTerm`, `varTerm`, `app`, `abs`, plus the namespace
mapping `Data.Bool.T -> T` etc. Depends on R6-1.
""")

issue("R6-3 OpenTheory inference commands onto the ten rules",
      [T + "coder-cloud", "lane:R6-import-bridge", "size:M", "blocked"], """
Port `inference_commands.rb` (68) + `environment.rb` (45) + `unfold.rb` (41): `refl`, `trans`?,
`appThm`, `absThm`, `betaConv`, `assume`, `eqMp`, `deductAntisym`, `subst`, `axiom`, `thm`,
`defineConst`, `defineTypeOp`. `axiom` must be **counted** — the acceptance test asserts how many
were minted. Depends on R6-2.
""")

issue("R6-4 Acceptance: `bool-1.37` replays — 71,426 commands, 137 theorems, axioms==3, 0 minted",
      [T + "review", "lane:R6-import-bridge", "size:M", "blocked"], """
Ruby's measured figures for the six `bool-1.37` articles. Reproduce in Rust with the article cache
(`~/.cache/adamas-a-import/articles`, curl recipe in Ruby `docs/a-import-dossier.md`). Record wall
time and RSS next to Ruby's. Depends on R6-3. Unblocks R0-6.
""")

issue("R6-5 Bench: the 47-article chain to ℝ (1,785,680 commands; Ruby 26.2 s / 190 MB)",
      [T + "review", "lane:R6-import-bridge", "size:L", "blocked"], """
Replay the whole chain. Target: < 5 s, < 100 MB, ordered field theorems come out as `Thm`, final
axiom count = 3 + the one named bridging assumption Ruby documented. Depends on R6-4.
""")

issue("R6-6 A-bridge stage 1 port: `num ≃ Number.Natural.natural`, 308 theorems' route",
      [T + "coder-cloud", "lane:R6-import-bridge", "size:L", "blocked"], """
Ruby #51 landed the bijection (both types are carved from the same `ind` via `NUM_REP`/`IND_SUC`/
`IND_0`, so the isomorphism is by construction, not by induction) and a transport that routes 308
imported theorems onto adamas's own `num`. Port `bridge/{isomorphism,representation,transport,
rename,vocabulary,support}.rb` (~900 lines). Depends on R2-5 and R6-4.
Decision context: the epic §Bridge.
""")

# --------------------------------------------------------------------------
# R7 service — the endpoint 結衣 calls
# --------------------------------------------------------------------------
issue("R7-1 Protocol doc: JSONL over stdio, request/response/refusal shapes",
      [T + "plan", "lane:R7-service", "size:S"], """
Read Ruby `service/{session,profile,at_path,server}.rb` and write `docs/protocol.md`: one request
per line, `{op, theory, args}` in, `{ok, thm|certificate|error}` out, and the three refusals the
Ruby service makes (#41 formula-as-name, no-op says so, unknown op). Plan only; R7-2..4 implement.
""")

issue("R7-2 Session: named theories, named theorems, `at_path` addressing",
      [T + "coder-cloud", "lane:R7-service", "size:M", "blocked"], """
Port `session.rb` (243) + `at_path.rb` (92). Depends on R0-2, R7-1.
""")

issue("R7-3 `adamas-serve` binary (stdio JSONL, zero deps)",
      [T + "coder-cloud", "lane:R7-service", "size:M", "blocked"], """
`src/bin/adamas-serve.rs`. Boot once, keep the theory (Ruby's constraint #2: install is the
expensive part). Depends on R7-2.
""")

issue("R7-4 Profile: time and step budget per request (Ruby profile.rb)",
      [T + "coder-local", "lane:R7-service", "size:S", "blocked"], """
Port `service/profile.rb` (95): a per-request budget `{max_steps, max_ms}` and the refusal it
produces. Depends on R7-3.
""" + COMMON_LOCAL)

issue("R7-5 A6: wire `adamas-serve` behind the yui gateway (結衣の数学器官)",
      [T + "coder-cloud", "lane:R7-service", "size:M", "blocked"], """
The endpoint. yui calls `adamas-serve` as a subprocess; every mathematical answer in conversation
carries the certificate the kernel replayed. Lives partly in `repos/yui`; this issue tracks the
adamas-rs side (stable protocol, versioned). Depends on R7-3, R2-9.
""")

# --------------------------------------------------------------------------
# R8 docs
# --------------------------------------------------------------------------
issue("R8-1 ROADMAP.md for adamas-rs (mirror of the epic, kept current)",
      [T + "coder-local", "lane:R8-docs", "size:S", "local-ready"], """
Write `ROADMAP.md` from the epic body verbatim, with a "Where we actually are" table (kernel lines,
tests, deps=0, axioms) that is **measured** by `scripts/status.sh` (new, 20 lines: wc, cargo test
count, grep for new_axiom sites). Re-run the script in every roadmap PR.
""" + COMMON_LOCAL)

issue("R8-2 docs/ja port (8 files) from the Ruby gem, Rust examples substituted",
      [T + "coder-cloud", "lane:R8-docs", "size:M"], """
Ruby `docs/ja/{01-what-it-is,02-first-proof,03-how-it-works,04-usage,05-design,06-troubleshooting,
glossary,index}.md`. Same text where the design is shared; Rust snippets must be doctests.
""")

issue("R8-3 docs/internals-for-ai.md: how an LLM should drive this crate",
      [T + "plan", "lane:R8-docs", "size:S"], """
Port and update Ruby `docs/internals-for-ai.md`: the invariants a model must never violate (no
`Thm` outside `kernel`, certificates are plans not proofs, `axiom` is counted), the module map, and
the tier labels used on this tracker so a paseo worker can self-route.
""")


EPIC_TITLE = "EPIC: adamas-rs roadmap — from ported kernel to 結衣's mathematics organ"
EPIC_BODY = """
## North star (unchanged from the Ruby gem)
**A symbolic mathematics system that cannot lie, with 結衣 as its first user.** Every transformation
a learner sees is a `Thm`; conversational mathematics arrives with a certificate the kernel replayed;
the trusted core stays small enough for one person to read.

## Where we actually are (measured 2026-09-04, `8bddd2c`)
| | |
|---|---|
| kernel (`src/kernel/`) | 1,608 lines, unchanged since the port; enforced by `scripts/kernel-frontier.sh` in CI |
| above the kernel | 4,932 lines (`certificate`, `replay`, `conversion`, `rewriter`, `witness`, `matching`, `order`, `logic/*`, `classical`, `taut`, `simp`) |
| tests | 201 `#[test]` + doctests incl. `compile_fail` with pinned error codes |
| deps | 0 |
| axioms | ETA, SELECT opt-in; INFINITY **not yet** (no `ind`, no `num`) |
| ahead of Ruby | the forgery boundary is real (module privacy), `descend` is iterative |
| behind Ruby | numbers, algebra, patterns, discrimination tree, OpenTheory reader, A-bridge, service |

Ruby (`minamorl/adamas`, 10,045 lib lines) is at A5 landed, A-bridge stage 1 landed (#51), gap
ledger (#52), numerals (#53). Rust is at "logic + classical + taut". The gap is **exactly the
untrusted mathematics**, and it is the point of the design that porting it grows nothing trusted.

## The bridge decision — decided, not recommended
Question: does adamas-rs build a bridge to an existing proof system?

**Yes, one bridge, one direction: OpenTheory articles → adamas-rs, by replay.** Reasons, measured
in Ruby and inherited here:
1. It is the strongest test the kernel can get. `bool-1.37` is 71,426 commands; the chain to ℝ is
   1,785,680. No hand-written test suite competes with replaying somebody else's development
   through our ten rules and counting minted axioms (target: 3 named + 1 documented assumption).
2. It buys ℝ without writing analysis. Ruby measured the ordered field coming out as `Thm`s.
3. The two-ℕ problem is already solved by construction (Ruby #51): OpenTheory carves `natural` out
   of *our* `ind` through the same `NUM_REP`, so the bijection is definitional and 308 theorems
   route onto our `num`. We port that; we do not re-derive it.

**No** to everything else, stated so nothing downstream re-opens it:
- **No export** to Lean / Isabelle / Metamath / Coq. Different logics (dependent types, ZF, first-
  order); an exporter would be a second trusted artefact nobody reads. If a consumer wants our
  theorems, they consume our *certificates* and replay them in their own checker (R0-1 makes them
  JSON). Certificates are the bridge, not a translator.
- **No "interpret"** (satisfying OpenTheory's `natural-def` exports from our own `num` instead of
  replaying). Ruby priced it: 850 assumptions above `natural-def`, no order, no division. Same
  price here.
- **No HOL Light OCaml linkage**, no FFI. Zero dependencies is a spec, not a habit.
- Kernel growth for any of this is a **kill condition**. The Rust kernel already contains
  `new_basic_type_definition`; the eleventh rule does not need a second gate. Any other `src/kernel/`
  diff for R2–R7 means the LCF bet failed and the design goes back on the table.

## Lanes (dependency order; parallel where no arrow)
```
R0 infra ──┬─► R1 untrusted port ──► R3 algebra ──► R4 patterns
           │                          ▲
           └─► R2 numbers ────────────┘──► R5 scale
R6 import/bridge (parallel from R0; R6-6 waits on R2-5)
R7 service (waits on R0-2 + R2-9)          R8 docs (anytime)
```
Each sub-issue carries one `tier:*` label — the routing signal for paseo:

| label | who runs it | what it looks like |
|---|---|---|
| `tier:plan` | Opus-class / plan agent | a decision, a dossier, a table. No code. |
| `tier:coder-cloud` | Claude Code / Codex / yui coder subagent | multi-file, new module, derivations |
| `tier:coder-local` | MacBook 30B (muse-glimmer) under `gtimeout` | one function, one file, **spec ships the excerpt with line numbers**, hard tool-call cap, `INCOMPLETE` protocol |
| `tier:review` | gpt-reviewer / yui | measure, mutate, compare, write the table |
| `tier:human-gate` | owner | kernel frontier, axioms, protocol freeze |

`local-ready` = the spec already contains everything the local model needs. Measured on paint
Lane A (2026-09-03): a 30B model cannot go from exploration to edit on a 4,400-line file; it can
when the excerpt is pasted and the lane is one function. Every `tier:coder-local` issue here is
written to that constraint; the ones without `local-ready` still need the excerpt pasted by the
dispatcher (usually because the referenced file does not exist until a sibling lands).

## Kill conditions
1. Any `src/kernel/` change for proving power → stop, reopen design.
2. `axioms.len()` after full install ≠ 3 (+1 documented for the ℝ chain) → a lane minted something.
3. A certificate that replays in Ruby and not in Rust (or vice versa) after R1-7 → the two kernels
   disagree on meaning; fix before anything else lands.

## Order of first pull
R0-1, R0-3, R1-1, R2-1, R6-1, R8-1 are unblocked now. R1-1 / R0-3 / R2-8b / R6-1 are the
`local-ready` probes: dispatch them to the MacBook first and record whether they land.

## Sub-issues
(filled in by `scripts/issues-seed.py`)
"""


def gh(*args, input=None):
    r = subprocess.run(["gh", *args], capture_output=True, text=True, input=input)
    if r.returncode != 0:
        print(r.stderr, file=sys.stderr)
        raise SystemExit(f"gh failed: {' '.join(args[:3])}")
    return r.stdout.strip()


def existing_titles():
    out = gh("issue", "list", "-R", REPO, "--state", "all", "--limit", "300", "--json", "title,number,url")
    return {i["title"]: i for i in json.loads(out)}


def main():
    have = existing_titles()
    created = []
    for title, labels, body in ISSUES:
        if title in have:
            created.append((title, have[title]["number"], have[title]["url"]))
            print("skip", title)
            continue
        url = gh("issue", "create", "-R", REPO, "--title", title, "--body", body,
                 "--label", ",".join(labels))
        num = int(url.rstrip("/").split("/")[-1])
        created.append((title, num, url))
        print("made", num, title)
    lines = []
    lane = None
    for title, num, url in created:
        this_lane = title.split("-")[0]
        if this_lane != lane:
            lane = this_lane
            lines.append(f"\n### {lane}")
        lines.append(f"- [ ] #{num} {title}")
    body = EPIC_BODY.replace("(filled in by `scripts/issues-seed.py`)", "\n".join(lines))
    if EPIC_TITLE in have:
        gh("issue", "edit", "-R", REPO, str(have[EPIC_TITLE]["number"]), "--body", body)
        print("epic updated", have[EPIC_TITLE]["url"])
    else:
        url = gh("issue", "create", "-R", REPO, "--title", EPIC_TITLE, "--body", body,
                 "--label", "epic,tier:plan")
        print("epic", url)


if __name__ == "__main__":
    main()
