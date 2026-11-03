# spec-derive-spike

A small spike that proves out a **workflow**, not a domain:

1. **Specify in Lean 4.** Each example has types, an obviously correct `reference`, an
   `Invariant` (as a `Prop` plus a `Bool` checker), an optimized `plan`, and
   `run := if checkInvariant s then plan s else reference s`.
2. **Prove.** The key theorem is `Invariant s → plan s = reference s`. The proofs also show that
   the checker is sound and complete, that `run = reference`, and that the integer bounds keep
   OCaml `int` from overflowing. The kernel checks all of this on every `lake build`.
3. **Generate plain OCaml.** `Emit.lean` reads the *elaborated* definitions (the same terms the
   theorems are about) from the compiled environment and prints `gen/<name>_gen.ml{,i}`. It is
   ordinary text generation over a small, documented subset. Anything else is rejected.
4. **Check for drift.** `scripts/check-gen.sh` (and CI) regenerates into a temp dir and fails
   if `gen/` differs.
5. **Differential-test** the generated OCaml against a Lean oracle executable, and `plan`/`run`
   against `reference`, on seeded, boundary-biased, partly invariant-violating inputs.
6. **Benchmark** `reference` against `plan`, and also time `check_invariant` and `run`.
7. **Keep the invariant true by construction** where it pays. `running_sum` has a generated,
   proved invariant-preserving `push`, behind a small typed OCaml wrapper, so the O(1) plan
   needs no check.

Two examples, chosen to differ in structure:

| example         | reference                 | invariant                    | plan                     |
|-----------------|---------------------------|------------------------------|--------------------------|
| `running_sum`   | sum all amounts, O(n)     | cached running totals agree  | read head's total, O(1)  |
| `sorted_lookup` | linear scan for key, O(n) | keys strictly increasing     | exit at first larger key |

## Build from a clean clone

Prerequisites: [elan](https://github.com/leanprover/elan) (it installs the Lean version pinned
in `lean-toolchain`), plus OCaml 5.x with opam.

```sh
opam install dune alcotest
scripts/verify.sh     # lake build, proof gate, generator reject tests, drift check,
                      # dune build, differential test; prints "verify: PASS"
scripts/bench.sh      # optional: benchmark tables
```

Other entry points:
- `lake exe emit gen gen` regenerates the OCaml.
- `SEED=7 CASES=10000 scripts/difftest.sh` reruns the differential test with another seed.
- `scripts/test-reject.sh` checks that the generator refuses out-of-subset Lean.

## Layout

```
SpecDerive/<Ex>/Spec.lean    definitions + theorem statements (`def Foo : Prop`)
SpecDerive/<Ex>/Proofs.lean  proofs (kept apart so statements can be reviewed and locked)
SpecDerive/Check.lean        `example : Statement := proof` per statement + `#print axioms`
SpecDerive.lean              library root: imports specs only (generator/oracle never see proofs)
Emit.lean                    generator (`lake exe emit`); subset documented at the top
RejectCases.lean             out-of-subset definitions the generator must refuse
Oracle.lean                  Lean oracle exe: input line -> "<reference> <check> <bounded>"
gen/                         generated OCaml (checked in, drift-checked)
harness/                     generic: Subject signature, Pick, Diff driver, Bench
wrapper/                     hand-written typed wrapper (`Running_sum_t`): private type, no-check total
subjects/                    per-example adapters (input generators, oracle line format)
test/difftest.ml             alcotest runner for the differential test
test/push_seq.ml             push-sequence differential test (through the wrapper)
bench/bench.ml               benchmark runner
bench/workflow.ml            whole-workflow benchmark: push+total vs. reference vs. checked run
scripts/                     verify, proof-gate, check-gen, test-reject, difftest, bench
docs/adding-an-optimization.md   the procedure for a new triple
```

## What is proved, what is tested, what is trusted

**Proved (Lean kernel), about the Lean model only:**

| theorem | running_sum | sorted_lookup |
|---|---|---|
| cache consistency → `plan = reference` | `plan_correct` | `plan_correct` (keys sorted) |
| checker sound / complete for the invariant (consistency and value bounds) | `check_sound`, `check_complete` | same (keys sorted) |
| `run = reference` (all inputs) | `run_correct` | `run_correct` |
| OCaml `int` bounds | `bounded_tail`, `reference_fits`, `check_site_fits` | none needed (0 arithmetic sites) |
| `push` preserves the invariant (consistency and bounds) | `push_preserves`, `push_preserves_consistent` | none |
| `push` semantics | `push_tail`, `push_reference`, `push_total` | none |
| `push` stays in range | `push_values_bounded`, `push_site_fits`, `reference_fits_inv` | none |

`#print axioms` (from `scripts/proof-gate.sh`, Lean 4.35.0); no `sorry`:

```
'RunningSum.plan_correct' does not depend on any axioms
'RunningSum.check_sound' depends on axioms: [propext, Classical.choice, Quot.sound]
'RunningSum.check_complete' depends on axioms: [propext, Classical.choice, Quot.sound]
'RunningSum.run_correct' depends on axioms: [propext, Classical.choice, Quot.sound]
'RunningSum.bounded_tail' depends on axioms: [propext, Quot.sound]
'RunningSum.reference_fits' depends on axioms: [propext, Quot.sound]
'RunningSum.check_site_fits' depends on axioms: [propext, Quot.sound]
'RunningSum.push_preserves' depends on axioms: [propext, Quot.sound]
'RunningSum.push_preserves_consistent' depends on axioms: [propext, Quot.sound]
'RunningSum.push_tail' depends on axioms: [propext, Quot.sound]
'RunningSum.push_reference' depends on axioms: [propext, Quot.sound]
'RunningSum.push_total' depends on axioms: [propext, Quot.sound]
'RunningSum.push_values_bounded' depends on axioms: [propext, Quot.sound]
'RunningSum.push_site_fits' depends on axioms: [propext, Quot.sound]
'RunningSum.reference_fits_inv' depends on axioms: [propext, Quot.sound]
'SortedLookup.plan_correct' depends on axioms: [propext, Quot.sound]
'SortedLookup.check_sound' depends on axioms: [propext, Quot.sound]
'SortedLookup.check_complete' depends on axioms: [propext, Quot.sound]
'SortedLookup.run_correct' depends on axioms: [propext, Quot.sound]
```

`Classical.choice` (accepted by the gate, as in the formal-spec skill) remains in three theorems:
`check_sound`, `check_complete` and `run_correct`. It comes from Lean core's decidable equality on
`Int` (`beq_iff_eq`; even a `decide_eq_true_iff` route uses it), which the checker's `==`
relies on. Removing it would mean rewriting the checker without `==`, which is not cheap. The
other source, `omega` on a conjunction goal, was cheap to remove: the bound theorems now split
the goal first and are classical-free.

**Tested, not proved:** that the generated OCaml behaves like the Lean definitions. This is
covered by the differential test against the Lean oracle, plus `plan = reference` whenever the
checker holds, and `run = reference` always.

**Trusted base (not verified by anything here):**
- `Emit.lean`, the generator. It is tested by the difftest and the reject cases. One mitigation:
  it translates elaborated terms, not source text, and it requires every operator instance to be
  definitionally equal to the standard one.
- The OCaml compiler and runtime. Also the Lean compiler, which builds the oracle: the oracle
  runs compiled Lean, not the kernel.
- The hand-written adapters in `subjects/`: input generators and line formats.
- The typed wrapper `wrapper/running_sum_t.ml` (6 lines). Every `t` satisfies the full invariant,
  consistency and value bounds. That rests on the generator being faithful, which is tested,
  not proved.
- Evaluation order in the checker. `check_from` range-checks an entry before the addition that
  uses it (`&&` short-circuits), so the checker cannot overflow on arbitrary input. This is
  read off the code; `CheckSiteFits` assumes it.
- The `Bounded` precondition of `reference` and `run` (and of `sorted_lookup`). **It is not
  checked at runtime.** The generated `.mli` documents it, and the difftest asserts (through the
  oracle) that every generated input is inside it. The wrapper path (`of_list`, `push`,
  `total`) no longer needs it: the invariant carries the bounds.
- Coverage of arithmetic sites by `Fits` theorems. The generator counts the sites per function
  and prints them in the header, but matching each site to a theorem is done by review.

## Integer bounds: Lean `Int` vs. OCaml `int`

Lean `Int` is unbounded. OCaml `int` is 63-bit: `[-2^62, 2^62-1]`. The approach:

- Each spec defines `Bounded` as the input domain of the generated code. For `running_sum` that
  is ≤ 1000 entries, |x| ≤ 10^12 and |cum| ≤ 10^15.
- It also proves one `Fits` theorem per Int arithmetic site in the emitted functions, plus
  `BoundedTail`, so every recursive call stays in the domain. For example, `reference_fits`
  proves |reference s| ≤ 10^12 · length ≤ 10^15.
- The generator prints the site inventory in the header
  (`reference: 1, check_from: 1, push: 1`), which makes a missed site visible in review.
- The generator rejects `Nat` (truncated subtraction), `/` and `%` (Lean's `Int` division is
  Euclidean, OCaml's truncates), and literals that don't fit.

It was clean for these examples: `omega` closes every bound with literal constants. The weak spot
is that "one theorem per site" is a convention the tools don't enforce.

## Keeping the invariant true by construction

Checking on every call (`run`) cancels most of the plan's gain. So `running_sum` also has
`push x s : Option (List Entry)`, which sets the new head's cached total to `x + plan s` in O(1).

**The invariant includes the bounds.** `Invariant s` is cache consistency and every
|x| ≤ 10^12 and |cum| ≤ 10^15. The checker range-checks each entry once, before using it in
arithmetic. So `of_list` is safe on any list, and a consistent list with out-of-range values is
rejected. `plan_correct` and `push_total` need only consistency, so they are stated over
`Consistent`. The `of_list` differential test feeds consistent lists with an out-of-range
amount, an out-of-range total, huge values, and an older entry near `max_int`. On all of them the
generated checker agrees with the Lean checker. A generated `in_range` that always returns
`true` fails the test; the generic differential test does not catch it, because its inputs are
all in range.

**Refusal instead of a precondition.** `push` returns `none` when |x| > 10^12 or the new total
would leave ±10^15. Two reasons for not using a length precondition: a length bound can't be
stated in the generator's subset (no `Nat`), and a caller precondition would need more trusted
OCaml to enforce. Lists built by `push` can be longer than `Bounded`'s 1000 entries.
`reference_fits_inv` proves that this doesn't matter under the invariant: every value
`reference` computes is a cached total of some suffix.

The generator needed one change: a per-example list of exported operations (`ops = ["push"]`).
`push` itself translated with the existing subset. The OCaml wrapper (`Running_sum_t`) has a
`private` type built only by `of_list` (which runs the generated checker) or `push`, and an
unchecked O(1) `total`.

The sequence test (`test/push_seq.ml`, run by `scripts/difftest.sh`) checks each push
sequence against the Lean oracle: refusal count, total, reference, checker verdict and every
entry. Its inputs include sequences that saturate exactly at ±10^15 and out-of-range amounts.
Breaking the generated `push` result (`cum + 1`) or its bound (`<` → `<=`) makes it fail.

## Benchmarks

Run with `scripts/bench.sh` (dune release profile) on an AMD Ryzen 5 2600X, OCaml 5.5.1. The
harness is hand-rolled to avoid dependencies. Per (function, size) it does a warm-up, uses a pool
of 64 inputs, calibrates batches of at least 5 ms, and takes 21 samples. It reports the median
ns/call ± the IQR as a % of the median, plus minor-heap words per call. The workload always
satisfies the invariant. The harness floor (an identity function) is about 5 ns/call.

**running_sum**

| size | reference ns | plan ns | check ns | run ns | plan speedup | run speedup |
|---:|---:|---:|---:|---:|---:|---:|
| 0 | 4.9 ±4% | 4.8 ±0% | 4.9 ±1% | 4.8 ±2% | 1.01x | 1.01x |
| 1 | 4.9 ±1% | 4.8 ±1% | 5.1 ±3% | 5.1 ±8% | 1.01x | 0.96x |
| 10 | 23.1 ±11% | 4.8 ±0% | 24.2 ±11% | 24.6 ±2% | 4.83x | 0.94x |
| 100 | 215.1 ±10% | 5.0 ±3% | 156.7 ±6% | 157.2 ±3% | 43x | 1.37x |
| 1000 | 2336.9 ±3% | 4.9 ±1% | 1420.8 ±4% | 1414.8 ±1% | 479x | 1.65x |

**sorted_lookup** (half the queries hit, half miss between two present keys)

| size | reference ns | plan ns | check ns | run ns | plan speedup | run speedup |
|---:|---:|---:|---:|---:|---:|---:|
| 0 | 5.0 ±3% | 4.9 ±5% | 4.8 ±1% | 5.1 ±7% | 1.03x | 0.98x |
| 1 | 9.6 ±3% | 9.9 ±4% | 4.8 ±1% | 12.6 ±3% | 0.96x | 0.76x |
| 10 | 17.7 ±6% | 20.8 ±12% | 17.2 ±12% | 30.9 ±5% | 0.85x | 0.57x |
| 100 | 116.5 ±4% | 83.4 ±6% | 151.2 ±8% | 218.8 ±2% | 1.40x | 0.53x |
| 1000 | 1018.3 ±4% | 691.2 ±5% | 1362.1 ±4% | 2006.4 ±3% | 1.47x | 0.51x |

Where the plan does **not** win:
- **Sizes 0 and 1** sit at the harness floor and can't be told apart.
- **Sorted lookup below about 100 entries.** The plan loses (0.85x at n=10): it does an extra
  comparison per element, and a hit costs the same as in the reference.
- **`run` on sorted lookup, at every size (about 0.5x).** The O(n) check costs more than the
  lookup it licenses.
- **`run` on running sum.** Its 1.4–1.65x "win" is not the plan's doing. `check_from` is
  tail-recursive and the naive `reference` is not, so the check is simply a cheaper traversal.
  The 479x plan speedup only becomes real if the invariant is established once, for example
  checked at ingestion or maintained by construction, rather than checked on every call.

Caveats: the numbers are from one machine and are noisy (a few IQRs exceed 10%). There is no CPU
pinning or frequency control, and the clock is `Unix.gettimeofday`. Treat ratios under about 1.2x
as noise.

**running_sum, whole workflow** (`bench/workflow.ml`, `bench/baseline.ml`). Each path consumes
the same n amounts:
- reference: a plain cons, then `reference` (O(n) per query);
- generated: `push` + `total` through the wrapper (proved, generated, O(1));
- hand: hand-written `{ total; items }`, with no checks and no `Option`;
- hand+checks: the same, plus the generated push's bounds checks and `Option` result.

Numbers are from one run. The last column is generated ÷ hand+checks; across three runs it
ranged from 1.01x to 1.26x, and A at n=1000 was the noisiest cell.

A. Build n entries, then query once:

| n | reference ns | generated ns | hand ns | hand+checks ns | generated / hand+checks |
|---:|---:|---:|---:|---:|---:|
| 10 | 64.3 ±3% | 70.4 ±1% | 51.6 ±5% | 68.0 ±6% | 1.04x |
| 100 | 533.1 ±10% | 587.6 ±7% | 394.4 ±5% | 570.9 ±3% | 1.03x |
| 1000 | 5757.0 ±12% | 6350.5 ±9% | 3576.6 ±3% | 5045.0 ±7% | 1.26x |

B. Query after every insert (n inserts, n queries):

| n | reference ns | generated ns | hand ns | hand+checks ns | generated / hand+checks |
|---:|---:|---:|---:|---:|---:|
| 10 | 160.2 ±1% | 106.0 ±2% | 84.4 ±3% | 99.6 ±3% | 1.06x |
| 100 | 11109.7 ±1% | 956.1 ±3% | 732.5 ±2% | 893.1 ±5% | 1.07x |
| 1000 | 1080870.6 ±2% | 10530.9 ±5% | 7858.5 ±13% | 9508.8 ±8% | 1.11x |

Per insert (build only), median of three runs:

| n | reference (cons) ns / words | generated ns / words | hand ns / words | hand+checks ns / words |
|---:|---:|---:|---:|---:|
| 10 | 4.6 / 6 | 6.7 / 8 | 4.6 / 6 | 5.9 / 8 |
| 100 | 3.7 / 6 | 5.6 / 8 | 3.4 / 6 | 5.7 / 8 |
| 1000 | 4.3 / 6 | 6.6 / 8 | 3.7 / 6 | 5.8 / 8 |

What this says:
- **The proofs add nothing at runtime.** No proof artifact reaches the OCaml.
- **The generated code is close to equivalent hand-written code, but not identical.**
  Generated `push` and hand-written code with the same checks allocate the same 8 words per
  insert. In the steadiest scenario (B) the generated path is 4–16% slower across runs, always
  in the same direction but under the 1.2x noise threshold. A likely cause, not verified: the
  spec stores a cached total in every entry, so `push` reads it through the list cell and the
  entry record (`plan s`), while the hand-written version keeps one total in a record.
- **What costs is the safety the spec asks for.** The bounds checks and the `Option` result
  account for most of the gap to the plain hand-written version (about 1.25–1.8x).
- **Against the naive reference:** building and querying once doesn't win (0.9–0.95x), and
  querying after every insert wins about 100x at n=1000. The fair comparison is hand+checks, not
  the reference.

One finding from the benchmark: the first `running_sum` checker, written as
`checkInvariant (e' :: t)`, rebuilt a list cell on every step (3 words/entry in the generated
OCaml). The fix was a change to the Lean source (`checkFrom e t`), followed by re-proving and
regenerating. The drift check failed until `gen/` was regenerated.

## Tool versions

Lean 4.35.0 (elan 4.2.4, Lake 5.0.0), core library only. OCaml 5.5.1, dune 3.24.2,
alcotest 1.9.1, jj 0.46.0. The benchmark uses only `unix` from the OCaml distribution:
bechamel was not installed, and the hand-rolled harness is about 60 lines.
