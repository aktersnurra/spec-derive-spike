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
subjects/                    per-example adapters (input generators, oracle line format)
test/difftest.ml             alcotest runner for the differential test
bench/bench.ml               benchmark runner
scripts/                     verify, proof-gate, check-gen, test-reject, difftest, bench
docs/adding-an-optimization.md   the procedure for a new triple
```

## What is proved, what is tested, what is trusted

**Proved (Lean kernel), about the Lean model only:**

| theorem | running_sum | sorted_lookup |
|---|---|---|
| `Invariant → plan = reference` | `plan_correct` | `plan_correct` |
| checker sound / complete | `check_sound`, `check_complete` | same |
| `run = reference` (all inputs) | `run_correct` | `run_correct` |
| OCaml `int` bounds | `bounded_tail`, `reference_fits`, `check_site_fits` | none needed (0 arithmetic sites) |

`#print axioms` (from `scripts/proof-gate.sh`, Lean 4.35.0); no `sorry`:

```
'RunningSum.plan_correct' does not depend on any axioms
'RunningSum.check_sound' depends on axioms: [propext, Classical.choice, Quot.sound]
'RunningSum.check_complete' depends on axioms: [propext, Classical.choice, Quot.sound]
'RunningSum.run_correct' depends on axioms: [propext, Classical.choice, Quot.sound]
'RunningSum.bounded_tail' depends on axioms: [propext, Quot.sound]
'RunningSum.reference_fits' depends on axioms: [propext, Classical.choice, Quot.sound]
'RunningSum.check_site_fits' depends on axioms: [propext, Classical.choice, Quot.sound]
'SortedLookup.plan_correct' depends on axioms: [propext, Quot.sound]
'SortedLookup.check_sound' depends on axioms: [propext, Quot.sound]
'SortedLookup.check_complete' depends on axioms: [propext, Quot.sound]
'SortedLookup.run_correct' depends on axioms: [propext, Quot.sound]
```

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
- The `Bounded` precondition. **It is not checked at runtime.** The generated `.mli` documents
  it, and the difftest asserts (through the oracle) that every generated input is inside it.
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
  (`reference: 1, check_from: 1`), which makes a missed site visible in review.
- The generator rejects `Nat` (truncated subtraction), `/` and `%` (Lean's `Int` division is
  Euclidean, OCaml's truncates), and literals that don't fit.

It was clean for these examples: `omega` closes every bound with literal constants. The weak spot
is that "one theorem per site" is a convention the tools don't enforce.

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

One finding from the benchmark: the first `running_sum` checker, written as
`checkInvariant (e' :: t)`, rebuilt a list cell on every step (3 words/entry in the generated
OCaml). The fix was a change to the Lean source (`checkFrom e t`), followed by re-proving and
regenerating. The drift check failed until `gen/` was regenerated.

## Tool versions

Lean 4.35.0 (elan 4.2.4, Lake 5.0.0), core library only. OCaml 5.5.1, dune 3.24.2,
alcotest 1.9.1, jj 0.46.0. The benchmark uses only `unix` from the OCaml distribution:
bechamel was not installed, and the hand-rolled harness is about 60 lines.
