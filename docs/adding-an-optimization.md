# Adding an optimization (reference / invariant / plan triple)

The exact steps used to add `sorted_lookup` (example 2). `<Ns>` is the Lean namespace
(e.g. `SortedLookup`), `<stem>` the OCaml file stem (e.g. `sorted_lookup`).

## 0. Decide how the invariant will hold

A plan only pays if its invariant doesn't have to be re-checked on every call. In order of
preference:

1. **Keep it true by construction.** Add operations (e.g. `push`) proved to preserve it, and
   generate them (step 7). No check is needed, and an insert stays O(1).
2. **Check once where data comes from outside** (load, parse, network) with the generated
   `checkInvariant`, through a typed wrapper (step 7).
3. **Check on every call** (`run`). This is the fallback: the benchmarks show the O(n) check
   cancels or reverses the gain (`sorted_lookup` `run` is about 0.5x the reference).

The four-function shape below is still required in every case: `run` and the checker are what
the differential test exercises.

## 1. Spec: `SpecDerive/<Ns>/Spec.lean`

In `namespace <Ns>`, write only generator-subset code (see the docstring at the top of
`Emit.lean`) for these four definitions, with these exact names:

| Lean name        | Role                                                        |
|------------------|-------------------------------------------------------------|
| `reference`      | obviously correct, slow                                     |
| `checkInvariant` | `Bool` checker for the invariant                            |
| `plan`           | the optimized version, correct only under the invariant     |
| `run`            | `if checkInvariant s then plan .. else reference ..`        |

Helpers and `structure`s in the same namespace are emitted automatically when used.
Docstrings on the four become the `.mli` doc comments.

Then add the statements as `def Name : Prop := ...` (statements and proofs are kept apart):

- `Invariant` (the `Prop` version; does not need to be in the subset; write it to be obviously
  right, e.g. `List.Pairwise`)
- `PlanCorrect : ∀ inputs, Invariant s → plan .. = reference ..`
- `CheckSound`, `CheckComplete` (the Bool checker vs. `Invariant`)
- `RunCorrect : ∀ inputs, run .. = reference ..`
- `Bounded` (the input domain of the OCaml code, with a `Decidable` instance) and one
  `Fits` theorem statement per Int arithmetic site. Run step 3 first if unsure: the generated
  header lists the sites per function. With no sites, `Bounded` only has to make the inputs
  representable, and there is nothing to prove.

Add `import SpecDerive.<Ns>.Spec` to `SpecDerive.lean`.

## 2. Proofs: `SpecDerive/<Ns>/Proofs.lean` and `SpecDerive/Check.lean`

Prove each statement as `theorem foo : Statement := by unfold Statement; ...` using core
tactics (`simp only`, `induction`, `cases`, `omega`). In `SpecDerive/Check.lean`, import the
proofs and add `example : <Ns>.Statement := <Ns>.foo` and `#print axioms <Ns>.foo` for each.
Then run `lake build && scripts/proof-gate.sh`. The gate fails on `sorry` and the like, on any
statement without an `example`, and on non-standard axioms.

Helper checkers should take head and tail separately (`checkFrom e t`) rather than rebuild
`e' :: t` in the recursive call. The generated OCaml would otherwise allocate per element.

## 3. Generate: `Emit.lean`

Add `("<stem>", `<Ns>)` to `Emit.examples`, then run `lake exe emit gen gen`. If it reports
something outside the subset, change the Lean source to fit. Widen the generator only when
fitting would make the reference less obviously correct, and record why in the commit message
(example 2 needed `Option`). Check that `gen/<stem>_gen.ml` is readable, then run `dune build`.

## 4. Oracle: `Oracle.lean`

Write a `String → Option String` parser/printer for one input line, printing
`<reference result> <checkInvariant> <decide Bounded>`, and register it in `examples`. Keep the
line format trivial: space-separated tokens, with `a:b` for a pair.

## 5. OCaml adapter: `subjects/<stem>_subject.ml`

Implement `Harness.Subject.S`. Wrap the generated functions (uncurry multi-argument functions
into one `input` type). Write `show_output` to print exactly as the oracle does, and `to_line`
to produce exactly what the oracle parses. Then write:

- `gen st ~size ~valid`: inputs inside `Bounded`, values from `Harness.Pick` (boundary-biased).
  With `valid:false`, actively break the invariant in several ways (off-by-one, duplicates,
  swaps, random).
- `workload st ~size`: a realistic invariant-holding benchmark input.

Add the module to `Subjects.all`.

## 6. Verify and measure

```sh
scripts/verify.sh          # build, proof gate, reject tests, drift, difftest
SEED=7 CASES=10000 scripts/difftest.sh
scripts/bench.sh
```

The difftest requires that both the invariant-holding and the invariant-violating paths get
exercised, and that the plan alone is wrong on at least one violating input (so the check is
load-bearing). Commit `gen/` together with the spec change: CI's drift job fails otherwise.

## 7. Optional: invariant-preserving operations and a typed wrapper

Done for `running_sum` with `push`.

1. **Spec.** Define the operation in the subset. If it can grow a value (a cached total grows
   with every insert), have it return `Option` and refuse at the value bounds rather than take a
   length precondition. A length bound can't be stated in the subset, and the caller can't
   enforce it without extra trusted code. Range-check inputs *before* any arithmetic that uses
   them. Statements:
   - preservation: `Invariant s → op x s = some s' → Invariant s'`
   - what the operation does, in reference terms (e.g. `reference s' = x + reference s`)
   - the plan on the result (e.g. `plan s' = x + reference s`)
   - values stay bounded (`ValuesBounded s → … → ValuesBounded s'`)
   - one `Fits` per arithmetic site in the operation
   - if results can exceed the `Bounded` length, that the other functions still fit on them
     (`ReferenceFitsInv`)
2. **Generate.** Add the name to the example's `ops` in `Emit.examples`, then run
   `lake exe emit gen gen`. It is emitted and exported in the `.mli` like the fixed four.
3. **Wrapper.** Write `wrapper/<stem>_t.ml{,i}`, a few lines of trusted code:
   `type t = private entry list`, `of_list` (runs the generated checker), the generated
   operations, and the plan on `t` with no check. The `.mli` states what the type guarantees:
   every `t` passed through the generated checker or a generated preserving operation. It also
   states what that rests on: proofs of the Lean model plus a tested, unproven generator, with
   `Bounded` unchecked on `of_list` inputs.
4. **Oracle.** Add a sequence mode: one line of operation arguments, applied from the empty
   value. Print the refusal count, plan, reference, checker verdict and the full resulting value.
5. **Test.** Write a sequence test like `test/push_seq.ml`, which builds through the wrapper.
   Include sequences that hit each refusal limit exactly. Deliberately break the generated
   operation's result and its bound once each, and confirm the test fails.
6. **Benchmark the whole workflow** (`bench/workflow.ml`): build with operations then query,
   against plain build + reference and against the checked `run`. Do this both for
   query-once and query-after-every-insert, and report the per-operation cost and allocation.
   For `running_sum`, by-construction loses slightly when building and querying once
   (about 0.95x), and wins 148x at n=1000 when querying after every insert.

## What you should not need to touch

`harness/*` (subject signature, picker, differential driver, benchmark), `test/difftest.ml`,
`bench/bench.ml` and `scripts/*`. If you have to change them, the workflow did not generalize
for your case: write down why.

Exception: invariant-preserving operations (step 7) are sequences of operations, which the
generic input → output `Diff` driver doesn't express. They needed a per-example sequence test
and workflow benchmark, both reusing `Diff.oracle_outputs`, `Pick` and `Bench.measure`.
