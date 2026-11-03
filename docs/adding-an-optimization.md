# Adding an optimization (reference / invariant / plan triple)

The exact steps used to add `sorted_lookup` (example 2). `<Ns>` is the Lean namespace
(e.g. `SortedLookup`), `<stem>` the OCaml file stem (e.g. `sorted_lookup`).

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

## What you should not need to touch

`harness/*` (subject signature, picker, differential driver, benchmark), `test/difftest.ml`,
`bench/bench.ml` and `scripts/*`. If you have to change them, the workflow did not generalize
for your case: write down why.
