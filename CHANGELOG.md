# Changelog

## 2026-11-03: bounds in the invariant; fair baseline
- `RunningSum.Invariant` is now cache consistency and value bounds; the checker range-checks
  each entry before using it in arithmetic, so the wrapper path needs no unchecked
  precondition. `PlanCorrect`/`PushTotal` stated over `Consistent`; new
  `PushPreservesConsistent`; `CheckSiteFits` now guarded by `InRange` instead of `Bounded`.
- `of_list` differential test on consistent but out-of-range lists.
- Bound theorems classical-free (split conjunction goals before `omega`).
- Hand-written `{ total; items }` baselines (with and without checks) in the workflow
  benchmark.

## 2026-11-03: keep the invariant true by construction
- `RunningSum.push`: generated O(1) insert that refuses at the value bounds; proofs of
  invariant preservation, semantics, value bounds, and `reference` fitting under the
  invariant at any length.
- `Emit.lean`: per-example exported operations (`ops`); `let` keeps the Lean binder name.
- `wrapper/Running_sum_t`: typed wrapper (private type, checker-gated `of_list`, `push`,
  unchecked `total`).
- Oracle `running_sum_push` mode and push-sequence differential test; whole-workflow
  benchmark; procedure doc gains the order of preference and step 7.

## 2026-11-03: spike complete
- Lean spec and proofs for `running_sum` (cached running total) and `sorted_lookup`
  (early-exit lookup in a key-sorted list): plan correctness under the invariant, checker
  soundness/completeness, `run = reference`, OCaml int bounds.
- `Emit.lean`: generator from elaborated Lean definitions to plain OCaml over a documented
  subset; out-of-subset definitions rejected (`RejectCases.lean`).
- Drift check (`scripts/check-gen.sh`, CI), proof gate, Lean oracle, generic differential
  test and benchmark harnesses, `scripts/verify.sh`.
- `docs/adding-an-optimization.md`: procedure, validated by adding example 2.
