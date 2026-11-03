# Changelog

## 2026-11-03: spike complete
- Lean spec and proofs for `running_sum` (cached running total) and `sorted_lookup`
  (early-exit lookup in a key-sorted list): plan correctness under the invariant, checker
  soundness/completeness, `run = reference`, OCaml int bounds.
- `Emit.lean`: generator from elaborated Lean definitions to plain OCaml over a documented
  subset; out-of-subset definitions rejected (`RejectCases.lean`).
- Drift check (`scripts/check-gen.sh`, CI), proof gate, Lean oracle, generic differential
  test and benchmark harnesses, `scripts/verify.sh`.
- `docs/adding-an-optimization.md`: procedure, validated by adding example 2.
