#!/usr/bin/env bash
# Proof gate (formal-spec): no escape hatches in proofs, every statement has a checked
# proof, and the proofs depend only on Lean's standard axioms.
set -euo pipefail
cd "$(dirname "$0")/.."
fail=0

proofs=$(find SpecDerive -name Proofs.lean | sort)
if grep -nE '\bsorry\b|^\s*axiom\b|native_decide|\bunsafe\b|implemented_by|@\[extern' $proofs; then
  echo "proof-gate: forbidden construct in a proofs file"; fail=1
fi

# Every `def Foo : Prop` statement in a Spec.lean must have `example : NS.Foo := ...` in Check.lean.
for spec in $(find SpecDerive -name Spec.lean | sort); do
  ns=$(grep -m1 -oE '^namespace [A-Za-z.]+' "$spec" | awk '{print $2}')
  for stmt in $(grep -oE '^def [A-Z][A-Za-z]* : Prop' "$spec" | awk '{print $2}'); do
    if ! grep -qE "^example : $ns\.$stmt :=" SpecDerive/Check.lean; then
      echo "proof-gate: statement $ns.$stmt has no checked proof in SpecDerive/Check.lean"; fail=1
    fi
  done
done

out=$(lake env lean SpecDerive/Check.lean 2>&1) || { echo "$out"; echo "proof-gate: Check.lean failed"; exit 1; }
echo "$out"
bad=$(echo "$out" | grep -oE "depends on axioms: \[[^]]*\]" | sed -E 's/.*\[(.*)\]/\1/' | tr ',' '\n' \
  | sed 's/ //g' | grep -vE '^(propext|Classical\.choice|Quot\.sound)$' || true)
if [ -n "$bad" ]; then echo "proof-gate: non-standard axioms: $bad"; fail=1; fi
n=$(echo "$out" | grep -cE "depends on axioms|does not depend on any axioms" || true)
echo "proof-gate: $n theorems checked"
[ "$fail" -eq 0 ] && echo "proof-gate: PASS" || { echo "proof-gate: FAIL"; exit 1; }
