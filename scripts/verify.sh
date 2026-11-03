#!/usr/bin/env bash
# One command for the whole workflow: Lean build (kernel-checks every proof), proof gate,
# generator rejection tests, drift check, OCaml build, differential test vs. the Lean oracle.
set -euo pipefail
cd "$(dirname "$0")/.."
lake build
scripts/proof-gate.sh
scripts/test-reject.sh
scripts/check-gen.sh
dune build
scripts/difftest.sh
echo "verify: PASS"
