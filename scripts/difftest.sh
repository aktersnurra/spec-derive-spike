#!/usr/bin/env bash
# Differential test: generated OCaml vs. the Lean oracle. SEED and CASES are optional.
set -euo pipefail
cd "$(dirname "$0")/.."
lake build oracle
dune build test/difftest.exe
ORACLE="$PWD/.lake/build/bin/oracle" ./_build/default/test/difftest.exe --verbose "$@"
