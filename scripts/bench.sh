#!/usr/bin/env bash
# Benchmark reference vs. plan (and checker / run) for every example. Release profile.
set -euo pipefail
cd "$(dirname "$0")/.."
dune build --profile release bench/bench.exe
./_build/default/bench/bench.exe
