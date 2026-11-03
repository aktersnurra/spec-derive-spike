#!/usr/bin/env bash
# The generator must refuse every definition in RejectCases.lean with a clear error.
set -euo pipefail
cd "$(dirname "$0")/.."
cases=$(grep -oE '^(partial )?def [A-Za-z]+' RejectCases.lean | awk '{print $NF}')
names=()
for c in $cases; do names+=("RejectCases.$c"); done
lake exe emit reject "${names[@]}"
