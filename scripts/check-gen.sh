#!/usr/bin/env bash
# Drift check: regenerate the OCaml from the Lean spec into a temp dir and fail if it
# differs from the checked-in gen/ (changed, missing, or stale *_gen.ml / *_gen.mli files).
set -euo pipefail
cd "$(dirname "$0")/.."
tmp=$(mktemp -d)
trap 'rm -rf "$tmp"' EXIT
lake exe emit gen "$tmp"
status=0
for f in "$tmp"/*; do
  name=$(basename "$f")
  if [ ! -f "gen/$name" ]; then echo "check-gen: gen/$name is missing"; status=1
  elif ! diff -u "gen/$name" "$f"; then echo "check-gen: gen/$name differs from generator output"; status=1
  fi
done
for f in gen/*_gen.ml gen/*_gen.mli; do
  [ -e "$f" ] || continue
  [ -f "$tmp/$(basename "$f")" ] || { echo "check-gen: $f is stale (not generated)"; status=1; }
done
[ "$status" -eq 0 ] && echo "check-gen: PASS (gen/ matches the Lean spec)" || {
  echo "check-gen: FAIL. Run 'lake exe emit gen gen' and commit the result."; exit 1; }
