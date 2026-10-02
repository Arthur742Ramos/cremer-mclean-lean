#!/usr/bin/env bash
# Full verification: build all targets, assert the library is placeholder-free,
# and run the Palomar packaging checks.
set -euo pipefail
cd "$(dirname "$0")/.."

export PATH="$HOME/.elan/bin:$PATH"
export LAKE_HOME="$HOME/.elan/toolchains/leanprover--lean4---v4.35.0-rc2"

echo "== lake build =="
lake build

echo "== sorry audit (library must be placeholder-free) =="
if grep -rn "sorry" CremerMcLean.lean CremerMcLean/ 2>/dev/null; then
  echo "FAIL: sorry found in library"
  exit 1
fi
echo "OK: no sorry in library"

echo "== Challenge regeneration check =="
cp Challenge.lean /tmp/cm-challenge-before.lean
python3 scripts/make_challenge.py
if ! cmp -s Challenge.lean /tmp/cm-challenge-before.lean; then
  echo "FAIL: Challenge.lean was not the generator output; regenerated in place"
  exit 1
fi
echo "OK: Challenge.lean matches generator output"

echo "== package shape check =="
python3 scripts/check_package.py

echo "== Palomar comparator replica =="
./scripts/verify-palomar.sh

echo "== metadata check =="
python3 scripts/verify_metadata.py

echo "== verification passed =="
