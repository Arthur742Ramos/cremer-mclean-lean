#!/usr/bin/env bash
# M0 verification: build all targets and assert the library has no placeholders.
set -euo pipefail
cd "$(dirname "$0")/.."

echo "== lake build =="
lake build

echo "== sorry audit (library must be placeholder-free at M0) =="
if grep -rn "sorry" CremerMcLean.lean CremerMcLean/ 2>/dev/null; then
  echo "FAIL: sorry found in library"
  exit 1
fi
echo "OK: no sorry in library"

echo "== M0 verification passed =="
