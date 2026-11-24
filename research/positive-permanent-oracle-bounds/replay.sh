#!/bin/sh
set -eu
: "${MATHLIB_PROJECT:?Set MATHLIB_PROJECT to an installed mathlib4 checkout}"
src=$(cd "$(dirname "$0")" && pwd)
cd "$MATHLIB_PROJECT"
original=$(lake env printenv LEAN_PATH)
export LEAN_PATH="$src:$original"
for mod in RegularMatchings MatchingFace ToricAmplitudes PermanentAmplitudes RepeatFaces OrderedSupport OracleFlow OracleMask; do
  lean --root="$src" -j1 -DElab.async=false -o "$src/$mod.olean" "$src/$mod.lean"
done
