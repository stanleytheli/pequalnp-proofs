#!/bin/sh
set -eu
: "${MATHLIB_PROJECT:?Set MATHLIB_PROJECT to an installed mathlib4 checkout}"
src=$(cd "$(dirname "$0")/lean" && pwd)
cd "$MATHLIB_PROJECT"
original=$(lake env printenv LEAN_PATH)
export LEAN_PATH="$src:$original"
for mod in OracleFlow ParseFlow CornerMass FiberCoupling HallBlocks TightMatching BraceReadout CategoricalCut PhysicalBrace UniversalReadout; do
  lean --root="$src" -j1 -DElab.async=false -o "$src/$mod.olean" "$src/$mod.lean"
done
