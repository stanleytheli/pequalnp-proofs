#!/bin/sh
set -eu
: "${MATHLIB_PROJECT:?Set MATHLIB_PROJECT to an installed mathlib4 checkout}"
packet=$(cd "$(dirname "$0")" && pwd)
src="$packet/evening/affine"
cd "$MATHLIB_PROJECT"
original=$(lake env printenv LEAN_PATH)
export LEAN_PATH="$src:$original"
for mod in NormalizedPath GraphContraction GenericParameters ExplicitSpecialization PhysicalNetwork ReadOnce CutRank GraphCut CubePolynomial AffineCircuit PolynomialNetwork SupportRank CircuitNetwork BorderTransfer BorderNetwork; do
  lean --root="$src" -j1 -DElab.async=false -o "$src/$mod.olean" "$src/$mod.lean"
done
