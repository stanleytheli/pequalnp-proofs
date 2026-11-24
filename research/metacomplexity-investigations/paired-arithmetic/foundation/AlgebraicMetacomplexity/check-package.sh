#!/bin/sh
# Replay from a preinstalled Lean 4.36.0 and matching built Mathlib.
# All theorem modules here are local sources; the script never downloads.
set -eu
src=$(CDPATH= cd -- "$(dirname -- "$0")" && pwd)
: "${MATHLIB_ROOT:?Set MATHLIB_ROOT to the verified, built Mathlib checkout}"
mathlib=$(CDPATH= cd -- "$MATHLIB_ROOT" && pwd)
objects=$(mktemp -d "${TMPDIR:-/tmp}/algebraic-meta.XXXXXXXX")
lib="$objects:$mathlib/.lake/build/lib/lean"
for dep in "${MATHLIB_DEPS_DIR:-"$mathlib/.lake/packages"}"/*/.lake/build/lib/lean; do lib="$lib:$dep"; done
export LEAN_PATH="$lib"
cd "$mathlib"
for mod in OccurrenceCycle CopyCompiler FunctionalCNF PlantedSlices SignedTransfer EncodedModels FiberPolynomial QueryCounting ExactWidth; do
  echo "Checking $mod"
  lean --root="$src" -j1 -DElab.async=false -o "$objects/$mod.olean" "$src/$mod.lean"
done
export PYTHONDONTWRITEBYTECODE=1
for control in check_gap check_fibers check_boundary; do python3 "$src/$control.py"; done
echo "Verified objects are in $objects"
