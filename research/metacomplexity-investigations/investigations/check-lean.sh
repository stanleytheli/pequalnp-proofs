#!/bin/sh
set -eu
src=$(CDPATH= cd -- "$(dirname -- "$0")" && pwd)
: "${MATHLIB_ROOT:?Set MATHLIB_ROOT to a built Mathlib 4.36.0 checkout}"
mathlib=$(CDPATH= cd -- "$MATHLIB_ROOT" && pwd)
objects=$(mktemp -d "${TMPDIR:-/tmp}/metacomplexity.XXXXXXXX")
lib="$objects:$mathlib/.lake/build/lib/lean"
for p in "$mathlib"/.lake/packages/*/.lake/build/lib/lean; do lib="$lib:$p"; done
export LEAN_PATH="$lib"
cd "$mathlib"
for mod in BalancedSlices LocalThreshold MonotoneSwitch ParityEdgeCount JuntaRows; do
  lean --root="$src" -j1 -DElab.async=false -o "$objects/$mod.olean" "$src/$mod.lean"
done
