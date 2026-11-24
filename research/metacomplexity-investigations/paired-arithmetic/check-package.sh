#!/bin/sh
set -eu
src=$(CDPATH= cd -- "$(dirname -- "$0")" && pwd)
: "${MATHLIB_ROOT:?Set MATHLIB_ROOT to a built Mathlib checkout}"
mathlib=$(CDPATH= cd -- "$MATHLIB_ROOT" && pwd)
scratch=$(mktemp -d "${TMPDIR:-/tmp}/paired-meta.XXXXXXXX")
export PYTHONDONTWRITEBYTECODE=1
python3 - "$src" "$scratch" <<'PY'
from hashlib import sha256
from pathlib import Path
from sys import argv
root,dest=map(Path,argv[1:])
for line in (root/"SHA256SUMS").read_text().splitlines():
    digest,relative=line.split("  ",1)
    assert sha256((root/relative).read_bytes()).hexdigest()==digest,relative
base=root/"foundation"/"AlgebraicMetacomplexity"
for line in (base/"SHA256SUMS").read_text().splitlines():
    digest,relative=line.split("  ",1)
    assert sha256((base/relative).read_bytes()).hexdigest()==digest,relative
PY
mkdir "$scratch/objects"
lib="$scratch/objects:$mathlib/.lake/build/lib/lean"
for dep in "${MATHLIB_DEPS_DIR:-"$mathlib/.lake/packages"}"/*/.lake/build/lib/lean; do lib="$lib:$dep"; done
export LEAN_PATH="$lib"
cd "$mathlib"
for mod in OccurrenceCycle CopyCompiler FunctionalCNF; do
  echo "Checking foundation/$mod"
  lean --root="$src/foundation/AlgebraicMetacomplexity" -j1 -DElab.async=false -o "$scratch/objects/$mod.olean" "$src/foundation/AlgebraicMetacomplexity/$mod.lean"
done
for mod in IncidenceCompiler PairedLayers PhaseCircuit GateLeaves TightCone AntipodalFloor BooleanBlocks; do
  echo "Checking $mod"
  lean --root="$src" -j1 -DElab.async=false -o "$scratch/objects/$mod.olean" "$src/$mod.lean"
done
export PYTHONPATH="$src/foundation/AlgebraicMetacomplexity"
for control in check_layered check_antipodes check_recognition check_read_two; do python3 "$src/$control.py"; done
echo "Verified paired modules and controls in $scratch"
