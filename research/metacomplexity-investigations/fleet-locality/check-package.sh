#!/bin/sh
set -eu
src=$(CDPATH= cd -- "$(dirname -- "$0")" && pwd)
: "${PROJECT_LEAN_ROOT:?Set to the built lean directory of the pinned fleet project}"
project=$(CDPATH= cd -- "$PROJECT_LEAN_ROOT" && pwd)
scratch=$(mktemp -d "${TMPDIR:-/tmp}/parity-fleet.XXXXXXXX")
python3 - "$src" <<'PY'
from hashlib import sha256
from pathlib import Path
from sys import argv
root=Path(argv[1])
for line in (root/'SHA256SUMS').read_text().splitlines():
    digest, file=line.split('  ',1)
    assert sha256((root/file).read_bytes()).hexdigest()==digest,file
PY
lib="$scratch:$project/.lake/build/lib/lean"
for dep in "$project"/.lake/packages/*/.lake/build/lib/lean; do lib="$lib:$dep"; done
export LEAN_PATH="$lib"
cd "$project"
for module in LocalThreshold ParityEncoding; do
  echo "Checking $module"
  lean --root="$src" -j1 -DElab.async=false -o "$scratch/$module.olean" "$src/$module.lean"
done
python3 "$src/pack-guest.py" "$project" "$src/fleet-pins.json" "$src/ParityCircuit.lean" "$scratch/ParityCircuitReplay.lean"
echo "Checking physical circuit theorem"
lean --root="$scratch" -j1 -DElab.async=false -o "$scratch/ParityCircuitReplay.olean" "$scratch/ParityCircuitReplay.lean"
echo "Verified parity-to-partial-MCSP theorem in $scratch"
