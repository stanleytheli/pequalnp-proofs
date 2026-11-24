#!/bin/sh
set -eu
src=$(CDPATH= cd -- "$(dirname -- "$0")" && pwd)
: "${PROJECT_LEAN_ROOT:?Set to the built lean directory of the pinned fleet project}"
project=$(CDPATH= cd -- "$PROJECT_LEAN_ROOT" && pwd)
scratch=$(mktemp -d "${TMPDIR:-/tmp}/zero-gate.XXXXXXXX")
python3 - "$src" <<'PY'
from hashlib import sha256
from pathlib import Path
from sys import argv
root=Path(argv[1])
for line in (root/'SHA256SUMS').read_text().splitlines():
    digest, file=line.split('  ',1)
    assert sha256((root/file).read_bytes()).hexdigest()==digest,file
PY
if [ -z "${PARITY_OBJECTS:-}" ]; then
  fleet=${FLEET_LOCALITY_DIR:-"$src/../fleet-locality"}
  PROJECT_LEAN_ROOT="$project" sh "$fleet/check-package.sh" >"$scratch/fleet.log"
  cat "$scratch/fleet.log"
  PARITY_OBJECTS=$(sed -n 's/^Verified parity-to-partial-MCSP theorem in //p' "$scratch/fleet.log")
fi
test -f "$PARITY_OBJECTS/ParityCircuitReplay.olean"
lib="$scratch:$PARITY_OBJECTS:$project/.lake/build/lib/lean"
for dep in "$project"/.lake/packages/*/.lake/build/lib/lean; do lib="$lib:$dep"; done
export LEAN_PATH="$lib"
cd "$project"
for module in ZeroSize ZeroMatrix CodeRows CodeRowsDistinct OneRow; do
  echo "Checking $module"
  lean --root="$src" -j1 -DElab.async=false -o "$scratch/$module.olean" "$src/$module.lean"
done
echo "Verified zero-gate size and matrix theorems in $scratch"
