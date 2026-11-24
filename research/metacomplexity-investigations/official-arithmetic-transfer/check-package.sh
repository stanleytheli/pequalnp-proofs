#!/bin/sh
set -eu
src=$(CDPATH= cd -- "$(dirname -- "$0")" && pwd)
: "${MATHLIB_ROOT:?Provide a built Mathlib checkout}"
mathlib=$(CDPATH= cd -- "$MATHLIB_ROOT" && pwd)
scratch=$(mktemp -d "${TMPDIR:-/tmp}/planted-upstream.XXXXXXXX")
python3 - "$src" <<'PY'
from hashlib import sha256
from pathlib import Path
from sys import argv
root=Path(argv[1])
for line in (root/'SHA256SUMS').read_text().splitlines():
    digest, file=line.split('  ',1)
    assert sha256((root/file).read_bytes()).hexdigest()==digest,file
PY
lib="$scratch:$mathlib/.lake/build/lib/lean"
for dep in "${MATHLIB_DEPS_DIR:-"$mathlib/.lake/packages"}"/*/.lake/build/lib/lean; do lib="$lib:$dep"; done
export LEAN_PATH="$lib"
cd "$mathlib"
for module in Statement Projection PlantedSlices OfficialTransfer; do
  echo "Checking $module"
  lean --root="$src" -j1 -DElab.async=false -o "$scratch/$module.olean" "$src/$module.lean"
done
echo "Verified planted arithmetic transfer in $scratch"
