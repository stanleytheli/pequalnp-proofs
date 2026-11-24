#!/bin/sh
set -eu
if [ "$#" -ne 1 ]; then
  echo 'Usage: sh check-lean.sh /absolute/path/to/prebuilt/mathlib4' >&2
  exit 2
fi
package=$(CDPATH= cd -- "$(dirname -- "$0")" && pwd)
mathlib=$(CDPATH= cd -- "$1" && pwd)
build=$(mktemp -d "${TMPDIR:-/tmp}/matching-extensions.XXXXXXXX")
base_src="$package/foundation/HighGirthMatchingProofs"
if ! sh "$base_src/check-lean.sh" "$mathlib" > "$build/foundation.log" 2>&1; then
  cat "$build/foundation.log" >&2
  exit 1
fi
base=$(sed -n 's/^Verified modules are in \(.*\)$/\1/p' "$build/foundation.log")
test -s "$base/PortTrees.olean"
cd "$mathlib"
packages=${MATHLIB_DEPS_DIR:-"$mathlib/.lake/packages"}
LEAN_PATH="$build:$base:$mathlib/.lake/build/lib/lean"
for d in "$packages"/*/.lake/build/lib/lean; do
  if [ -d "$d" ]; then LEAN_PATH="$LEAN_PATH:$d"; fi
done
export LEAN_PATH
while IFS= read -r mod; do
  case "$mod" in ''|*[!A-Za-z0-9_]*) exit 2 ;; esac
  echo "Checking $mod"
  lean --root="$package/lean" -j1 -DElab.async=false -o "$build/$mod.olean" "$package/lean/$mod.lean"
done < "$package/modules.txt"
printf 'Verified extension modules are in %s\n' "$build"
