#!/bin/sh
set -eu
: "${LEAN_PROJECT:?Set LEAN_PROJECT to the existing project lean directory}"
src=$(cd "$(dirname "$0")" && pwd)
cd "$LEAN_PROJECT"
base=$(lake env printenv LEAN_PATH)
export LEAN_PATH="$src:$base"
for name in WindowCore997 StableWindow CircuitPins PinTransport WindowAtBase PhysicalWindow PlaneTradeoff; do
  lean --root="$src" -j1 -DElab.async=false -o "$src/$name.olean" "$src/$name.lean"
done
