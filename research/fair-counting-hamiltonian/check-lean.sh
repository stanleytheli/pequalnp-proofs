#!/bin/sh
set -eu
here=$(CDPATH= cd -- "$(dirname -- "$0")" && pwd)
mathlib=${MATHLIB_ROOT:?Set MATHLIB_ROOT to an existing built Mathlib 4.36.0 checkout}
build=$(mktemp -d)
trap 'rm -rf "$build"' EXIT
cd "$mathlib"
LEAN_PATH="$build:$mathlib/.lake/build/lib/lean"
for p in "$mathlib"/.lake/packages/*/.lake/build/lib/lean; do LEAN_PATH="$LEAN_PATH:$p"; done
export LEAN_PATH
lean --version
for name in RankCertificate FibonacciTransfer; do
    lean --root="$here" -j1 -DElab.async=false -o "$build/$name.olean" "$here/$name.lean"
done
