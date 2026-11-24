#!/bin/sh
# Replay against an already-built project checkout. All generated objects go into a fresh directory.
set -eu
: "${LEAN_PROJECT:?Set LEAN_PROJECT to the Lean subdirectory of the installed project}"
src=$(CDPATH= cd -- "$(dirname -- "$0")" && pwd)
build=$(mktemp -d "${TMPDIR:-/tmp}/projective-plane234.XXXXXX")
trap 'rm -rf "$build"' EXIT
cd "$LEAN_PROJECT"
lake env sh -c '
  set -eu
  src=$1
  build=$2
  export LEAN_PATH="$build:${LEAN_PATH:-}"
  lean --version
  for module in WindowCore997 OneNotRefundCases Chain997 BiCut997 SparseCertificate997 PhysicalSparse997 Plane232 Plane233 Transparent997 Reader997 PhysicalSkip997 Plane234 OrHeavy997 PinnedOr997
  do
    printf "\nChecking %s\n" "$module"
    lean -j1 -DElab.async=false --root="$src" -o "$build/$module.olean" "$src/$module.lean"
  done
' sh "$src" "$build"
