#!/bin/sh
set -eu
if [ "$#" -ne 1 ]; then
  echo 'Usage: sh check-lean.sh /absolute/path/to/already-built/mathlib4' >&2
  exit 2
fi
bundle=$(CDPATH= cd -- "$(dirname -- "$0")" && pwd)
mathlib=$(CDPATH= cd -- "$1" && pwd)
if [ ! -f "$mathlib/.lake/build/lib/lean/Mathlib.olean" ]; then
  echo 'A prebuilt Mathlib.olean is required from Lean 4.36.0.' >&2
  exit 2
fi
build=$(mktemp -d "${TMPDIR:-/tmp}/sparse-permanent.XXXXXXXX")
cd "$mathlib"
LEAN_PATH="$build:$mathlib/.lake/build/lib/lean"
packages=${MATHLIB_DEPS_DIR:-"$mathlib/.lake/packages"}
for dep in "$packages"/*/.lake/build/lib/lean; do
  if [ -d "$dep" ]; then LEAN_PATH="$LEAN_PATH:$dep"; fi
done
export LEAN_PATH
lean --version
for mod in Selector MatchingData Core CorePerm Degree OddSubdivision Iterate Explicit Statement Projection Consequence FlowStep FlowCore FlowIterate FlowCost FlowCycle FlowUpper FlowLift FlowSquare Girth GirthExact GraphOrder GraphBounds Padding Attach AttachDegree AttachMatch AttachFlow FamilyShape MatchExtension PaddingProjection RegularCompletion EdgeCount DirectedSplit RoutedModel RoutedProjection DirectedGrowth BinaryWords PortAccess GreedyRouting PortTrees; do
  echo "Checking $mod"
  lean --root="$bundle/lean" -j1 -DElab.async=false -o "$build/$mod.olean" "$bundle/lean/$mod.lean"
done
printf 'Verified modules are in %s\n' "$build"
