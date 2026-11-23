# One-NOT circuit bounds for line ORs

For the 57 cyclic projective-plane lines of order seven, a circuit with a genuine NOT gate needs **at least 400 gates** if the input of that NOT is true on each of 57 explicit triples. In particular this applies when the input is a Hamming-weight threshold of one, two or three. A monotone circuit needs 399 gates, attained by computing each eight-point OR with seven gates. The general one-NOT lower bound of 229 appears in the companion projective-plane proof.

For a linear family of arbitrary output sets, the package also proves the full refund inequality of the project's L-meta-997 under two stated deletion hypotheses. A third theorem charges any single chosen output at full size while retaining the truncated charges of every other output. The exact result also holds under a local activation-rank condition, and a separate mathematical proof covers every instance through eighteen input variables. The unrestricted refund inequality remains open. See `refund-cases.md` for the formulas and hypotheses and `eighteen-inputs.md` for the small-input theorem.

## Verification

The sources use Lean 4.36.0, mathlib commit `fc4f59e577feb1a4956671bc04ac18aaaf8cd842`, and `PEqualNP.Defs.CircuitLowerBounds` from the project. With the sources extracted locally and `LEAN_PROJECT` set to the Lean subdirectory of an existing project checkout with dependencies installed, run the following in a POSIX shell.

```sh
src="$PWD"
(cd "$LEAN_PROJECT" && lake env sh -c '
  set -eu
  src=$1
  export LEAN_PATH="$src:$LEAN_PATH"
  lean -j1 --root="$src" -o "$src/WindowCore997.olean" "$src/WindowCore997.lean"
  lean -j1 --root="$src" -o "$src/OneNotRefundCases.olean" "$src/OneNotRefundCases.lean"
  lean -j1 --root="$src" "$src/Chain997.lean"
' sh "$src")
```

The kernel checks the finite incidence and orientation predicates with `decide +kernel`. The printed axiom lists contain only `propext`, `Classical.choice`, and `Quot.sound`. The foundational monotone cut lemma is adapted from [the project's L988 proof](https://github.com/brilliant-hq/pequalnp-proofs/blob/48a1a46a56b8b906a7e15b4f98bbceb16b50e5d2/lean/PEqualNP/Outside/L_meta_988.lean).
