# Projective-plane line ORs with one NOT gate

The 57 line ORs of the cyclic projective plane of order seven require **at least 229 gates** in a fan-in-two AND/OR/NOT circuit with at most one NOT. Distinct outputs may share gates. `PlaneOneNot.lean` also proves the two parity-dependent formulas for every finite projective plane of order at least two. The arithmetic bounds grow as one half of the cube of the order.

The proof uses the actual gate-list semantics from `PEqualNP.Defs`. It permits gates with zero or one input, missing or forward references with the project's default value, and outputs at arbitrary indices. The result applies to multi-output Boolean circuits computing the listed ORs for every input assignment.

`one-not-plane.md` gives the proof for all orders. `window-partial.md` explains the two counts, their use in special cases of L997, and the obstacle to combining them for all set families. The general L997 conjecture remains open here. In the Lean source, `plane57_one_not_229` is the explicit cyclic example, `even_plane_one_not997` and `odd_plane_one_not997` are the all-orders results, and `one_not_uniform997` is the structural statement for general uniform set families.

## Reproduce

Start in the extracted directory. Set `LEAN_PROJECT` to the `lean` subdirectory of an existing `brilliant-hq/pequalnp-proofs` checkout with the project's reviewed dependencies already installed. The verified environment used Lean 4.36.0 and mathlib commit `fc4f59e577feb1a4956671bc04ac18aaaf8cd842`.

```sh
source_dir="$PWD"
(cd "$LEAN_PROJECT" && lake env lean -j1 "$source_dir/PlaneOneNot.lean")
```

The source prints the axiom dependencies of the key theorems. Each uses only `propext`, `Classical.choice`, and `Quot.sound`. `verification.txt` contains the corresponding guest output. The two-window arguments use the monotone circuit cut and soundness lemmas from the project's L988 proof. [Reviewed L988 source](https://github.com/brilliant-hq/pequalnp-proofs/blob/48a1a46a56b8b906a7e15b4f98bbceb16b50e5d2/lean/PEqualNP/Outside/L_meta_988.lean) · [Project definitions](https://github.com/brilliant-hq/pequalnp-proofs/tree/main/lean/PEqualNP/Defs)
