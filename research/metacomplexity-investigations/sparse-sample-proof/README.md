# Sparse examples suffice for full-function formula replacement

This separate Lean 4.36.0 supplement imports `CappedMinimum` from `SparseSampleFormulaMinimization.zip`, SHA-256 `de2a9853255794366c9fcb7ea74543333ed2d48e1a0288b3062d0da89e6568b8`.

For any nonempty simple graph, every monotone binary formula that accepts its edge pairs, rejects their paired neighborhood tests, and rejects the specified singletons for degree-one vertices can be replaced by a formula computing the whole graph edge predicate, with no increase in any variable's reads or in gate count. Girth at least five guarantees that these labeled examples themselves agree with the target function. The hypotheses are declared as `WeightedFormula.Sparse.Fits` and `FitsLeaves`, and `sampled_full` is the checked replacement theorem.

`sampled_orientation` establishes the vertexwise read bound from the examples alone. `double_error` proves the local monotonicity step behind the sharp noise repair: if a formula ignores a vertex with one retained incident edge, each other incident edge forces both a positive and a negative error, under the stated memberships. The complete global noisy counting argument is in the parent archive.

The package contains this README, `SparseOrientation.lean`, the three theorem axiom inventories in `axioms.txt`, and the manifest `SHA256SUMS`. To replay, extract the parent archive and copy `SparseOrientation.lean` to its `lean/` directory. In `lean/replay.py`, append `"SparseOrientation"` to the compilation-order tuple after `"CappedMinimum"`. Run the parent archive's replay command against a compiled copy of its pinned Mathlib using Lean 4.36.0.
