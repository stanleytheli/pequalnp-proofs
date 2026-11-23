# Affine probability representations of the Hamiltonian-cycle polynomial

For a graph H let Q be the probability that independently selected vertices form an independent set. The manuscripts study direct affine equality and positive rescaled limits. On arbitrary graphs the languages supported by polynomial-size no-edge limits are exactly NP/poly. On bipartite graphs they lie in P/poly. For the opposite, edge-present event they are exactly the 2-DNFs, even if graph sizes are unbounded. They use directed Hamiltonian cycles on m vertices, m at least two.

- [Exact representations](probability-barrier.md): any representation of Hamiltonicity as positivity of Q under cube-preserving real affine parameters requires at least 2^m-2 graph edges. A sparsity obstruction and a quantitative finite tolerance statement also hold.
- [Bipartite positive limits](positive-border.md): polynomial-size limits with arbitrary positive normalization have Boolean support in P/poly. For Hamiltonicity this would imply NP is contained in P/poly.
- [Unsigned odd-subdivision construction](positive-odd-construction.md): over every field, an explicit family of nonbipartite subcubic graphs has HC as a leading coefficient after single-variable affine substitutions. The same parameters preserve the real probability cube. Each graph has a known optimal read-two monotone formula for its Boolean edge predicate.
- [Characterization of the no-edge event](positive-support-class.md): arbitrary nonuniform NP verifiers can be encoded, preserving the witness-count function on the Boolean inputs.
- [Characterization of the edge-present event](positive-event.md): the same statement for rank-d witness hypergraphs gives exactly width-d DNF supports.
- [Hamiltonian verifier](graph-arithmetic-transfer.md): the unique anchored-rank certificate used by the construction.

From this directory run the following Python standard-library controls.

```sh
python3 check_probability_barrier.py
python3 check_positive_border.py
python3 check_threshold.py
python3 check_positive_odd.py
python3 check_supports.py
python3 check_event_width.py
```

The checks include a min-cut comparison with direct enumeration at finite, zero and infinite weights, direct physical-root contraction for six small Boolean verifier templates, and structural checks for complete Hamiltonian graph templates of orders two through four. The larger physical templates are generated and their formula counts checked. The leading coefficient on them is proved in the manuscript.

Five Lean files cover the positivity characterization, union argument, Hamiltonian cut restorations, the full exponential edge bound for both tour and transitive-permutation witnesses, and the four unique conditional path maxima and exponent calculation. With Lean 4.36.0 on PATH and a built matching Mathlib checkout, run `MATHLIB_ROOT=/absolute/path/to/mathlib4 sh check-lean.sh`. The P/poly theorem and the complete positive construction have mathematical proofs and finite controls. The checked Lean scope is limited to the declarations listed in `verification.txt`. `SHA256SUMS` covers every source and receipt.
