# Bounded-degree Hamiltonian encoding and fair counting

The same family of long even subdivisions has polynomial-time constructible, gate-optimal Boolean read-two formulas, while its canonical multilinear extension inherits the published Hamiltonian-cycle arithmetic lower bound. Exact fair counting on such graphs is #P-complete under a one-query metric reduction. A single fixed formula per size bound suffices when some inputs may be fixed to zero. The same fixed templates give the parity result.

- [Weighted Hamiltonian construction and arithmetic transfer](graph-arithmetic-transfer.md)
- [Unweighted metric and parity reductions](fair-counting.md)
- [Fixed-template zero-restriction theorem](universal-fair.md)

All Python programs use the standard library. In this directory run:

```sh
python3 check_contraction.py 4
python3 check_contraction.py 3 --probability-leaves
python3 check_fair.py
python3 check_metric.py
python3 check_universal.py
python3 read_two_formula.py
```

The contraction checks eliminate the vertices of the generated physical graph. The universal controls reuse the identical unsigned graph for different subcubes. The read-two builder verifies the actual syntax tree and its gate count, and the matching verifier checks the distinct incident-edge witnesses.

The two Lean files formalize the anchored-rank equivalence for permutations and the common-modulus Fibonacci path identity and scalar normalization. With an existing built Mathlib 4.36.0 checkout and its matching Lean executable on PATH, run `MATHLIB_ROOT=/absolute/path/to/mathlib4 sh check-lean.sh`. These files contain original proof source. The full graph and complexity arguments are in the manuscripts. The physical gate benchmark is also covered by the linked long-subdivision result. `verification.txt` records verification of the included controls. `SHA256SUMS` covers every source and receipt.
