# Circuit lower bounds on prescribed-margin slices

These notes give explicit reductions from generic permanent and Hamiltonian cycle polynomials to the same polynomials on matrices with fixed linear constraints. The upstream circuit lower bound is an input to the asymptotic corollaries. The algebraic identities and reductions have separate proofs here.

| Polynomial on constrained inputs | Constraints | Characteristics | Reduction |
| --- | --- | --- | --- |
| Rectangular injective permanent, \(r\times s\), \(s\ge r\) | All row and column sums prescribed, with equal totals | Different from 2 | Three evaluations expose the square permanent of order \(r-2\) |
| Square permanent | Symmetric, all row sums and all diagonal entries prescribed | Different from 2 | A four-vertex marker exposes a permanent square, then truncated square-root recovery gives the generic permanent |
| Directed Hamiltonian cycle polynomial | All row sums, column sums and diagonals prescribed, with equal row and column totals | Every characteristic, including 2 | The degree-four coefficient contracts a directed path |
| Symmetric Hamiltonian cycle polynomial | All row sums and diagonals prescribed | Different from 2 | The degree-six coefficient forces a path through two four-cycles and exposes a directed Hamiltonian cycle polynomial |

Every row gives an ordinary and a border arithmetic circuit lower bound of \(n^{\Omega((\log n)^{1/3})}\) in the corresponding growing dimension (use \(n=r\) in the rectangular case). The threshold may depend on characteristic. In characteristic two the square permanent equals the determinant and the symmetric Hamiltonian cycle polynomial vanishes in orders at least three. All the bounds are polynomial-identity statements. Over the reals, the proofs also explain how exact equality on an appropriate relative open set of positive matrices suffices. Numerical accuracy and Boolean circuit size are different questions.

## Proofs and verification

* `transportation-slices.md` proves both permanent reductions and the positive-definite stochastic promise corollary over the reals.
* `hamiltonian-slices.md` proves both Hamiltonian reductions, with explicit treatment of orientations, diagonal constraints, filling margins, and the auxiliary endpoints.
* `MarginMarker.lean` formalizes the rectangular signed two-by-two marker identity for arbitrary finite row and column core types over every commutative ring. It also proves the marker preserves every row and column sum. The growth bounds, circuit simulations and Hamiltonian constructions are proved in the manuscripts. The Lean file requires mathlib and imports no project-specific definitions.
* `verify_slices.py` exercises the permanent constructions in 108 rectangular and 24 symmetric cases over the integers and the fields of orders 3, 5 and 7. `verify_hamiltonian.py` checks 80 directed Hamiltonian examples over the integers and fields of orders 2, 3, 5 and 7. `verify_symmetric_hamiltonian.py` enumerates all orders of the seven marker vertices, then checks 30 full symmetric examples over the same rings for orders 12–17. These checks use exact arithmetic and test concrete cases of the general arguments.

Run the three checks from this directory with Python 3.10 or newer.

```sh
python3 verify_slices.py
python3 verify_hamiltonian.py
python3 verify_symmetric_hamiltonian.py
```

For the Lean check, start in the extracted directory. Set `LEAN_PROJECT` to the path of an existing Lean 4.36.0 project with matching mathlib.

```sh
source_dir="$PWD"
(cd "$LEAN_PROJECT" && lake env lean "$source_dir/MarginMarker.lean")
```

The upstream result is Theorems 1.1 and 1.4 in Anthropic's manuscript. It proves separate arithmetic lower bounds for the permanent and the Hamiltonian cycle polynomial. The circuit formalization and paper reviewed here were pinned to Git commit `11b6c7e3c927df2658f513b6b68ea7f8929c62c5`. [Formal statement](https://github.com/anthropics/formal-math/blob/11b6c7e3c927df2658f513b6b68ea7f8929c62c5/vp-vnp/Statement.lean) · [Manuscript](https://github.com/anthropics/formal-math/blob/11b6c7e3c927df2658f513b6b68ea7f8929c62c5/vp-vnp/paper.pdf)
