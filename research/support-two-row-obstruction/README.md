# Two supported coordinates of a rank-four normal

Suppose a seven-dimensional complex linear space preserves the rectangular 4 by 5 permanent after translation by the all-ones matrix, all four row ranks are four, every projection onto two rows is injective, and three normals have full support. The [support-two argument](support-two-obstruction.md), [support-three/four argument](sparse-row-obstruction.md), and [full-support argument](full-row-obstruction.md) together force the fourth normal to be supported on a single coordinate. Existence under that remaining hypothesis is open.

The package contains the analytic [sparse/high classification](sparse-high-pair.md), the original arithmetic and phase verification modules, and the additional support-two verifier. From this directory, with Python 3.10 or newer, NumPy and interpreter assertions enabled, run

```sh
OPENBLAS_NUM_THREADS=1 python3 verify_support_two.py
```

The available stages are `--part profiles`, `--part finite`, and `--part curves`. For parallel reproduction add `--shard INDEX COUNT` and run every index from zero to COUNT minus one for the selected stage. The curves stage skips phase configurations containing a three-group high pair, since those have enough conics for the finite route. Its sharding indices therefore refer to the retained sign-profile sublist. The full-stage and finite-stage indices use the entire retained list. The calculation generates its orientations, polynomials and projected determinants from the formulas in the manuscript. It makes no network requests. This is an exact computer-assisted argument in Python, not a Lean formalization.
