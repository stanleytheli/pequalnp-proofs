# Row projections on the 4 by 5 permanent level

This package proves a conditional obstruction for L-gct-179. If a seven-dimensional complex linear space keeps the rectangular permanent equal to 120 after translation by the all-ones matrix, then it has a direction supported on at most two rows, a row projection of rank at most three, or a zero coordinate in the normal of a rank-four row projection. Whether such a space exists in any of those cases remains open.

The [main proof](full-row-obstruction.md) derives the fourth-root profiles and the rank obstruction. The [two-group argument](two-group-proof.md) handles the sign profiles without enumeration. The [verifier](verify_full_rows.py) generates all remaining input data from the formulas in the proofs.

## Reproduction

From this directory, run the following command using Python 3.10 or newer and an existing NumPy installation. The reference environment uses Python 3.12.14 and NumPy 2.3.5.

```sh
OPENBLAS_NUM_THREADS=1 python3 verify_full_rows.py
```

The verifier checks 29,808 orientations and retains 12,185 after the exact row-projection test. Six retained orientations fall under the two-group argument. The finite calculation covers 12,023 cases, and the curve calculation covers the other 156. A successful complete run prints the finite and curve totals and exits with status zero.

Use `--part profiles`, `--part finite`, or `--part curves` for a single stage. For parallel runs, use `--shard INDEX COUNT` for every index from zero through `COUNT−1`. Each invocation generates its own inputs and writes only to standard output. Python assertions must be enabled.
