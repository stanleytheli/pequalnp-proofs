# Row projections on the complex 4 by 5 permanent level

Every seven-dimensional complex linear space preserving the value 120 after translation by the all-ones matrix must have a nonzero direction supported on at most two rows, or a zero coordinate in a rank-four row normal. Existence in those remaining cases is open.

The [rank-three argument](rank-three-obstruction.md) and the [low-row support reduction](row-reduction.md) strengthen the [full-row result](full-row-obstruction.md), whose [two-group proof](two-group-proof.md) and verifier are included unchanged. The rank-three verifier reconstructs all 320 orientations, Gram minors and Macaulay matrices. Its four small lists of row numbers only select subsets of true polynomial consequences. Their independence and the subsequent rational identities are checked during verification.

Run with Python 3.10 or newer, NumPy and Python assertions enabled. The reference environment uses Python 3.12.14 with NumPy 2.3.5. Each verifier performs local computation and writes its results to standard output.

```sh
OPENBLAS_NUM_THREADS=1 python3 verify_full_rows.py
OPENBLAS_NUM_THREADS=1 python3 verify_rank_three.py
```

If the full-row calculation has already been reproduced, run just the second command. Its stages may be run separately with `--part profiles`, `--part finite`, `--part curves` or `--part sign`. A successful full rank-three run reports 248 finite cases, the branches for 68 mixed curve orientations, and four all-sign dual spaces reduced to dimension zero. The argument is an exact computer-assisted mathematical proof. The verification scripts are Python and have not been formalized in Lean.
