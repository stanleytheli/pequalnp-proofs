# Mixed row ranks on the complex 4 by 5 permanent level

A seven-dimensional constant-permanent space with injective projections onto every pair of rows and ranks 4, 4, 4, 3 can have exactly two full-support rank-four normals only if the third rank-four normal has at most two nonzero entries. The [proof](mixed-row-obstruction.md) gives the reductions and the exceptional curve calculations. The unrestricted seven-dimensional existence problem remains open.

Run from this directory with Python 3.10 or above, NumPy and assertions enabled.

```sh
OPENBLAS_NUM_THREADS=1 python3 verify_mixed_rows.py
```

The verifier regenerates its input and all exact certificates. It reports 232 retained orientations and the number checked by each method. Options include `--support 3`, `--support 4`, and `--part profiles`, `--part finite` or `--part curves`. The two imported verifier modules and background arguments are included. This is an exact computer-assisted mathematical proof in Python. No Lean formalization is claimed.
