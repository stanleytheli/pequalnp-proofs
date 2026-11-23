# Singleton row normals on the complex 4 by 5 permanent level

Suppose a seven-dimensional complex linear space preserves the rectangular permanent after translation by the all-ones matrix, projects injectively to every pair of rows, and has four single-row projections of rank four. If three row normals have full support and the remaining normal is supported on a single coordinate, then at least one pair of the three full normals has exactly two relative phase values. The [proof](singleton-finite-projection.md) excludes all 1,112 orientations in the three-ratio case. The two-ratio cases and the unrestricted seven-plane question remain open.

Run the following command from this directory with Python 3.10 or above, NumPy and assertions enabled.

```sh
OPENBLAS_NUM_THREADS=1 python3 verify_singleton.py
```

The calculation reconstructs every phase orientation, its eight-sheet or aggregate projection, and the exact polynomial or finite-field rank certificates from the formulas. It uses no external input files or network services. Use `--groups 3`, `--groups 4` or `--groups 5` to select a column count. For parallel reproduction, provide `--shard INDEX COUNT` and run all indices from zero through COUNT minus one. The final report accounts for 64, 672 and 376 verified orientations, respectively. A successful full run has an empty unresolved list. This is an exact computer-assisted proof in Python. A Lean formalization remains open.
