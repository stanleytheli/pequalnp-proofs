# A support-two normal beside a rank-three row

In a complex 4 by 5 constant-permanent seven-plane with injective two-row projections and row ranks 4,4,4,3, suppose two rank-four normals have full support and the third has support two. Its two coordinates must both be inactive in the rank-three row, meaning that both of that row's defining covectors vanish there. The [proof](mixed-two-argument.md) excludes all 1,834 orientations in which the sparse support contains the active columns.

Run from this directory with Python 3.10 or above, NumPy, and assertions enabled.

```sh
OPENBLAS_NUM_THREADS=1 python3 verify_mixed_two.py
```

The verifier generates its inputs from the coordinate and phase formulas. Use `--part finite` for the 1,554 finite orientations or `--part curves` for the 280 others. An optional `--shard INDEX COUNT` partitions the retained orientation list. The four supporting verifier modules are included. This is an exact computer-assisted mathematical proof in Python.
