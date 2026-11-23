# The sparse normal in mixed row ranks has one supported coordinate

For a complex 4 by 5 constant-permanent seven-plane with injective two-row projections and row ranks 4,4,4,3, two full-support normals force the third rank-four normal, if sparse, to be supported on a single coordinate. The [proof](disjoint-two-argument.md) excludes all 1,974 disjoint support-two orientations. Earlier reductions linked in the proof cover the other supports of size at least two. The singleton and unrestricted cases remain open.

With Python 3.10 or above, NumPy, and assertions enabled, run from this directory

```sh
OPENBLAS_NUM_THREADS=1 python3 verify_disjoint_two.py
```

Use `--part finite` for the 1,484 finite orientations or `--part curves` for the other 490. An optional `--shard INDEX COUNT` selects a disjoint portion of the retained orientation list. The verifier establishes an exact computer-assisted proof in Python.
