# A sparse rank-four normal on the complex 4 by 5 permanent level

Assume a seven-dimensional constant-permanent space projects injectively onto every pair of rows, all four row ranks are four, and exactly one row normal has zero entries. The [theorem](sparse-row-obstruction.md) shows that normal must be supported on at most two coordinates. The [sparse/full pair classification](sparse-high-pair.md) is analytic and applies to any proper support. The calculation presented here excludes supports of sizes three and four. The unrestricted seven-plane question remains open.

The package includes the [full-row reference](full-row-obstruction.md), its [two-group argument](two-group-proof.md) and its original arithmetic verifier. Reproduce this supplement by running the following command with Python 3.10 or above, NumPy, and assertions enabled.

```sh
OPENBLAS_NUM_THREADS=1 python3 verify_sparse_rows.py
```

Use `--support 3` or `--support 4` for one support, and `--part profiles`, `--part finite`, or `--part curves` for a single stage. The option `--shard INDEX COUNT` assigns disjoint portions of the retained orientation list. The program generates all its mathematical input and writes the successful counts to standard output. It makes no network calls. The verification is an exact computer-assisted proof using Python, and has not been formalized in Lean.
