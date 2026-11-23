# Three distinct full phase columns on the 4 by 5 permanent level

For a seven-dimensional constant-permanent space with injective two-row projections, four rank-four row projections and a singleton normal beside three full normals, exactly three distinct full phase columns force every pair of full rows to have two relative phase values. The [proof](three-column-argument.md) excludes all 40 remaining orientations by two aggregate conics and exact identities from eight physical covectors. The four all-two-ratio orientations and the unrestricted existence question remain open.

Run the following command from this directory with Python 3.10 or above, NumPy, and assertions enabled.

```sh
OPENBLAS_NUM_THREADS=1 python3 verify_three_columns.py
```

The program reconstructs its inputs and checks the exact Gaussian integer certificates. The final counts cover 64 three-ratio exclusions, ten further empty aggregate spectra and thirty polynomial identities. The option `--shard INDEX COUNT` selects a disjoint portion of the 104 excluded orientations. This is an exact computer-assisted proof in Python.
