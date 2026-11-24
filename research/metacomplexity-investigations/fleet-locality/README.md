# A circuit for every partial table from 3q+1 parity neighbors

The theorem `ParityEncoding.every_table` uses the public fleet's actual definitions of `QueryLocal`, `PartialMCSP`, `Consistent` and `HasCircuitSize`. For a fixed unary size bound s and fixed target arity, suppose a q-local map takes odd input exactly to partial-MCSP membership. If the source has at least k = 3q+1 bits, **every** image table has a consistent fan-in-two circuit with at most

    1 + k (s + 1 + 2(2q+1))

gates. The stronger linear-overhead adder analysis in the accompanying research note has a separate mathematical proof. This formal gate bound uses the fleet's existing unary counter.

An odd center already has a size-s witness. At an even center choose k distinct single-bit flips and take one circuit witness for each odd neighbor. The same witnesses serve every target row. The encoding for undefined, zero and one rows is 00, 10 and 11, respectively. A specified one remains a one if its value-bit certificate is preserved. Preserving both certificates fixes a specified zero. At most q and 2q flips, respectively, can damage these conditions. The threshold 2q+1 on k witness outputs therefore agrees at every specified row. The result sharpens the source dimension 4q+1 and the number of witness circuits in the cited fleet theorem. [Fleet L-meta-043 receipt](https://data.pequalnp.com/data/lemma/L-meta-043.101d01304a2d.json)

The tests used Lean 4.36.0 with built Mathlib `fc4f59e577feb1a4956671bc04ac18aaaf8cd842` in the disposable guest. The 12 project helper source hashes match the published receipt in `fleet-pins.json`. The runner verifies the hashes, combines the original helper declarations in topological order with the new wrapper, and builds the result without fetching code. All three new endpoints report only propext, Classical.choice and Quot.sound. The physical replay log includes linter warnings in the upstream declarations. The first two modules need only the pinned built project definitions and Mathlib. The public-facing `ParityCircuit.lean` uses a normal project import and may instead be checked individually when that import is already built.

With a reviewed, built project checkout, from its pinned commit or a checkout whose helper sources pass the pinned hashes, use

```sh
PROJECT_LEAN_ROOT=/absolute/path/to/pequalnp-proofs/lean sh check-package.sh
```

The original paper behind the fleet's neighbor-witness technique is Allender, Ilango and Vafa, *The Non-Hardness of Approximating Circuit Size*. [Primary paper](https://doi.org/10.1007/s00224-020-10004-x)
