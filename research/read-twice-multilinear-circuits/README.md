# Read-two Boolean formulas and their hard multilinear extensions

For an explicit family of subcubic bipartite graphs, deciding whether the selected vertices contain an edge has a linear-size monotone formula reading each variable at most twice. That formula attains the minimum size even among unrestricted fan-in-two AND/OR/NOT circuits with arbitrary fanout. The unique multilinear polynomial agreeing with the same Boolean function on the cube inherits the reported superpolynomial arithmetic circuit lower bound for Hamiltonian cycles, over every field, for both exact and coefficientwise-Laurent border complexity.

The reduction uses an exactly normalized ten-edge path. Constants at its internal vertices program a weighted hard-core interaction. Each matrix variable appears at just one physical input as 1−x. No limiting process is used for this exact specialization. The number of physical variables can be Θ(m²) for matrix order m. For a common stretch length L=10(6a+1), the family has N=Θ(m²L) vertices and girth at least 3L. For L bounded by a fixed polynomial in m, the inherited lower bound has the form exp(Ω((log N)^(4/3))). A read-once formula, in contrast, gives a linear arithmetic computation of its multilinear extension by independence at every binary gate.

The expander overlay also gives a direct, independent use of flattenings. With g=Θ(m²) long paths, both the edge and no-edge truth tensors require maximum bond 2^Θ(g) on every exact binary tensor tree after optimizing its shape. For fixed uniform additive error below 1/2, the optimum is 2^Θ(√g). Relative error for edge probability has the latter cost, while relative error for no-edge probability has the former. The write-up extends the additive statement to all symmetric Boolean functions of the g path violations at vanishing errors. Those tensor bounds have direct proofs using induced matchings, approximation of symmetric functions and pattern matrices; they do not use the new arithmetic separation.

## Attribution and relation to P versus NP

The arithmetic lower bound used as input is the Hamiltonian-cycle theorem reported in Anthropic’s formal-math release at commit `11b6c7e3c927df2658f513b6b68ea7f8929c62c5`. We examined the public theorem statement, manuscript and CI. The entire upstream proof has not been independently replayed as part of this packet. Its subject is arithmetic circuits. These results leave Boolean P versus NP open. Earlier work includes Hrubeš’s hardness for multilinearizations of monotone 2-CNFs, and established expander-matching lower bounds in knowledge compilation. The local work specializes the graph family, proves the read and size constraints jointly and derives quantitative tensor approximation results. Priority of the combination has not been established. [Published Lean statement](https://github.com/anthropics/formal-math/blob/11b6c7e3c927df2658f513b6b68ea7f8929c62c5/vp-vnp/Statement.lean) [Hrubeš](https://eccc.weizmann.ac.il/report/2015/067/)

## What is verified

The file `verification.txt` names the Lean declarations and lists the independent finite tests. The Lean components cover normalized path signatures, nonvanishing over arbitrary characteristic, the contraction of an arbitrary seed, expansion over all physical spins, uniqueness of multilinear extension, read-once evaluation and rank lower bounds from an actual induced crossing matching. The exact and Laurent-border seed transfer are now both checked as explicit circuit simulations with at most 2 times the number of data leaves plus four new circuit nodes. The support-only triangular rank bound is checked over arbitrary fields. The manuscripts give the witness-to-Hamiltonian identification, quantitative sizes and expansion estimates, the tensor-tree upper and approximation bounds, and the transfer to the upstream complexity theorem. The entire combined result is not one end-to-end Lean theorem. The optimal Boolean lower bound uses the companion long-subdivision circuit results and their stated circuit model. [Earlier subdivision proof](https://github.com/stanleytheli/pequalnp-proofs/tree/a31fcb5bd01e0bd1ba8e58c7c7db40195392c5fa/research/long-subdivision-circuits)

## Reproduce

Use the extracted directory as the working directory. The Python programs need only the standard library. `check_specialization.py` without options exhausts the internal spins of both path types over selected finite fields. The `--physical` option constructs the physical graph and contracts it without referring to the seed witness. The expander-overlay control is memory intensive. The source for the smaller Hamiltonian seed is in `graph-transfer/`.

```sh
python3 evening/affine/check_specialization.py
python3 evening/affine/quadratic_seed.py
python3 evening/affine/check_specialization.py --physical 2 3 4 5
python3 evening/affine/check_specialization.py --quadratic --physical 2 3
python3 evening/affine/check_specialization.py --expand --physical 2
python3 evening/affine/check_approximation.py
python3 evening/affine/check_symmetric.py
```

For Lean, set `MATHLIB_PROJECT` to the location of an already installed mathlib4 checkout and run `sh replay.sh`. The recorded version is Lean 4.36.0 with mathlib `fc4f59e577feb1a4956671bc04ac18aaaf8cd842`. The script builds only the sources in this packet and writes compiled files to the extracted directory.
