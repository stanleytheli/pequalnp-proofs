# Positive graph probability limits at the cube midpoint

The Boolean support of a positive, midpoint-bounded limit of independent-set probabilities on any N-vertex bipartite graph is a conjunction of at most N+|L||R| clauses. Each clause uses one vertex's affine positivity condition or the disjunction for an opposite-side pair. The converse realizes all CNFs. The complete finite-dimensional support theorem is kernel-checked in Lean, from the Bernoulli event law through the shared literal clauses. The additional statements below have written mathematical proofs and targeted finite controls.

| Manuscript | Result |
|---|---|
| midpoint-theorem.md | Common subsequence, lattice of positive covers, the shared CNF, and ordinary unscaled realization on ≤N+2 vertices |
| permanent-support.md | The minimum bipartite graph order for Boolean perfect-matching support is 2^{3m/2+O(log m)} on m×m input matrices |
| consequences.md | Superexponential graph-order requirement for directed Hamiltonian support, matching parity bounds, and tradeoffs with deletion to bipartiteness |
| degree-two.md | Positive supports on paths and cycles at locality d have width-3d CNFs. Odd cycles realize all such CNFs using polynomial size when the CNF has polynomial size |
| decomposition-width.md | Positive midpoint supports of polynomial-size graphs of fixed pathwidth or treewidth give nonuniform NC¹; logarithmic pathwidth gives NL/poly and logarithmic treewidth gives nonuniform SAC¹ |
| monomial-normal-form.md | The whole limit on a fixed graph has a one-parameter monomial realization. On bipartite graphs every vertex exponent is at most its degree plus one. Repeated five-cycle substitution shows an exponential lower bound for fixed labeled forms on general graphs |

These bounds use cube-preserving affine entry probabilities, positive scaling and boundedness at the midpoint. The limiting support classifications differ when only Boolean-corner convergence is required. The signed arithmetic constructions that transfer Hamiltonian hardness use constants beyond the probability interval. None of these bounds decides Boolean P versus NP. Priority for the combinations presented here has not been established.

## Verification

The main theorem is `Midpoint.cube_graph_CNF` in `CubeGraph.lean`. Its inputs are finite bipartite vertex types and a finite set of input coordinates. Every vertex has an affine table of absence probabilities in [0,1] on the Boolean corners. Its value at the true cube midpoint is the average of its values at zero and one. The theorem assumes finite pointwise convergence on Boolean inputs and a single uniform bound on the scaled midpoint probability. It constructs two families of literal clauses and the fixed singleton and opposite-pair requirements whose conjunction is precisely positive support. Affine interpolation from corner tables to the real cube is unique. The applications and asymptotic estimates are developed in the manuscripts separately.

Set `MATHLIB_PROJECT` to an installed Lean 4.36.0 mathlib checkout, then run `sh replay.sh`. Python checks require only the standard library. Run `python3 check_midpoint.py`, `python3 check_paths.py` and `python3 check_hall.py`. The recorded outputs and the axioms of the main checked statements appear in `verification.txt`. This packet uses only original proof sources and official mathlib.
