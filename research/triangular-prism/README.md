# Ten gates for the triangular prism

The smallest monotone circuit with binary AND and OR gates computing the triangular-prism edge function has **ten gates**. This answers the eight-gate existence question in P vs NP project row L-meta-618 negatively. The positive construction is a Lean theorem checked against the project definitions. The lower bound below is a reproducible exhaustive computation with an elementary completeness argument.

Label the triangular faces 0,1,2 and 3,4,5. The three matching edges are 03,14,25. An assignment is accepted when it includes both endpoints of an edge. The nine edge pairs are the minimal true assignments. The six remaining pairs are the maximal false assignments, since the complement is a six-cycle with no triangle. Monotonicity fixes the other 49 answers. Every vertex is essential, as can be seen using any adjacent vertex alone and then adding the vertex.

## Ten-gate construction

Number inputs 0 through 5, then number new wires from 6 in the following order.

| Wire | Operation |
|---|---|
|6|1 OR 3|
|7|2 OR 4|
|8|1 OR 5|
|9|4 OR 5|
|10|2 OR 6|
|11|7 AND 8|
|12|3 AND 9|
|13|0 AND 10|
|14|12 OR 13|
|15|11 OR 14|

The output is wire 15. The project-importing file `TriangularPrism.lean` checks the size, monotonicity, and the output on all 64 assignments via the Lean kernel. It was checked with Lean 4.36.0 at project revision a285ace2301a31d8cdea9fd9e718bca202b4d06d.

## Exhaustive lower bound

Compile and run the self-contained search with any C++17 compiler.

    c++ -O3 -std=c++17 enumerate.cpp -o enumerate
    ./enumerate 5 9

If a circuit realizing the required answers on the 15 pairs exists, choose one of smallest size. The boundary argument above makes every such circuit globally correct, so its output depends on all six variables.

Discard gates outside the output cone. Unavailable wires in the project's semantics read false. AND with false gives false and OR with false copies its other input. Repeatedly simplify these constant or copying gates. If a gate has the same 15-bit truth vector as an earlier available wire, redirect uses to that wire and delete the gate. On the 15 deciding assignments this preserves the function, hence it preserves it everywhere. Thus a smallest circuit has neither kind of redundancy. At least five gates are required, since a connected binary output cone with six input vertices and k gates has at most 2k edges and needs at least 6+k−1.

Traverse this directed acyclic circuit from its output. The first visit to a gate creates a binary tree node. Any later visit to the same already completed wire is a leaf reference. Inputs are introduced in order of first use, with all input renamings checked by comparing the final truth mask against the graph's 60 relabelings. A depth-first traversal cannot encounter a previously opened unfinished ancestor, since the circuit is acyclic.

At a newly visited gate, count the as-yet undiscovered gates reachable from each child, before exploring either child. Explore the larger cone first. Every undiscovered gate in that cone is then visited, while the other child can only lose undiscovered gates. Thus the left child introduces at least as many gates as the right child. The AND and OR inputs commute, so this is a permissible ordering at every node. The program generates every binary discovery tree meeting that size condition, including both orders for children of equal size. At each leaf it tries both a new input and every earlier completed wire when enough leaves remain. At each internal node it tries both gates. It refuses a gate whose 15-pair vector duplicates a completed wire. These rules retain a representation of a smallest realizing circuit.

| Gates | Discovery-tree shapes | Completed labeled computations | Matches |
|---:|---:|---:|---:|
|5|6|100|0|
|6|11|4,798|0|
|7|24|185,923|0|
|8|47|5,379,038|0|
|9|103|170,941,382|0|

The independent normalized SAT search also returned UNSAT at sizes 5 through 9. An additional eight-gate SAT encoding uses no gate ordering, liveness, or graph automorphism restrictions. It permits repeated operands, unused gates, and a constant false wire. A shorter circuit can be padded with gates that copy the selected output. The generated CNF has 737 variables and 63,674 clauses. The included checker independently verified a proof of the empty clause with 1,936,473 reverse-unit-propagation additions. The large certificate can be regenerated locally.

    python3 plain_cnf.py prism.cnf
    cadical --lrat --no-binary prism.cnf prism.lrat
    c++ -O3 -std=c++17 rupcheck.cpp -o rupcheck
    ./rupcheck prism.cnf prism.lrat

CaDiCaL returns exit code 20 for UNSAT. The certificate from the run used here ends at clause 2,000,147. Solver versions can generate different valid certificates. The lower-bound computations are external to Lean. The standalone enumerator does not require a SAT solver, a network connection, or the project repository.
