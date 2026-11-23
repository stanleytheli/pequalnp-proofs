# Exact circuit size on long subdivisions

Given a set of vertices of a graph H, its edge function tests whether the set contains an edge. Count binary AND, binary OR and unary NOT gates, allowing arbitrary sharing. If H is obtained by replacing every edge of a nonempty loopless graph by a path of at least seven edges with its own internal vertices, the minimum circuit size is

    |E(H)| + minimum_vertex_cover(H) − 1.

The manuscript proves this for mixed path lengths. For the uniform length seven, the answer reduces to 10M+τ(G)−1, where G is the original graph, M its edge count and τ(G) its minimum vertex-cover size. This yields NP-hardness for graph-described functions with maximum degree three and girth at least 21. The same reduction applies on the explicitly encoded graph class even when the decomposition is supplied. Independent research for the P vs NP collaboration, November 23, 2026.

## Proofs and related results

* `subdivision-minimization.md` gives the circuit argument, examples, the decision reduction and the mixed-parity extension. It links both upstream path-elimination lemmas and their contributors.
* `parity-quotient.md` reduces a mixed subdivision to one vertex-cover instance on contracted components. For all-even lengths a linear-time construction produces a smallest circuit.
* `approximation-gap.md` gives the quantitative transfer from the Berman–Karpinski bounded-degree Independent Set gap and states the source's reduction model.
* `AUDIT.txt` records which declarations were checked with the original pinned Lean project and which parts are mathematical arguments. The original project and the upstream repository's acceptance process are independent of this research branch.

The girth bound can depend on input size. For every fixed α strictly between zero and one, the reduction can produce graphs on N vertices with no cycle shorter than N^α. It uses longer paths and still has polynomial output size. `GirthGrowth.lean` checks the integer size inequalities.

## Lean verification

`SubdivisionTheorems.lean` proves the exact physical circuit threshold, exhibits a circuit attaining the minimum, and proves the direct seven-edge equivalence from an arbitrary indexed base graph with at least two edges. Its dependencies include the unrestricted path reductions and the explicit circuit construction in this directory. The named declarations all passed the pinned VM kernel. `kernel-audits.txt` contains the 18 named axiom reports from the project and the supplementary Mathlib modules.

To rebuild, use an already-built copy of the project containing the merged `PEqualNP.Outside.L_meta_575` module, its pinned Mathlib, and the actual Lean 4.36.0 executable. The script builds fresh proof objects in a temporary directory and checks their reported axioms.

    python3 verify_proofs.py /path/to/pequalnp-proofs/lean --lean /path/to/lean-4.36.0/bin/lean

## Construct and check circuits

`optimal_circuit.py` takes a JSON file with a vertex count and triples of original endpoints and path length. The output lists input wires, gates, the output wire and a minimum cover. Original vertices have indices starting from zero. Each path receives consecutive private input indices in the order listed. The all-even case is linear. For general mixed inputs this reference implementation uses exact branching on the smaller vertex-cover instance.

    python3 optimal_circuit.py instance.json

An example input for the 21-cycle is `{"vertices":3,"paths":[[0,1,7],[1,2,7],[2,0,7]]}`. Its optimum is 31 gates. The three independent checks below require Python 3.10 or later and only its standard library.

    python3 verify_compiler.py
    python3 verify_mixed.py
    python3 verify_quotient.py

    python3 independent-multigraph-compiler.py

These checks compare explicit circuits with complete truth tables, calculate small vertex-cover optima independently, check both terminal outcomes of the path reductions and compare the quotient with direct minimization. The exact lower bound for unrestricted circuit size on the infinite family is a proof.
