# Exact monotone formula size for graph edge functions

Let G be a finite simple graph with at least one edge, with no triangles or four-cycles. Its edge function accepts precisely the vertex sets that contain both endpoints of an edge. Every monotone binary formula computing this function needs at least |E(G)| + τ(G) − 1 gates, and a construction from a minimum vertex cover attains that value. Here τ(G) is the minimum vertex-cover size. Input and constant leaves are free.

The manuscript in formula-exact.md gives the argument. FormulaRank.lean proves the lower bound, constructs the matching formula and checks the exact size over official Mathlib. The proof partitions a communication matrix into leaf rectangles. The leaf reached on the diagonal orients each edge toward one endpoint. Around each vertex, real matrix rank bounds its number of occurrences in the formula. Summing those bounds accounts for both the edge count and a vertex cover.

For the exact 52 incidences and 26 inputs in project search L-meta-650, ProjectivePlane650.lean proves that the minimum is 64 formula gates. The incidence certificate includes a matching of 13 edges and a cover of 13 points. The Heawood and Petersen formula minima are 27 and 20 by the general argument.

The project searches for smaller circuits allowing shared intermediate wires. The separate local-auxiliary.md excludes a class of such circuits on the order-three plane, using an arbitrary private auxiliary circuit with support up to 14 and a specified star output. We verified its finite calculation by two different optimizations.

## Reproduction

Use a Mathlib workspace with Lean 4.36.0. From that workspace put these source files in the same directory and include that directory in LEAN_PATH alongside the environment supplied by Lake. Compile FormulaRank.lean to FormulaRank.olean before checking ProjectivePlane650.lean. Both kernel checks succeeded in the disposable project VM. Their principal theorem axiom reports are in AUDIT.txt.

For the local auxiliary calculation, use a C++17 compiler and Python 3.10 or later. The independent Python program recomputes all 26 maxima from a vertex-cover optimization. It requires only the standard library.

    c++ -O3 -std=c++17 support.cpp -o support
    ./support
    python3 check_support.py

## Variable occurrences and shared circuits

PointwiseFormula.lean proves the per-variable bound from the diagonal orientation. ReadOptimal.lean constructs a formula that computes the same function and uses every individual variable at most as often. It is an OR of stars, with each edge owned by one endpoint. These files depend successively on FormulaRank.lean. Compile them in that order using the same local Lean search path.

The matching algorithm in readability.py either constructs a formula meeting specified variable-use budgets or returns a Hall obstruction. Run python3 readability-check.py for 1,384 comparisons with exhaustive orientation, plus witnesses for the Petersen, Heawood and order-three incidence graphs. The proof and graph-input complexity result are in readability-and-minimization.md.

The paper proof in shared-or-formulas.md extends the exact bound to circuits whose final stars can share arbitrarily through an OR network fed by raw variables and private monotone formulas. A separate formal result, Collision650.lean, gives a necessary condition on any 63-gate witness on the order-three incidence graph. It uses the project's physical circuit definitions. In the project Lean workspace, first compile StandaloneOneSided.lean and ProjectivePlane650.lean, then Collision650.lean.

TwinBlowup.lean imports ReadOptimal.lean and proves the pointwise statement also for graphs obtained by replacing vertices by nonempty independent twin classes. Each replacement term is now a complete bipartite subgraph. The twin-blowups.md manuscript derives uniform readability, exact weighted formula size, an exact unrestricted circuit-size identity and an explicit family with an unbounded formula-to-circuit size ratio.

A second paper argument, one-internal-and.md, permits shared OR gates on both sides of one auxiliary AND of any two input sums. Even when their raw OR subexpressions have other readers, the usual m+τ−1 lower bound survives. The same manuscript proves the bound for arbitrarily many independent ANDs with wide, almost-disjoint operand pairs sharing raw OR gates.

With several independent auxiliary ANDs, the exact bound also holds when their two raw supports are disjoint and have at least three labels each, and each final AND retains a wholly raw OR operand. Vertex degree and OR sharing are unrestricted. The proof assigns each newly created pair of stars to a component and counts the terminal ANDs that disappear. [Several wide auxiliaries with raw OR partners](wide-auxiliary-raw-partners.md)

The paper proof in sparse-shared-trunk.md treats arbitrary nesting above shared gates with small positive-edge footprints and explains when their outputs can be removed without increasing formula size.

For all graphs without triangles or four-cycles, one earlier AND can feed arbitrary terminal ANDs through a shared OR circuit. Both inputs of a terminal may be OR signals, and vertex degree is unrestricted. The minimum remains |E| + τ − 1. The proof counts the repeated incidences of restored stars and the OR gates removed when their shared signal is set to false. [Arbitrary terminal ANDs above one earlier AND](arbitrary-terminal-one-earlier-and.md)

## Hyperedges, graph density and two layers of shared computation

HypergraphFormula.lean proves the exact binary monotone formula size for every finite linear hypergraph with edge sizes at least two and no Berge triangles or quadrangles. The answer is the sum of |e|−1 over edges, plus the transversal number, minus one. The accompanying hypergraph-formula-size.md describes the negative inputs and the matching construction. This module imports FormulaRank.lean.

ReadBudgets.lean, ReadDensity.lean and RegularRead.lean form a sequence after ReadOptimal.lean. They machine-check the Hall characterization, its induced-subgraph density equivalence and the exact readability ceil(d/2)+1 for all nonempty d-regular graphs of girth at least five and d≥2.

The paper proof in two-and-layers.md covers every finite graph without triangles or four-cycles, of maximum degree at most four. Arbitrarily many ANDs of raw OR signals can share the OR computation feeding their operands. Another shared OR network feeds the final ANDs, each of which has a raw vertex input. The minimum in this class is |E| + τ − 1 for a graph with at least one edge. It is 64 for the order-three plane and 27 for Heawood. The manuscript gives the circuit argument and its complete gate count.

TaintedOR.lean and TaintedLocal.lean kernel-check the error-tolerant OR-query lower bound used in that count. Compile TaintedOR.lean first and then TaintedLocal.lean. ORReplacement.lean independently checks the operand choices from the three-vertex conditions, and the operand-slot count when signals are set to false. It imports only Mathlib. OptimalReads650.lean shows that a minimum 65-leaf plane formula reads every vertex on one entire side exactly once.
