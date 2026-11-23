# Exact monotone circuit sizes for graphs of girth at least five

For each graph in the catalogue the inputs indicate a set of vertices. The output is true exactly when that set contains both endpoints of an edge. Size counts binary AND and OR gates, allows an intermediate wire to be read any number of times, and excludes the input wires.

Every simple graph without triangles or four-cycles on at most **nine nonisolated vertices** has optimum size **|E| + τ − 1**, where τ is minimum vertex-cover size and the graph has at least one edge. The nine-vertex calculation covers 179 isomorphism classes and 22,771,971 labeled graphs. Both the graph generation and the circuit-size lower bounds have independent checks. The lower-bound calculation can start with just the one-edge graph.

On ten nonisolated vertices there are 576 classes and 864,497,179 labeled graphs. The lower and upper bounds agree on 575 classes. The Petersen graph with one edge removed needs exactly 19 gates. The Petersen graph itself is the remaining case, with an unrestricted circuit size between 18 and 20 gates. The accompanying formula proof gives an exact value of 20 when every internal gate has a single reader. In each row of ten-results.txt the entries are the graph mask, the lower bound and the upper bound.

## Reproduce

Use a C++17 compiler and standard Python 3. The nine-vertex check first validates coverage and constructs an upper-bound circuit for each graph. It then rebuilds the search executable and checks every lower bound from the two-vertex base.

    python3 reproduce.py 9

The ten-vertex command includes the full nine-vertex calculation before using it on induced subgraphs. It progressively increases the length of the enumerated prefix for cases whose bounds still differ.

    python3 reproduce.py 10

A shorter coverage check recomputes automorphism group sizes and counts admissible labeled vertex extensions, checks that the listed graphs are pairwise nonisomorphic, and verifies every stated upper bound on the entire Boolean cube.

    python3 reproduce.py 10 --coverage-only

For vertices numbered 0 through n−1, mask bits encode the pairs (i,j) with i<j in lexicographic order, starting at bit zero. Every isolated vertex can be fixed to zero without changing the optimum on the nonisolated subgraph. The edgeless function is constant and excluded from the displayed formula.

## Why the gate search proves lower bounds

A monotone function is determined by its minimal positive inputs and maximal negative inputs. Here those are the edges and the maximal independent sets. They fit in a machine word for the cases in this package. A minimum live circuit has binary gates on distinct earlier wires. A repeated operand, unused gate, unary gate, constant or missing wire can be eliminated by substitution and constant propagation.

Let a minimum circuit have n essential inputs and k gates. Every wire in the output cone except the output has a reader. Counting the 2k input slots gives k−n+1 as the total excess of fanout above one. This identity counts two distinct slots separately.

Fix some original inputs and retain a smaller induced graph K with no isolates. Additional vertices can be fixed to one provided they form an independent set anticomplete to K. One may also leave some of their neighbors free. The residual function then equals the edge function of K OR the free singleton terms. Fixing each free term to zero in turn removes at least one gate, so the extra terms do not reduce the bound on k−n+1.

Suppose p input wires are pinned and c gate outputs become constant. Every constant wire has a reader because the original output was nonconstant after restriction. Its outgoing slots end either at a constant gate or at a nonconstant gate with exactly one constant input. Write b for the number of those latter gates. Counting slots from both ends shows that the c+b removable gates are exactly

    p + sum over constant wires of (fanout − 1)
      + sum over constant gates of (2 − number of constant inputs).

A nonconstant gate giving the same values as an earlier wire on the residual extremal assignments can also be removed when it has no constant input. More generally, one can substitute an earlier signal if doing so raises values only on positive tests and lowers values only on negative tests. Propagating these changes forward preserves output correctness. The ten-vertex program also uses this observation to clamp suitable signals to constants. Any gate removed for two reasons receives one count.

The algorithm enumerates an initial segment of an unknown optimal circuit. For a fixed prefix, every positive and negative row must be distinguished, in the positive direction, by some signal read by the suffix. Wires with zero readers so far must be read later. For other wires each pair of still-undistinguished rows gives a clause requiring another read. The program computes inclusion-minimal sets hitting these clauses. Every actual completion contains one such set, and each chosen wire contributes an additional reader to its original fanout. The same choice must survive every restriction. When none survives, the prefix is impossible within the size budget.

To shorten the prefix search, write a signal as safe if it never accepts a negative input. Choose a minimum circuit with as few unsafe gates as possible. An AND reading a safe operand can be bypassed by that operand, preserving all extremal constraints. If an unsafe OR reads a safe wire h, clamp its downstream uses to false, remove the resulting redundant OR, and OR h back into the output. When h is false this preserves the old computation and when h is true the target is already true. Gate count does not increase and the number of unsafe gates drops. Thus safe AND sources feed a final tree of safe ORs. With t sources this suffix has 2t−1 gates. Its feasibility at a fixed unsafe prefix is exactly a finite set-cover test on the edge rows. Each safe source is the intersection of two prefix signals and must miss all maximal independent sets. Also, any unsafe gate which lights only one edge can be replaced by the AND of that edge's two raw endpoints, preserving that positive row and improving the negative rows. An unsafe gate lighting no edge can be removed. Thus the search only adds unsafe gates lighting at least two edges.

The search fixes one representative of each input symmetry and commutation and uses a lexicographically least topological listing to avoid redundant prefixes. Restriction bounds use only smaller graphs. A prefix which escapes the charge at the depth limit leaves the bound open. A successful lower-bound proof excludes every prefix at the stated budget.

## General formula theorem

The proof in `formula-exact.md` gives the exact monotone binary formula size |E| + τ − 1 for every finite nonempty graph with neither triangles nor four-cycles. It applies at all degrees and graph sizes. Its argument partitions a communication matrix into rectangles and assigns each diagonal entry to one endpoint of an edge. The 575 finite ten-vertex equalities additionally allow arbitrary fanout.

The final ten-vertex program compares every candidate gate with other pairs of available operands. Among minimum circuits with the fewest unsafe gates, choose one maximizing the sum, over its gates, of the number of positive test rows accepted and negative test rows rejected. Improving both sets weakly and at least one strictly increases this sum after replacement, since downstream gates are monotone. If the two patterns agree, choose the lexicographically least topological description. A same-cost gate on earlier operands with a smaller description can then replace the candidate. A replacement that makes a gate unused or safe already improves one of the preceding optimization criteria.

## Formal results

The circuit-size enumeration and coverage tests are external computations. The separate OneSided.lean file proves a general lower bound for C4-free bipartite circuits under its stated no-collision condition, and extracts an explicit collision from an unrestricted counterexample. It was independently kernel-checked with the project's pinned Lean and Mathlib and the project's circuit definitions. Its final theorems are PEqualNP.Outside.Rectangles624.collision_free_graph and PEqualNP.Outside.Rectangles624.collision_of_counterexample.
