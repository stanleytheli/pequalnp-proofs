# Independent twin classes, variable budgets and weighted size

Start with any finite graph G having no triangles or four-cycles. Replace each vertex v by a nonempty independent set of t_v vertices. For each original edge, join every member of one set to every member of the other. Write H for this expanded graph. It can contain arbitrarily large complete bipartite graphs and four-cycles.

**Theorem.** Every monotone formula for the edge function of H can be replaced by an OR of complete-bipartite formulas that reads each individual input at most as often. Each term has a whole twin class on one side and a union of whole twin classes on the other. The edge sets of the terms partition E(H).

Given the formula, pick one member of each twin class having the fewest occurrences in that class. Set all other inputs to false and rename the chosen variables by their base vertices. The restricted formula computes the edge function of G. Its number of occurrences of each surviving representative is unchanged before simplification. Apply the pointwise star theorem. Finally replace each leaf v by the OR of all members of its class. This computes the edge function of H because an original edge has an active endpoint in each class exactly when an expanded edge is present. Each variable of the class occurs once for each occurrence of v in the base star formula, which is at most the original minimum in that class. Expanding a star centered at v gives precisely the displayed complete-bipartite term.

This proves the existence of a read-optimal complete-bipartite cover requested in Golumbic, Peled and Rotics' Problem 1.1 on this class of triangle-free graphs containing four-cycles. [Original question, p. 2](https://arxiv.org/pdf/math/0610456)

For variable budgets b_w on H, solve the matching instance on G with budget min_{w in class(v)} b_w at v. It is feasible exactly when the original problem is. The uniform readability of H equals the uniform readability of G. In fact equality of uniform readability under independent twin expansion holds for any base graph by specialization and substitution.

For a graph with at least one edge, the minimum gate count on H is

    min over orientations of G of Σ_v t_v (outdeg(v) + 1[indeg(v)>0]) − 1.

The upper bound counts variable leaves in the expanded orientation formula. Every formula dominates one of these formulas coordinatewise, giving the reverse inequality. Weighted leaf costs work as well when all weights are nonnegative: replace t_v by the sum of leaf costs of members of v's class before minimizing. For example, blowing up the two endpoints of a single edge gives the exact p+q−1 gates for K_{p,q}.

The class is recognizable from the graph alone. Merge vertices having identical open neighborhoods. They are independent twins. If the resulting simple quotient has no triangles or four-cycles, the construction applies directly. Conversely merging duplicate neighborhoods in an expansion and then choosing representatives in the base produces an induced subgraph of the base, so the quotient also has girth at least five.

## Unrestricted circuit size on the same graphs

Let C(G) denote the minimum physical gate count using binary AND and OR with arbitrary fanout. The same identity holds if unary NOT gates are also allowed. Assume G has an edge and no isolated vertices, and let W denote the expanded vertex set. Then

    C(H) = C(G) + |W| − |V(G)|.

For the upper bound build the OR of each class once and feed that wire to every original use. For the lower bound set all but one member of each class to zero, one input at a time. At every step the removed variable is essential: a neighboring class still has a representative. It must therefore have a reader in the live output cone. The output cannot be that raw variable, since no singleton contains an edge. After assigning zero, an AND or OR reader becomes a constant or an alias, and a NOT reader becomes a constant. At least one physical gate is saved at every step. Fold constants and aliases and continue. The final circuit computes the base graph.

For example, the 5-cycle has 7 gates in either circuit basis, as is verified in the finite graph catalogues. Replacing each vertex by t twins gives exactly 5t+2 gates with reusable wires, compared with exactly 8t−1 gates in a monotone formula. At t=2 the two optima are 12 and 15.

An explicit family gives an unbounded ratio. Take the incidence graph of a projective plane of prime order q. Each side has h=q²+q+1 vertices; the graph is (q+1)-regular with no triangles or four-cycles. It has a perfect matching by Hall's theorem and either side covers the edges. With t independent twins per vertex the formula minimum is exactly t(q+2)h−1. The circuit built from stars and shared twin-class ORs uses at most (q+2t)h−1 gates. In particular taking t=q gives a ratio of minimum monotone formula size to minimum monotone circuit size at least (q+2)/3, unbounded as q grows. This comparison uses only an upper bound on circuit size for the base incidence graph.
