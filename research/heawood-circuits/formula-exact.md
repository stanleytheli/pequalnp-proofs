# Exact monotone formula size for graphs without triangles or four-cycles

Let G be a finite simple graph with m>0 edges. Suppose G contains no triangle and no cycle of length four. If τ is its minimum vertex-cover size, the monotone binary formula leaf size of its edge function is exactly m+τ. Its binary formula gate size is m+τ−1.

The edge function tests whether the variables set to one include both endpoints of an edge. A minimum vertex cover gives the upper bound: assign each edge to an endpoint in the cover and compute the OR of the resulting stars. A star with t assigned edges has t+1 variable occurrences, giving at most m+τ in total.

For each edge f={a,b}, form the independent set

  I_f = (N(a) ∖ {b}) ∪ (N(b) ∖ {a}).

Any edge within either neighbor set would make a triangle. An edge across the two sets would make a four-cycle. The sets are disjoint because a common neighbor of a and b would make a triangle.

Consider the deterministic monotone Karchmer–Wigderson protocol induced by a formula. The positive player receives the two-element set e, indexed by an edge. The negative player receives I_f, indexed by another edge. Start at the formula root. At each OR the positive player selects a true child using only e; at each AND the negative player selects a false child using only f. Fix the tie-breaking orders. Each leaf receives a rectangle in E×E; these rectangles are disjoint and together cover the grid. A leaf labelled v may receive (e,f) only when v∈e and v∉I_f. Constant leaves receive an empty rectangle.

For every e, orient e toward the endpoint selected by the protocol at (e,e). Write d_v for the degree of v, k_v for its resulting indegree and ℓ_v for its number of variable occurrences in the formula. Consider the submatrix with row and column indices the edges incident to v. If e and f are distinct in this submatrix, the other endpoint of e belongs to I_f, so v is the unique permissible leaf label. At a diagonal entry, the label is v exactly when the edge is oriented toward v.

Consequently the v-labelled leaf rectangles, restricted to this submatrix, partition the support of the matrix M_v with all off-diagonal entries equal to one and with ones on exactly the k_v assigned diagonal entries. Each such rectangle has real indicator rank at most one. Real rank subadditivity gives ℓ_v≥rank M_v.

- If k_v>0, the columns for assigned edges are the all-ones vector. For each unassigned edge i, the corresponding column differs from this vector by the i-th standard basis vector. These d_v−k_v standard vectors together with the all-ones vector are independent, as any one of the assigned coordinates tests the all-ones coefficient. Hence the rank is d_v−k_v+1.
- If k_v=0 and d_v≥2, M_v=J−I is invertible over the reals. A vector in its kernel has each coordinate equal to the sum of its coordinates; their common value is then d_v times itself, hence zero. Its rank is d_v.
- If d_v=1 and k_v=0, v is essential: the singleton of its neighbor and the edge obtained by adding v have different outputs. Its variable must occur in the formula, so ℓ_v≥1. An isolated vertex needs no occurrences.

In every case, ℓ_v≥d_v−k_v+1[k_v>0]. The degree sum is 2m and the total indegree is m. Vertices of positive indegree form a vertex cover. Summing proves that at least m+τ leaves are required. For binary formulas every tree with L variable leaves has at least L−1 gates, and the star construction achieves equality.

Applied to the Petersen and Heawood graphs this gives respectively 21 and 28 leaves, hence 20 and 27 gates. The same proof gives the exact value for every nonempty induced subgraph of either one. Shared internal wires require a separate argument because the rectangle that reaches a reused node can be a union of rectangles.

The edge-indexed independent sets are also used in Stasys Jukna's rank argument, stated as Theorem 7.2 of his *Boolean Function Complexity* with the lower bound m. The calculation here assigns the diagonal cells to endpoints and sums the local real ranks to obtain the additional τ term. No priority claim is made. [Stasys Jukna, *Boolean Function Complexity*, §7.2](https://web.vu.lt/mif/s.jukna/boolean/bool-V7.pdf)
