# A constant approximation gap

The exact seven-edge formula also transfers a quantitative gap for bounded-degree Vertex Cover. Use Theorem 3 of Berman and Karpinski, with the reduction guarantees of that paper. For each sufficiently small positive ε, their independent-set instances have 284t vertices and maximum degree three. Distinguishing an independent set larger than (140−ε)t from a maximum independent set smaller than (139+ε)t is hard. Taking complements gives vertex-cover thresholds (144+ε)t and (145−ε)t. [Berman and Karpinski, ICALP 1999, Theorem 3](https://www.cs.umd.edu/~gasarch/TOPICS/pcp/BK99.pdf)

Let M be the actual number of edges of the instance. Then M≤426t by the degree bound. Its seven-edge subdivision H has minimum unrestricted circuit size C=10M+τ(G)−1. The two endpoint thresholds for C are

    L = 10M − 1 + (144+ε)t,
    U = 10M − 1 + (145−ε)t.

Their ratio satisfies U/L ≥ 1 + (1−2ε)/(4404+ε). Indeed U−L=(1−2ε)t and L≤(4404+ε)t. Both thresholds are computed from the input, including M.

For every fixed 1≤ρ<4405/4404, choose ε small enough that ρL<U. A procedure returning any value A with C≤A≤ρC would distinguish the two cases by comparing A to U. This includes algorithms returning a correct circuit with at most ρ times the optimal number of gates. The additional graph transformation is deterministic and linear in the graph description. The explicit constant inherits the original independent-set gap's reduction model, which uses randomized constructions. The exact decision reduction in the main manuscript uses ordinary Vertex Cover directly.

The graph input to this minimization problem has maximum degree three and girth at least 21. This is a multiplicative gap for the total gate count, including the fixed contribution of all subdivision edges. As the fixed path length increases, the same argument gives a smaller positive constant gap for each fixed girth requirement.

## Related circuit work

Quadratic Boolean functions and their monotone circuit complexity have a substantial literature. Amano and Maruoka treat both single-level and general monotone circuits, including separations for the number of AND gates. The present size identity counts every binary AND, binary OR and unary NOT and permits unrestricted wire sharing on the specified long subdivisions. A priority determination would require a fuller comparison with prior work. [Amano and Maruoka, Algorithmica](https://doi.org/10.1007/s00453-006-0073-0)
