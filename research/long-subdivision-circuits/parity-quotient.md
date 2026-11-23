# Computing the optimum from the original graph

Let H be a long subdivision as in the circuit theorem. Mark each original edge odd or even according to its replacement path length. The minimum circuit size can be recovered from a smaller vertex-cover instance on the original graph.

Form the connected components of the even edges on the full original vertex set, including isolated vertices. For each component K let v_K and p_K denote its numbers of vertices and even edges. Contract each component to one vertex. Delete the vertices for components containing cycles and all their incident edges. Retain the odd edges between the remaining vertices. An odd edge internal to a surviving component becomes a loop, which forces its vertex into every cover. Parallel edges can be merged. Call this final graph Q.

The exact formula is

    C(H) = |E(H)| − 1 + Σ_e h_e + Σ_K min(v_K,p_K) + τ(Q).

Here odd lengths are 2h_e+1 and even lengths are 2h_e+2. The circuit theorem supplies C(H)=|E(H)|+τ(H)−1. Its endpoint calculation expresses τ(H)−Σh_e as the minimum of |T| plus the number of even edges with an endpoint outside T, over all sets T meeting the odd edges.

If T meets an even component without filling it, add a vertex adjacent to T. Its unit cost is offset by at least one even edge whose two endpoints are now in T. The odd coverage persists. Repeating shows that an optimum takes either all or none of each component. Taking all costs v_K and taking none costs p_K. Every component containing a cycle has p_K≥v_K, so an optimum can take all of them. Each surviving component is a tree with p_K=v_K−1. Taking such a component costs exactly one more than taking none. The odd-edge constraints still requiring payment are exactly the edges and loops of Q. This proves the formula, and the argument also reconstructs a minimum cover and an optimal star circuit from any minimum cover of Q.

For example, when every path has even length, Q has no edges. The optimum then requires only component counts, and the construction runs in linear time on an explicit subdivision with its paths given. For mixed lengths, removing the forced loop vertices reduces the remaining optimization to ordinary simple-graph Vertex Cover. If that remaining graph is bipartite, a maximum matching supplies a minimum cover in polynomial time by Kőnig's theorem. The quotient construction applies to arbitrary base degree.

`verify_quotient.py` independently compares the quotient optimum with direct minimization over all original vertex subsets for every assignment of absent, odd, or even to each potential edge on up to five vertices.
