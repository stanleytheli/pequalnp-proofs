# Exact formula size for sparse hypergraphs

Let H be a finite hypergraph with at least one edge and at least two vertices per edge. Assume distinct edges meet in at most one vertex and H has no Berge cycles of length three or four. A Berge cycle uses different hyperedges and different vertices at its successive intersections. Equivalently the bipartite incidence graph has no cycles of length four, six or eight. Write τ for the minimum size of a set of vertices meeting every hyperedge.

The monotone edge predicate accepts when the input contains an entire hyperedge. Its exact binary monotone formula size is

    Σ_{e∈H} (|e|−1) + τ − 1.

The coordinatewise theorem is more precise. For each formula F there is an assignment of one owner vertex to each edge e, from among its members. If d_v counts incident hyperedges and k_v counts edges owned by v, then F has at least d_v−k_v+1[k_v>0] occurrences of v. For this very assignment, group edges by owner. A group headed by v contributes x_v AND the disjunction of the conjunctions of all other inputs in each owned edge. This realizes all the coordinate bounds simultaneously. Choosing owners in a minimum transversal gives optimal total size.

To see the lower bound, test each positive row consisting of one full hyperedge e. For its negative diagonal test use vertices outside e that belong to hyperedges touching e. This set contains no full hyperedge. Otherwise take two members of the purported contained edge k. Their connecting hyperedges back to e are distinct by linearity, and distinct from both k and e. If their two attachment vertices in e coincide, they give a Berge triangle; if different, a Berge quadrangle. For the independent test at a single vertex v, take the union of the other vertices of all edges containing v. An analogous pair of witnesses would create a Berge triangle.

Run the monotone formula protocol on these positive and negative tests. Each edge's diagonal selects an owner in that edge. Among rows touching v, different edge indices give forced label v off the diagonal, and the vertex-specific negative test forces label v throughout its column. The rank argument for the graph proof applies to every vertex separately. Summing the non-owner occurrences contributes Σ(|e|−1); the distinct owners form a transversal.

The formal statements hypergraph_orientation and exact_hypergraph_size in HypergraphFormula.lean use these explicit linearity and Berge-cycle assumptions and the same formula type as the graph theorem. They include the matching upper construction for nonuniform edges.
