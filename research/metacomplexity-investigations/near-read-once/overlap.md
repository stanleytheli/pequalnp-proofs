# Minterm and zero-certificate overlap measures excess gates

Let f depend on all N≥2 variables. Suppose a single-output acyclic circuit with g binary AND or OR gates computes f. Fanout is free. For every minterm M and every minimal zero certificate Z,

    g ≥ N−2+|M∩Z|.

Here a minterm is an inclusion-minimal true set of ones. A minimal zero certificate is an inclusion-minimal set whose forced zeros make f false. The gate count is over a syntactically monotone basis. The spike examples in `oracle.md` attain this inequality for arbitrarily large intersections.

Trim gates outside the output cone. Regard the remaining wires as edges of an undirected multigraph with vertices for the gates and primary inputs. Retain separate edges for repeated operand slots. All N essential inputs occur and this graph is connected. It has cycle rank β=2g−(N+g)+1=g−N+1. If trimming removed gates the lower bound for the smaller circuit also holds for the original one.

At input 1_M trace the true output backwards, retaining both operand slots at a visited AND and one true operand at a visited OR. At a gate reached from several readers make the same choice each time. The connected resulting graph T is a certificate for truth given its selected primary leaves. They are exactly M. Every leaf lies in M, and a proper subset would contradict minimality. Trace the false output at input 1_(V minus Z) in the dual way. The resulting connected graph U takes both slots at visited ORs and one false slot at visited ANDs; its leaves are exactly Z.

In T∩U each common gate has exactly one edge leading to a predecessor: one trace kept both slots and the other selected one. A common primary vertex is a sink, and all sink vertices are the |M∩Z| common leaves. In the orientation towards inputs each vertex has at most one outgoing edge, and there is no directed cycle. Following the unique outgoing path assigns each vertex to a sink, and endpoints of any edge have the same sink. Every connected component therefore has exactly one sink. Equivalently the intersection is a forest with Euler characteristic |M∩Z|. Both traced graphs contain the output so their union is connected. Inclusion-exclusion for numbers of vertices and edges gives

    β(T∪U) = β(T)+β(U)+|M∩Z|−1 ≥ |M∩Z|−1.

The cycle rank of a subgraph is at most that of the full graph. Comparing the two expressions proves the result.

In hypergraph terminology, the family of minterms of f is r-exact if each of its edges meets every minimal transversal in at most r vertices. This parameter and its fixed-r dualization algorithms have been studied directly for explicit hypergraphs. The inequality above gives a sufficient circuit-size condition for r-exactness, with r=g−N+2. The explicit hypergraph may have many more edges than the circuit has gates. [Polynomial-time dualization of r-exact hypergraphs with applications in geometry](https://doi.org/10.1016/j.disc.2010.05.017)
