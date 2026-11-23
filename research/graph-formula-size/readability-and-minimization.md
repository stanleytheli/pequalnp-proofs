# Variable budgets and exact formula minimization

For the edge function of a triangle-free, four-cycle-free graph G, each monotone formula F admits an oriented-star formula in which **no individual variable occurs more often than in F**. The variable-use statement is stronger than the total leaf count.

Indeed, let a_v be the number of F's leaves labelled v. Orient each edge to the endpoint selected on its diagonal protocol input as in formula-exact.md. If v has degree d_v and indegree k_v, the local rank bound gives

    a_v ≥ d_v − k_v + 1[k_v > 0].

Assign each edge to its head and form the OR of stars, omitting empty stars. The variable v appears once as a center if it is a head and once for each edge pointing away from it. Its number of occurrences in this formula is exactly the right-hand side. In particular a minimum-total formula and a minimum-maximum-occurrence formula can both be found among star formulas, although those objectives can choose different orientations.

## Connection with readability

The readability of a graph edge function is the least possible maximum number of occurrences of one variable in a monotone formula. Golumbic, Peled and Rotics asked in Problem 1.1 whether every triangle-free graph has a read-optimal formula obtained from a biclique cover. Every star is a biclique, so the coordinatewise conclusion supplies an affirmative answer on the subclass with no four-cycle. The cited question also includes graphs containing four-cycles, where bicliques can have several vertices on each side. [Golumbic, Peled and Rotics, *Chain Graphs Have Unbounded Readability*](https://arxiv.org/pdf/math/0610456)

For possibly different integer budgets b_v≥0, an orientation is acceptable precisely when every v with d_v>b_v receives at least d_v−b_v+1 edges. Vertices with d_v≤b_v have zero demand. To test feasibility, introduce a slot for each unit of vertex demand and connect that slot to all incident edges of its vertex. A bipartite matching saturating the slots selects distinct edges for the demands. Orient every other edge arbitrarily. An unsuccessful matching certifies impossibility, since some vertex set has greater total demand than the number of edges incident to it. The construction and a binary search over uniform budgets compute exact readability in polynomial time. readability.py returns either the star orientation or the obstructing vertex set.

In every nonempty d-regular graph of girth at least five with d≥2 the readability is ceil(d/2)+1. If a uniform budget b<d is feasible, adding all vertex demands shows d−b+1≤d/2. A budget b≥d also satisfies the resulting lower bound when d≥2. For the upper bound, orient an Euler circuit in each even-degree component. If d is odd, first pair the odd vertices and add edges to make degrees even, orient an Euler circuit, and discard the added edges. Each resulting indegree is at least floor(d/2). Substituting in the occurrence formula proves the claimed upper bound. The Petersen graph, the Heawood graph and the incidence graph of the order-three projective plane each have readability three. For a matching of positive size the readability is one.

## Exact total size is NP-complete to decide on this graph class

Input a finite simple graph H of girth at least nine, with at least one edge, and an integer B. Ask whether its edge function has a monotone binary formula with at most B gates. The exact size theorem places this decision problem in NP: a vertex cover of size at most B−|E(H)|+1 certifies yes.

For hardness start with a nonempty Vertex Cover instance (G,k), with m edges. Replace every edge by a path of length three with two new private interior vertices. The new graph H has 3m edges, and every cycle has length at least nine. If the old vertices selected in an H-cover are C, covering the three edges of a replacement path uses at least one interior vertex when C contains an endpoint and two when it contains neither. These counts are attainable independently on all paths. Hence

    τ(H) = m + min_C (|C| + number of G-edges missed by C) = m + τ(G).

The second equality holds because adding one endpoint of each missed edge turns C into a vertex cover, and an optimal cover itself misses no edges. The exact formula size of H is therefore 4m+τ(G)−1. Take B=4m+k−1. This is a polynomial many-one reduction from Vertex Cover. This complexity classification concerns optimization over formulas given an explicit graph description. It yields no separation of P and NP. [Karp, *Reducibility Among Combinatorial Problems*](https://doi.org/10.1007/978-1-4684-2001-2_9)

Jukna's Theorem 7.2 gives the earlier |E| lower bound on leaf count for the same class and uses local independent sets associated with edges and vertices. The improvements in this proof are the diagonal orientation, the separate occurrence bounds, and the matching star construction. These comparisons make no assertion of publication priority. [Jukna, *Boolean Function Complexity*, §7.2](https://web.vu.lt/mif/s.jukna/boolean/bool-V7.pdf)

Golumbic, Peled and Rotics asked in Problem 1.1 whether every triangle-free graph admits a read-optimal formula built from a cover of its edges by complete bipartite subgraphs. On a graph with no four-cycle each such subgraph is a star. The pointwise replacement therefore answers their question affirmatively on the triangle- and four-cycle-free subclass, including separate budgets for each vertex. The general triangle-free case allows non-star bicliques. [Golumbic, Peled and Rotics, *Chain Graphs Have Unbounded Readability*, Problem 1.1](https://arxiv.org/pdf/math/0610456)

## A density test and the read-twice case

Let H be the induced subgraph on vertices with degree d_v greater than their budget b_v. Variable budgets are feasible exactly when every S⊆V(H) satisfies

    |E(G[S])| ≤ Σ_{v∈S}(b_v−1).

Indeed the demand on S is Σ(d_v−b_v+1), and the number of edges touching S is Σd_v−|E(G[S])|. Hall's condition for all demand slots reduces to the displayed inequality. A partial selection of slots at vertices cannot give a stronger condition than selecting all their slots. This also handles a zero budget at a nonisolated vertex, which fails already on a singleton.

For a uniform budget two, this says the subgraph induced by vertices of degree at least three must be a pseudoforest (each connected component has at most one cycle). Such a graph and all its subgraphs have at most as many edges as vertices. Conversely a component with two or more independent cycles already violates the inequality. The recognition test is linear in the input graph. For a uniform budget one, the vertices of degree at least two must be independent, so the nontrivial components are stars.

More generally let p be the least possible maximum outdegree over all orientations of a nonempty graph. The exact readability here is always p or p+1: each occurrence count dominates outdegree, and an orientation attaining p incurs at most one additional center occurrence per vertex. The density test decides between the two possibilities.
