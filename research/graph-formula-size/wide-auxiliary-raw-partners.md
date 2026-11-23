# Several wide auxiliary ANDs with raw OR partners at the terminals

Let G be a finite simple graph with m≥1 edges, no triangles and no four-cycles. Its edge predicate accepts exactly the vertex subsets containing a graph edge. A raw OR signal is a disjunction of input variables; its support is the set of their labels.

Consider a monotone circuit with r independent auxiliary ANDs. Each multiplies two raw OR signals A_i,B_i whose supports are disjoint and each have at least three labels. Raw variables and auxiliary outputs feed a shared OR network. Each terminal AND takes one entirely raw OR signal and a second signal from this network. The output is the OR of these terminal terms. Both OR networks may reuse arbitrary gates, including shared subexpressions of the A_i and B_i. The minimum size among these circuits is m+τ(G)−1, where τ(G) is the minimum vertex-cover size. This allows the usual star formula with r=0.

Trim unused gates and propagate constants. Write c for the number of used terminal ANDs and q for the OR gates before them. Assign a raw side to each terminal, using its exclusively raw operand whenever the other depends on an auxiliary. With constants removed these raw operands are nonempty. The original size is at least q+r+2c−1.

## Edges supplied by a single auxiliary

Let K_i be the union of the raw sides of all terminal terms reached through an OR path from auxiliary i, including direct use. Its contribution to the original function is the product of the three sums with supports A_i,B_i,K_i. Indeed, each receiving terminal distributes over the disjunction of the auxiliaries in its other operand. Thus any choice of one vertex from each of those three sets contains a graph edge. On two-vertex inputs the contribution consists exactly of (A_i∩K_i)×B_i and A_i×(B_i∩K_i). Each intersection has at most one member, since two members would share all the neighbors in the opposite operand. A single nonempty intersection supplies a star with center in that intersection and the opposite raw signal as its query. Write s for the number of auxiliaries of this type.

An auxiliary with two nonempty intersections supplies two stars centered at p∈A_i∩K_i and z∈B_i∩K_i. Here B_i⊆N(p), A_i⊆N(z) and pz is an edge. Put A′=A_i∖{p}, B′=B_i∖{z}. Every pair a∈A′, b∈B′ is a nonedge, because an edge would close the four-cycle p,z,a,b. For any k∈K_i, safety on {a,b,k} now forces k to be adjacent to a or b. Consequently k is adjacent to every vertex in A′ or to every vertex in B′. Each of these sets has at least two members. The unique common neighbor can then only be z or p, respectively. In particular K_i={p,z}.

## Deleting the auxiliaries and counting raw queries

Set all auxiliary outputs to false. Let b be the number of terminal products that become zero, and δ the number of OR gates whose outputs become zero or which have one zero input. Delete all these OR gates and bypass every gate with one zero input. All original raw operand cones remain available. Each of the c−b surviving products is a raw star, since a complete bipartite graph in G has a singleton side. When its designated raw side is a singleton choose that label as its center.

We have r≤δ+b. To see this, consider the initially used auxiliary outputs and all z₀ zero OR outputs. Each of these r+z₀ wires is used in a zero-input operand slot. Such a slot enters one of the z₀ zero ORs, one of δ−z₀ mixed ORs or one of b dead terminal ANDs. The latter gates have at most one zero slot since each designated raw side is nonempty. Hence r+z₀≤2z₀+(δ−z₀)+b.

Form a simple graph D by placing an edge for each distinct unordered pair of double centers {p,z}. Write d=|E(D)|. Restore the affected stars using the appropriate original raw operands. At each center, group together the operands supplied by double auxiliaries having the same partner. Their raw supports all contain that partner. Each single-auxiliary operand and each surviving raw-star query gets its own group. The total number of groups is at most c−b+s+2d. Every restored raw query consists of neighbors of its center. Their union at each center counts all the original graph edges, and each of the d edges of D occurs at both its endpoints.

The union of the raw input cones of a group is connected, since its members share a raw label. For a center with union of labels U and g groups, the cones therefore contain at least |U|−g wide OR gates. This follows by folding single-label signals into the corresponding free input and applying the binary input bound to each connected component. Gates with two or more labels cannot be counted at two distinct centers, by four-cycle freeness. Summing gives

    q−δ ≥ m+d−(c−b+s+2d) = m−c+b−s−d.

## Counting newly used centers

Take the surviving residual centers and the centers of all single and double auxiliaries. They cover the graph. Each connected component of D meeting a residual center adds at most its number of edges in new vertices. A component disjoint from all residual centers adds at most its number of edges plus one. Every such component can be associated with a different dead terminal.

Indeed, choose a double auxiliary from the component. The nonempty designated raw side of any terminal it reaches is contained in K_i={p,z}. If that raw side is a singleton, a surviving terminal would have supplied a residual center in the component by the chosen orientation. If its raw side contains both p and z, then no nonempty raw residual partner could survive. Such a partner would have to contain only common neighbors of the adjacent vertices p,z, contradicting triangle freeness. Thus that terminal dies. Its nonempty designated raw side is contained in the chosen component, so distinct components give distinct terminal gates.

The total number of additional centers is at most s+d+b. Therefore τ(G)≤(c−b)+(s+d+b)=c+s+d. There are at least s+d auxiliaries, while b+δ≥r. The preceding OR bound gives

    q+r+2c−1 ≥ m+c−1 +(b+δ)+r−s−d
                ≥ m+c+s+d−1
                ≥ m+τ(G)−1.

The cover-star formula attains equality. The assumption of at least three labels per operand ensures that both A′ and B′ have two distinct vertices; the proof uses this when it restricts the entire set of raw partners for a double auxiliary.

## Unrestricted terminal operands for supports of size seven

If every A_i and B_i has at least seven labels, the lower bound also holds when both operands of every terminal AND may be arbitrary shared ORs of raw and auxiliary signals. No raw-partner condition needs to be imposed in this case.

In a graph without four-cycles, any four sets of at least seven vertices have an independent transversal. Here this means one may choose a vertex from each set so that the union of the chosen vertices is independent. Repeated choices of the same vertex are allowed. Trim the sets to seven vertices each. For any seven-set T, at most two vertices have at least four neighbors in T. Indeed, two distinct vertices have at most one common neighbor. The neighborhoods in T of three such vertices would therefore contain at least 12−3=9 different vertices.

Choose a vertex from the first set outside the exceptional vertices for the other three. There are at most six exceptions, so this choice leaves at least four nonneighbors in each remaining set. Retain four of them in each. In a four-set, at most one vertex has at least three neighbors, since two such vertices would share at least two neighbors. Choose a vertex in the next four-set outside the at most two exceptions for the last two. These last two sets now each contain at least two vertices adjacent to neither earlier choice. They have a nonadjacent cross pair: if the remaining sets meet, choose the same vertex in their intersection; if they are disjoint, a complete cross relation would contain a four-cycle. The four choices form the claimed independent transversal. An earlier choice may reappear later because the graph has no loops.

Suppose a terminal AND received auxiliary i via one operand and auxiliary j via the other. The indices may coincide. Apply the transversal assertion to A_i,B_i,A_j,B_j. On the resulting independent input both auxiliaries are true. Their OR paths make both terminal operands true, violating the edge predicate. Thus every terminal in a correct circuit has an entirely raw side. The preceding theorem gives the exact minimum m+τ(G)−1.
