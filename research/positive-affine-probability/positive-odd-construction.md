# A probability-preserving Hamiltonian border on nonbipartite read-two graphs

For every order \(m\ge2\), there is an explicitly generated, subcubic graph \(H\) of arbitrarily prescribed odd subdivision length \(2h+1\ge7\) with a known optimal read-two monotone Boolean formula. Its independent-set probability \(Q_H\) has a direct border specialization to the directed Hamiltonian-cycle polynomial over every field. At each positive real \(0<t\le1\), all substituted probabilities are cube-preserving affine functions of at most one target entry. Coefficients are integers, with no sign gadget or rational denominator. A single positive output rescaling \(t^{-W}\) selects the leading coefficient. The resulting graphs contain odd cycles.

## Records for satisfying assignments

Begin with the uniquely witnessed Boolean encoding of a directed Hamiltonian cycle described in [the signed seed construction](graph-arithmetic-transfer.md). It has one data bit per arc and a polynomial number of clauses of width at most three. The selected data bits of a satisfying witness describe its directed tour. This step also works with any fixed bounded-arity constraint verifier.

Form an unsigned compatibility graph \(B\). Give each Boolean bit a clique with its two truth-value records. Give each clause a clique with one record per satisfying assignment of its own distinct variables. Join a tuple record to the inconsistent truth-value record of each variable in its scope. Let \(k\) be the number of cliques. An independent set contains at most \(k\) records. Choosing one per clique is in bijection with satisfying assignments, because each clause's whole tuple is forced by the bit values. At least one full witness exists in the unconstrained Hamiltonian template. Mark the false record of each data bit by its corresponding matrix variable \(x_{ij}\). All other records receive marker 1.

Write \(r=|V(B)|\) and \(D=\sum_{v\in V(B)}\deg(v)\). All records have positive degree in the template. The graph size is linear in the number of source literal occurrences and variables.

## Alternating switches separate ordinary and weighted optimality

Replace a degree-\(d\) record by a cycle with alternating vertices \(P_1,N_1,\ldots,P_d,N_d\). For \(d=1\), use just the edge \(P_1N_1\). Give each old incidence its own port \(P_i\) and connect the corresponding two ports for each original edge. Call the resulting graph \(G\), with \(M\) edges. Every port has degree at most three; guards have degree at most two. The set of all guards is independent. Each cluster contributes at most \(d\) independent vertices, so this is an ordinary maximum independent set of size \(D\), with complementary known minimum cover consisting of all \(D\) ports.

For the weighted computation give each switch vertex reward 2, and give one distinguished port in each cluster reward 3 instead. Put its record's marker at this distinguished port. A cluster attaining its full unweighted size \(d\) chooses exactly one of the two alternating classes; this also holds for a one-edge cluster. In any independent set let \(S\) be the record clusters choosing all ports, and \(b\) the number of clusters below their maximum size. Then \(S\) is an independent record set. The total reward is at most
\[
  2(D-b)+|S|+b=2D+|S|-b\le2D+k.
\]
Equality holds precisely when every cluster is full and \(S\) is a complete witness. The choice of guards versus ports is then unique. The distinguished port of a false data record is absent exactly when its data bit is true.

## Odd paths with unique conditional maxima

Orient the edges of \(G\) in any way and replace each by a path of \(2h+1\) edges. Denote its two old endpoint choices by \(x,y\in\{0,1\}\), starting at the left endpoint. Put \(B_0=h+4\). Give its \(2h\) private positions alternating rewards \(B_0+1,B_0,\ldots,B_0+1,B_0\). The maximum private rewards for each pair of endpoint choices are:

| Endpoints | Maximum private reward | Unique maximizing private pattern |
| --- | ---: | --- |
| 00 | \(h(B_0+1)\) | all odd positions |
| 10 | \(hB_0\) | all even positions |
| 01 | \(h(B_0+1)\) | all odd positions |
| 11 | \((h-1)(B_0+1)\) | odd positions except the first |

Private patterns of lower cardinality lose more than the sum of all available unit bonuses, since \(B_0>h\). The 10 and 01 cases have odd-length remaining segments with unique maximum cardinality pattern. In the other cases the maximum-cardinality pattern taking all available odd positions is uniquely selected by its bonuses.

The table equals \(h(B_0+1)-h x-5xy\). Increase each old vertex reward from \(a_v\in\{2,3\}\) to \(a_v+h\,\operatorname{outdeg}(v)\). Thus for any selected old-root set \(R\) the optimized global reward becomes
\[
 h(B_0+1)M+\sum_{v\in R}a_v-5 e_G(R).
\]
If \(R\) contains a conflicting edge, delete at most one endpoint for each such edge to obtain an independent set. This loses at most \(3e_G(R)\) root reward while erasing the entire larger penalty. All maximizing sets therefore have independent roots. The switch argument and the unique private choices show there is exactly one maximizing physical configuration for each satisfying witness.

## Border identity and Boolean optimum

For a physical vertex of reward \(w\), give it selection probability \(1-t^w\), except at a marked distinguished port use \(1-t^w x_{ij}\). Its absence has probability \(t^w\) times the corresponding marker. In the independent-set sum the least possible power of \(t\) is the total physical reward less the largest selected reward, namely
\[
 W=2D+r-k+h(B_0+1)M.
\]
The coefficient at that power is the sum over complete witnesses of their data monomials. All selected vertex factors have constant coefficient one. Each data variable appears at exactly one physical input. Consequently \(t^{-W}Q_H=\mathrm{HC}_m+O(t)\) is an identity over \(\mathbb Z[x][t]\) after removing the explicit power, and it specializes to every characteristic. No ordering is needed for the identity; the real positivity statement follows by evaluating the same inputs on the real cube with \(0<t\le1\).

The unsigned odd subdivision has \((2h+1)M\) edges. Its cover has \(hM+D\) vertices: keep every old port and \(h\) alternating private vertices per path, starting at a port endpoint. The odd-path cover theorem makes this cover minimum. The long-subdivision physical lower bound gives exactly \((3h+1)M+D-1\) unrestricted binary De Morgan gates. To attain it, group the edges into stars at those centers. On each path assign every edge incident to an old port to that port and every other edge to its adjacent private center. When both old endpoints are ports this convention assigns the boundary edge between two centers to its old port; the private center still owns its other edge. Every old port occurs once. Every other physical vertex has degree at most two and hence at most two occurrences. The obtained monotone read-two formula is optimal. [Long-subdivision circuit theorem](https://github.com/stanleytheli/pequalnp-proofs/tree/a31fcb5bd01e0bd1ba8e58c7c7db40195392c5fa/research/long-subdivision-circuits)

Each tuple clique containing a triangle supplies an odd cycle in \(G\): the path between two ports inside an alternating cluster has even length. Odd subdivisions preserve this parity. The physical girth is at least \(3(2h+1)\). For fixed \(h\) the size is linear in the verifier. Choosing \(h\) polynomially in the verifier size gives girth at least \(N^\alpha\) for any fixed \(\alpha<1\), where \(N\) is the physical vertex count.

The construction relies on selecting a leading coefficient through a singular positive normalization. The [exact projection obstruction](probability-barrier.md) and [bipartite positive-border obstruction](positive-border.md) apply to their respective models.
