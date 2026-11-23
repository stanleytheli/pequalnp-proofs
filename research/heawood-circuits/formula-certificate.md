# The Heawood edge function requires 27 binary monotone formula gates

The Heawood graph has 21 edges. A monotone formula for its edge function needs **28 variable leaves**, hence at least 27 gates of fan-in at most two. The seven three-edge stars centered at all the point vertices give equality. A formula may use a variable at multiple leaves. A circuit in which each gate has at most one reader slot in the cone of its output gives a formula upon repeating the primary inputs.

## A signed weight on the monotone Karchmer–Wigderson game

A positive input consists of the endpoints of one edge. For each vertex \(z\), take a negative input \(I_z\) containing \(z\) and all its nonneighbors on the opposite side. This is independent. Give the cell for edge \(e\) and column \(I_z\) integer weight 2 if \(z\in e\), weight −1 if \(z\notin e\) is adjacent to the opposite-side endpoint of \(e\), and weight 1 otherwise. Each edge has total weight 8. On each side the endpoint contributes 2, its opposite-side neighbor has two other neighbors contributing −2 in total, and the other four vertices contribute 4. Across the 21 edges the weight is 168.

At an OR of the formula, choose the first child true on the positive input. Both children are false on the negative input. At an AND, choose the first child false on the negative input. Both children are true on the positive input. The positive player or the negative player therefore splits only its own side of the current rectangle at each gate. The formula's leaves partition the entire edge-by-column matrix into rectangles. A variable leaf labelled \(v\) contains only edges through \(v\) and only columns missing \(v\). Constants cannot label a reached leaf. This proof also permits nullary gates, unary gates and out-of-range references evaluated as false.

Suppose such a rectangle uses \(k\) of the three edges at \(v\). On the side of \(v\), the six other vertices share exactly one neighbor with \(v\). For \(2k\) of them this neighbor is selected and the column sum is \(k-2\). The other \(6-2k\) have sum \(k\). On the opposite side exactly the three neighbors of \(v\) are eligible. The \(k\) selected neighbors have sum \(3-k\) and the others have sum \(-k\). Any subset of the eligible columns contributes at most the sum of the positive column sums. For each \(k=1,2,3\) this upper bound is
\[
(6-2k)k+2k\max(0,k-2)+k(3-k)=6.
\]
Thus at least \(168/6=28\) leaves are needed. The proof allows negative weights because the leaf rectangles partition the matrix. A tree with binary and unary internal nodes has at most one more variable leaf than its number of gates.

## Vertex-deleted graphs

For a vertex mask \(U\), intersect the same 14 tagged negative rows with \(U\) and keep the remaining edges. The eligible columns for any remaining vertex are unchanged and every row subset is still a subset of its original three incident edges. Each remaining edge retains weight 8. This proves a lower bound of \(\lceil4|E(U)|/3\rceil\) variable leaves for every induced Heawood subgraph.

The graph is numbered with point vertices 0 through 6. Line vertices 7 through 13 have point neighborhoods 013, 026, 156, 045, 346, 235 and 124. The vertex mask has bit \(v\) set when vertex \(v\) is present. The numerical results are as follows.

| Mask | Vertices | Edges | Certified formula leaves | Exact formula gates |
|---:|---:|---:|---:|---:|
| 4091 | 11 | 14 | 19 | 18 |
| 8127 | 12 | 15 | 21 | 20 |
| 8175 | 12 | 16 | 22 | 21 |
| 8191 | 13 | 18 | 24 | 23 |
| 16383 | 14 | 21 | 28 | 27 |

For mask 8127 the supplemental integer matrix in `weights-8127.json` has total 2664 and maximum permitted leaf weight 133. Since \(2664>20\cdot133\), it certifies at least 21 leaves. Its columns are specified independent vertex subsets. For any fixed leaf variable and nonempty subset of incident positive edges, the greatest possible rectangle weight is obtained by summing all positive eligible column sums. The verifier checks every such choice, checks that every negative input is independent, and computes a matching upper bound by assigning all edges to stars at vertices of a minimum cover. Run `python3 verify.py` with the JSON file in the same directory. The verification uses only the Python standard library and integer arithmetic.

## Every subcubic bipartite graph without a four-cycle

Let \(G\) be any finite bipartite graph with maximum degree three and no four-cycle. Attach as many fresh neighbors as each original vertex needs to attain degree three. Give each new neighbor two private leaves. The enlarged graph remains bipartite and has no new cycles. Every original vertex and each of its neighbors now has degree three.

For every vertex \(z\) in the enlargement, keep the tagged negative set consisting of \(z\) and all opposite-side nonneighbors, intersected with the original graph. Repeated negative rows may have different tags. For an original edge \(ur\), where \(z\) and \(u\) are in the same side, give the cell weight

- 2 when \(z=u\).
- −1 when \(z\ne u\) is adjacent to \(r\).
- 1 when \(z\) and \(u\) have a common neighbor different from \(r\).
- 0 in all remaining cases.

Exchange the endpoints for tags on the other side. The three groups of two second-neighbors around \(u\) are disjoint by the four-cycle assumption. The weight on each side totals \(2-2+4=4\). At a variable leaf labelled by an original \(v\), eligible columns on its own side have nonzero weight only for those six second-neighbors. Eligible opposite-side tags are exactly the three neighbors of \(v\). The calculation for \(k=1,2,3\) above still gives a leaf cap of six.

Consequently every binary monotone formula computing the edge function has at least \(\lceil4|E(G)|/3\rceil\) variable leaves. Whenever the minimum vertex-cover size is \(\lceil|E(G)|/3\rceil\), the star upper bound matches. In particular every finite cubic bipartite graph without a four-cycle has exact formula leaf count \(4|E(G)|/3\). Either bipartition side is a cover of size \(|E|/3\), and maximum degree three rules out a smaller cover.

## Circuits that reuse bottom gates

The 27-gate lower bound for the full Heawood graph also holds if every gate with two or more reader slots takes its own inputs directly from the primary variables.

For a signal \(h\), let \(P(h)\) be the edges where it is true and \(Q(h)\) the tagged independent rows where it is false. Cutting a reused bottom gate out of the circuit gives an auxiliary input to the remaining formula. If \(h\) occurs \(r\) times as a leaf of that formula, these \(r\) leaves receive disjoint rectangles inside \(P(h)\times Q(h)\). The exact single- and double-rectangle capacities, and the sum of all positive cell weights in this Cartesian product, are shown below.

| Bottom gate | Largest rectangle | Two disjoint rectangles | Sum of positive cell weights |
|---|---:|---:|---:|
| AND of two same-side vertices | 0 | 0 | 0 |
| AND of opposite nonadjacent vertices | 0 | 0 | 0 |
| AND of adjacent vertices | 12 | 12 | 12 |
| OR of two same-side vertices | 12 | 17 | 24 |
| OR of opposite nonadjacent vertices | 8 | 16 | 24 |
| OR of adjacent vertices | 12 | 13 | 16 |

Run `python3 sharing.py` beside `verify.py` to check all 182 choices of two distinct inputs and an operation. It enumerates row subsets by Gray order, then takes maxima over subsets. Two rectangles are disjoint exactly when their row sets are disjoint or their column sets are disjoint, so a partition on either axis suffices to compute the third column. Repeated-input gates are identities and can be removed. Constants do not appear in a nonempty Karchmer–Wigderson rectangle.

For \(r=2\), the total weight of the auxiliary leaves is at most 17. For \(r\ge3\), it is at most 24. Both bounds are at most \(6(r+1)\). Cutting \(k\) shared bottom gates leaves a formula with at most \(s-k+1\) leaves if the original circuit has \(s\) gates. Each primary leaf contributes at most 6 and each auxiliary group contributes at most its leaf count times 6 plus a single extra 6. Therefore the entire weight is at most \(6(s-k+1)+6k=6(s+1)\), proving \(s\ge27\).
