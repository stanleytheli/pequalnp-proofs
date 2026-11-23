# Exact unrestricted circuit size after long odd subdivisions

Let G be any finite simple graph with M≥2 edges. For each original edge e choose an integer h_e≥3 and replace that edge by a path with 2h_e private internal vertices, of length 2h_e+1. Write H for the new graph. The input to an edge function is a choice of vertices and the function accepts exactly when the choice includes both endpoints of some edge.

The same proofs allow different original edges to have the same pair of endpoints. The endpoints of each individual edge must be distinct and its internal vertices private. In this slightly more general formulation G can be a loopless multigraph and H is still simple.

Count each binary AND, binary OR and unary NOT as one gate and allow arbitrary reuse of every wire, as in the collaboration's HasCircuitSize definition. If τ(G) is the minimum vertex-cover size, then the minimum circuit size for H is exactly

    3 Σ_e h_e + M + τ(G) − 1.

The same optimum is attained by a monotone formula. In particular, for these graphs the expression |E(H)|+τ(H)−1 is the exact answer even for unrestricted circuits.

## Lower bound

Use the project's checked path-elimination theorem L-meta-575. For a function formed by adjoining an odd path with 2h≥6 private inputs to g between distinct variables u,v, it gives an actual circuit for g with one pendant edge at u or at v, saving at least 3h gates. Its hypotheses require g to be nonconstant and to have a false assignment at each Boolean value of each endpoint. [Merged theorem and proof](https://github.com/brilliant-hq/pequalnp-proofs/pull/652)

At every step let g be the graph consisting of all the other paths and any pendants already produced. This graph has an edge because M≥2, even at the last step: each other original edge still has either its full path or a pendant. The all-false input is false, an edge input is true, and an endpoint singleton is false. This supplies all the hypotheses. Each new pendant can use a fresh coordinate. Renumbering input wires preserves the gate count. Iterating yields some choice of one original endpoint per edge, with one private pendant joined to each chosen endpoint.

The terminal forest has M different pendant vertices and t distinct chosen original vertices. All M+t inputs are essential: each can change the output when paired with the other endpoint of an incident edge. A connected output cone with fan-in at most two and s gates can depend on at most s+1 distinct raw inputs. Extra fanout and unary gates preserve this inequality, by counting the wiring edges of the connected cone. Thus the terminal circuit has at least M+t−1 gates. The t chosen endpoints cover G, so t≥τ(G). Adding the savings proves the lower bound.

## Matching upper construction

On a path of length 2h+1, suppose the selections at the two original endpoints are fixed. If at least one endpoint is selected into a cover, precisely h internal vertices suffice and are necessary. If neither is selected, h+1 are necessary and sufficient. This follows by alternating along the path, or by taking a matching of h internal edges (and the forced outside two when both endpoints are absent). The private interiors of different paths do not meet. Consequently

    τ(H) = Σ_e h_e + min_C [ |C| + number of original edges missed by C ]
         = Σ_e h_e + τ(G).

Here C ranges over subsets of original vertices. Add one endpoint of each missed edge to see the lower bound on the minimum; a minimum cover attains it. Also |E(H)|=2Σ_e h_e+M. Orient each subdivided edge toward an endpoint in a minimum cover of H. For each used endpoint z compute x_z AND (OR of its assigned neighbors) and OR the stars. An edge contributes one neighbor occurrence, each used center one center occurrence. The resulting formula therefore has |E(H)|+τ(H)−1 gates, proving equality.

For instance, replacing each of the three edges of a triangle by a path of length seven gives a 21-cycle. Its optimum is 31. Doing the same to the six edges of K₄ gives an example of maximum degree three with exact optimum 62.

## Complexity consequence

With h_e=3 for all e, the optimum is 10M+τ(G)−1. Map a Vertex Cover instance (G,k) to its explicit seven-edge subdivision H and threshold 10M+k−1. This gives a polynomial many-one reduction. The size of the graph description grows linearly in the size of G. Trivial instances with fewer than two edges can be decided separately.

On the language restricted to such subdivisions, membership in NP also follows: a certificate supplies a base graph, its subdivision isomorphism and a cover meeting the threshold. If the graph is given together with its base decomposition, the cover alone suffices. On the larger class of arbitrary graphs of girth at least 21 the reduction establishes NP-hardness. Starting from Vertex Cover on graphs of maximum degree three preserves that bound, since every inserted vertex has degree two. For any specified larger constant girth use a longer fixed odd path. [Garey, Johnson and Stockmeyer, *Some simplified NP-complete graph problems*](https://doi.org/10.1016/0304-3975(76)90059-1)

This decision problem receives a graph description. A truth table for its edge function has exponentially many entries. The reduction addresses this explicit graph representation and makes no conclusion about the usual truth-table MCSP or the equality of P and NP.

### Girth growing with the input

For each fixed 0<α<1, exact minimization remains NP-hard on subcubic graphs with N vertices and girth at least N^α. Start with subcubic Vertex Cover, discard isolated vertices, and choose an integer q≥1 with q/(q+1)≥α. Replace every original edge by a path of odd length L=(2M)^q+7, using h=(L−1)/2. The output size is polynomial for this fixed α. Testing the gate threshold 3hM+M+k−1 tests whether the original vertex-cover number is at most k.

There are at most 2M original vertices after removing isolates. Thus N≤(L+1)M≤2LM≤L^(1+1/q), because L≥(2M)^q. Every cycle in the subdivision has length at least 3L, so the asserted girth bound follows; forests satisfy the cycle bound vacuously. Only original vertices can have degree three. Since N≥(L−1)M≥2^q M^(q+1), their number is O(N^(1/(q+1))). The family can therefore have both widely separated cycles and few branching vertices. The exponent q is fixed before the reduction and controls the polynomial growth in the output size.

## Paths of both parities

The identity C(H)=|E(H)|+τ(H)−1 also holds when every original edge is replaced by a path of *any* length at least seven, and there is at least one original edge. The parity may vary from edge to edge. This extension uses the project's separately checked even-length companion L-meta-576. Its conclusion for a path of length 2h+2 is a saving of 3h+3 with no remaining edge, or a saving of 3h with one pendant left at each endpoint. [Companion theorem, independently contributed upstream](https://github.com/brilliant-hq/pequalnp-proofs/pull/656)

Let O be the odd-length edges (length 2h_e+1) and P the even-length edges (length 2h_e+2). In both cases h_e≥3. Add one disjoint anchor edge to H by an AND and a final OR, costing two gates. Keep it throughout the reductions. It guarantees that every outside function is nonconstant, even if all earlier replacements left no pendants. Endpoint singletons and the empty assignment still give all required false witnesses.

For each odd path the reduction chooses one pendant and saves 3h_e. For each even path it chooses two pendants or none. Let D⊆P be the even original edges for which it chose none. The total saving is at least 3Σh_e+3|D|. The terminal graph has the anchor, plus |O|+2(|P|−|D|) distinct pendant tips. Write T for their distinct original owners. The terminal circuit needs at least

    2 + |O| + 2(|P|−|D|) + |T| − 1

gates, since the anchor adds two essential variables. This also gives one gate when there are no pendants. Canceling the original two anchor gates yields

    C(H) ≥ 3Σh_e + |O| + 2|P| + |T| + |D| − 1.

T meets every edge of O. Every even original edge with at least one endpoint outside T belongs to D. To evaluate the resulting bound, fix the original cover choices C. On each odd path the necessary internal count is h_e plus one exactly when neither endpoint is in C. On each even path it is h_e plus one exactly when at least one endpoint is outside C. Alternating vertices attain these minima in each of the four boundary cases. Adding one endpoint per missed odd edge cannot increase this combined cover cost. Therefore

    τ(H) = Σh_e + min_{C meeting O} ( |C| + number of e∈P with e not contained in C ).

Since |E(H)|=2Σh_e+|O|+2|P|, the lower bound is at least |E(H)|+τ(H)−1. The star formula gives equality. This proof uses the actual unrestricted circuit reductions for both parities. The new Lean modules in this package target the odd-path theorem used in the NP-hardness reduction.

The mixed-length decision problem is also NP-complete when the decomposition is part of the input. For membership in NP, certify a cover of H of size at most k−|E(H)|+1 for the gate threshold k. Its validity is checked by scanning the edges. The same verification works when membership in the subdivision family is promised. For the ordinary language requiring both a valid decomposition and a circuit of size at most k, an omitted decomposition can itself be supplied as part of the certificate and checked in polynomial time. The fixed seven-edge case gives hardness even under the degree-three and girth-21 restrictions.

## Cycles

For the cycle on n≥14 vertices, take two parallel original edges and give their replacement paths lengths 7 and n−7. The mixed-length theorem gives the exact unrestricted circuit size n+⌈n/2⌉−1. The same formula covers 5≤n≤13 by the exhaustive finite certificate on the research fork. Its broader girth-five census covers lengths 5 and 6, and the subcubic girth-seven census covers lengths 7 through 13. Together these give the exact size for every cycle of length at least five. [Finite certificates and reproduction commands](https://github.com/stanleytheli/pequalnp-proofs/tree/f7ddcda96791cd13e786a01d4ac7421e2889ff52/research/demorgan-graph-bounds)
