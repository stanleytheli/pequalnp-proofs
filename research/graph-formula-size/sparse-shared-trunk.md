# Repairing the edge inputs lost when a circuit is cut

Let G = (V,E) be a finite simple graph with at least one edge. Write m = |E| and let τ(G) denote the minimum vertex-cover size. Its edge predicate is true on a set of vertices exactly when that set contains an edge. Size counts binary AND and OR gates, with unrestricted fanout and free raw inputs and Boolean constants. A formula is a tree of such gates.

## The cut and repair theorem

Consider a circuit for the edge predicate. Trace it backward from the output, stopping at selected gate outputs. Suppose that the part above these stops is a formula tree on raw variables, constants, and references to the stopped gate outputs. In particular, one can always stop at every shared gate as it is encountered. Let

- t be the number of binary gates in this tree,
- T be the number of occurrences of stopped signals as tree leaves, including repetitions,
- k be the number of distinct stopped signals occurring in the tree,
- q be the number of physical circuit gates outside the tree, including the k stopped gates.

The circuit therefore has t+q gates, with T ≥ k and q ≥ k. The dependencies below the boundary can be arbitrary. In particular, a stopped signal can depend on another stopped signal.

Set all the stopped leaves to false to form a residual formula R. Write D⊆ E for the edges whose two-vertex inputs R rejects, and d=|D|. The original circuit admits a formula with at most

    t − T + d + τ(D)

gates, where τ(D) uses the graph with edge set D. Consequently it admits a formula no larger than its gate count whenever d + τ(D) ≤ q + T.

Indeed, replacing signals by false can only decrease the output. Therefore R implies the graph predicate on every input. If R is nonconstant, propagate constants in its tree. Each of its remaining leaves is one of the original tree's t+1-T nonboundary leaves, so it has at most t-T gates. For d>0, use a minimum cover of D to assign every missing edge to one endpoint. At each used endpoint form its conjunction with the disjunction of its assigned neighbors, and disjoin the stars. This formula for D has at most d + τ(D) − 1 gates. Disjoining it with R adds at most d + τ(D) gates. For d=0 use R alone. The repaired function implies G and accepts every edge input, hence equals the full graph predicate by monotonicity. If R is constant, it is false because the original predicate rejects the empty input. Then D = E. The star formula alone suffices, since T≤ t+1.

For a stopped signal s, let M_s be the set of genuine two-vertex edge inputs on which s is true in the original circuit. If all stopped signals are false on an edge, its tree evaluation is unchanged by the cut. Thus D⊆ ⋃ₛ M_s. The union provides a usable sufficient condition |⋃ₛ M_s| + τ(⋃ₛ M_s) ≤ q + T. Overlapping edge footprints count once.

## Consequences

1. If every stopped signal is true on at most one genuine edge input, then d≤ k and τ(D) ≤ d, so d + τ(D) ≤ 2k ≤ q + T. This holds in particular whenever every shared gate computes a conjunction of at least two distinct raw variables. Single-variable conjunctions can be bypassed. Gates above the shared signals can be nested arbitrarily.
2. Suppose each stopped output is realized by a gate-disjoint private star formula (x_c ∧ (⋁_{u∈A} x_u)), with c∉ A. The star has at least as many gates as the number of genuine edges in its two-input footprint. All footprints together are covered by their k centers, so d≤ q, τ(D) ≤ k ≤ T, and repair has no size overhead. Shared uses above these formulas can have arbitrary nesting.
3. When G has girth at least five, its exact monotone formula size is m + τ(G) − 1. Under any of the no-overhead conditions above, the same lower bound applies to the original circuit. For the projective-plane graph of order three this gives 64 gates. The theorem itself requires no girth, degree, or bipartiteness assumption.

## An independent bound when all sharing implies the output

For any nonconstant monotone target F, suppose that every shared noninput gate computes a function bounded above by F on all inputs. A circuit of n gates has an equivalent formula of at most n+k-T gates, where k is the number of shared gates and T is the sum of their numbers of outgoing operand slots. Only live gates are counted. Each shared gate has at least two such slots, so in particular the bound is at most n-k.

To see this, cut every outgoing slot of every shared gate. The physical gates then partition into k+1 formula trees rooted at the shared gates and at the original output. Their original leaf counts sum to n+k+1, including the T cut slots. Replace all such slots by false. Every residual root implies F, by monotonicity and the hypothesis on shared gates. Conversely, if F(x) = 1, take the first true shared gate in a topological order. Its residual tree agrees with its original evaluation because every earlier shared signal is false. If there is no true shared gate, the original output tree agrees with its residual. The disjunction of the residual trees therefore computes F. Discard false trees and propagate constants in the others. None can be identically true because F is nonconstant. The result uses at most n+k+1-T leaves and hence at most n+k-T binary gates.
