# Positive limits of bounded-width witness events

Let a finite hypergraph have edges of size at most \(d\). Draw each vertex independently with a prescribed probability and accept when the selected vertices contain an edge. The vertex probabilities may be arbitrary affine functions preserving the real input cube. A positive scalar multiplies the event probability. At each input length permit any pointwise limit of such functions, allowing new hypergraphs, probabilities and unbounded positive scalars at every step.

**The Boolean supports of these limits are exactly the functions expressible by a DNF with at most \(d\) literals per term.** The hypergraphs may grow without bound during approximation. For ordinary graphs the bound is two. Directed Hamiltonicity on \(m\ge3\) vertices therefore has no such representation, even with unbounded graphs and singular positive normalizations.

## A simultaneous probabilistic coupling

Each affine probability \(p_v\) has an expression as a nonnegative constant plus at most one nonnegative multiple of a signed literal per input coordinate. Its value at the maximizing Boolean point is the sum of these coefficients and the constant, which is at most one. Independently for each vertex, sample a label. The constant-true label has mass equal to the constant, each literal has mass equal to its coefficient, and the leftover mass belongs to a never-active label. Activate the vertex on input \(x\) precisely when its sampled label is true at \(x\). This gives the required independent Bernoulli marginal distribution for every fixed input, using the same label space for all inputs.

For each possible conjunction \(C\) of at most \(d\) signed input literals, let \(A_C\) be the event that some hyperedge has labels giving exactly that conjunction, omitting constants and duplicate literals. Discard edges with a never-active label or contradictory literals. Put \(a_C=\Pr(A_C)\); these real numbers are independent of the input. For every \(x\), the edge-present event is the union of the \(A_C\) for which \(C(x)\) is true. If \(T(x)\) is the largest such \(a_C\), or zero if none exists, then
\[
 T(x)\le R(x)\le D T(x),\qquad D=(2n+1)^d.
\]
The count includes the empty conjunction using constant padding, and depends only on input length and width.

At a fixed length normalize a nonzero limit target so every positive value is at least one. Select one approximant with \(cR\) uniformly within \(1/(4D)\) of the target, which is possible on the finite cube. At every positive input \(cT>1/(2D)\); at every zero input \(cT<1/(2D)\). Therefore the disjunction of precisely the terms with \(c a_C>1/(2D)\) decides the support. An identically zero target uses the empty disjunction.

Conversely realize each DNF term with its own disjoint hyperedge, using its signed literals as vertex probabilities. On Boolean inputs the selections are deterministic and the edge-present event agrees with the given DNF. Width-one or constant terms may be padded by distinct probability-one vertices when ordinary graph edges must have two distinct endpoints. For directed Hamiltonicity, every consistent conjunction of at most two literals can be satisfied by a graph with at most two selected arcs, which has no Hamiltonian cycle for \(m\ge3\). Since some directed graphs do have such a cycle, a 2-DNF cannot represent Hamiltonicity.

The complementary event on the same physical graphs has a different support characterization. [Nonuniform verification by independent-set probability limits](positive-support-class.md)
