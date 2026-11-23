# An exponential obstruction to probability-preserving affine Hamiltonian projections

Let \(Q_H(p)\) be the probability that independent vertex choices with parameters \(p_v\) form an independent set of a finite graph \(H\). Let \(\mathrm{HC}_m(x)\) be the directed Hamiltonian-cycle polynomial, with \(m\ge2\). Suppose every \(p_v(x)\) is an arbitrary real affine function of the \(m^2\) adjacency entries and takes values in \([0,1]\) throughout the Boolean cube. Already equality on the Boolean inputs in
\[
 \mathrm{HC}_m(x)=c\,Q_H(p(x)),\quad c>0,
\]
requires \(|E(H)|\ge2^m-2\). Moreover, if each physical parameter uses at most \(d\) adjacency entries, then \(2d\ge\lfloor m^2/4\rfloor\). The one-entry specialization is impossible for \(m\ge4\) even with an unlimited graph. The positive scalar specialization to the complementary event \(1-Q_H\) is impossible for \(m\ge3\), even with unrestricted affine parameter supports.

## Positive probability and Boolean certificates

A draw can be independent with positive probability precisely when the set \(T=\{v:p_v=1\}\) is independent. If \(T\) is independent, the draw choosing exactly \(T\) has positive mass. If \(T\) contains an edge, that edge is present almost surely.

An affine form \(c+\sum_i w_i x_i\), bounded above by one on the cube, attains one either nowhere, everywhere or on a face. In the nonconstant case the face fixes each nonzero coefficient's bit to its maximizing value. Thus both ends of an edge are forced jointly on an empty set or on a subcube described by one conjunction of literals. Excluding it takes one clause. Accordingly the Boolean support \(Q_H(p(x))>0\) has a CNF with at most \(|E(H)|\) clauses and width at most \(2d\) in the bounded-support case.

For a direct counting argument, affine modularity gives \(p(x)+p(y)=p(x\lor y)+p(x\land y)\) at Boolean inputs. If both left terms equal one, both right terms equal one. Consequently a physical edge forced at two inputs is forced at their union. This is an elementary edge-count lower bound for any pairwise-join fooling set of rejected inputs.

## Exact characterization of the possible supports

Conversely, every CNF of width at most \(2d\) and with \(t\) clauses is the positive support of a no-edge probability on a matching with \(t\) edges, using at most \(d\) input coordinates per physical endpoint. For each clause divide its literals into two groups of size at most \(d\). Assign each endpoint the affine probability one minus the mean truth value of its group. Give an empty group probability one. Both endpoints are forced exactly when the clause is false. The empty clause yields a forced edge, and the empty CNF uses no edges. Thus the minimum edge count equals the minimum number of clauses among width-\(2d\) CNFs representing the target. Without a local support bound the minimum is simply the unrestricted CNF clause count.

Positive supports of the complementary event are exactly the functions with a 2-DNF. The construction for the reverse direction gives each term an isolated edge, uses its one or two literal values as endpoint probabilities, and supplies a deterministic one for an omitted literal.

## Directed Hamiltonian cuts

For each nonempty proper vertex subset \(S\), take the adjacency matrix \(x_S\) containing every arc except those from \(S\) to \(S^c\). It has no directed Hamiltonian cycle. Adding any missing arc \(u\to v\) restores a cycle: start at \(v\), visit the remainder of \(S^c\), visit all vertices of \(S\) ending at \(u\), then close with \(u\to v\). This works when either side has one vertex. Directed cut complements for different \(S\) are distinct maximal false inputs. Their union contains a Hamiltonian cycle because it adds at least one missing arc to either input. Loops may be retained throughout.

A clause false on two of these inputs would also be false on their union. Hence any CNF for directed Hamiltonicity requires at least the \(2^m-2\) distinct clauses. Further, every clause falsified by \(x_S\) must include *every* missing arc positively. Setting any one of those arcs to true makes the input Hamiltonian and must satisfy that clause. Applying this to a balanced \(S\) gives the width bound. Positivity of \(\mathrm{HC}_m\) at Boolean inputs over the reals is exactly directed Hamiltonicity, since it counts cycles there.

For the complementary event, positive probability of an edge holds exactly when for some edge both endpoint probabilities are positive. Each affine form is nonnegative. Its zero set is a minimizing face, so its positivity has an OR of literal witnesses (or is a constant). An edge gives a certificate of at most two true literals. A Hamiltonian input can have no such certificate when \(m\ge3\): retain any positively required entries, at most two, and set all other entries to zero. This preserves the certificate and leaves fewer than \(m\) arcs.

## Finite-error version

Any pointwise multiplicative approximation with relative error below one preserves zeros and positive values. The full support lower bounds therefore apply regardless of its positive normalization.

Let \(N\) count the nonisolated vertices. For \(0<\delta\le1/2\), the inequality \(Q_H(p(x))<\delta^N\) forces an edge whose two endpoint probabilities exceed \(1-\delta\). Otherwise the high-probability vertices are independent and the event that every remaining vertex is absent has probability at least \(\delta^N\). If one edge supplies this witness on two cut inputs, affine modularity and the bound of one at their intersection imply that both endpoint probabilities exceed \(1-2\delta\) at their union. The no-edge probability there is at most one minus the probability that this edge is present, hence is less than \(4\delta\).

Suppose a positive multiple \(cQ_H(p(x))\) approximates every Boolean Hamiltonian-cycle count with absolute error \(\varepsilon<1/2\). The existence of a positive target value forces \(c>1/2\). Taking \(\delta=1/(16c)\), each cut has a witness if \(\varepsilon<c(16c)^{-N}\). A Hamiltonian union has \(cQ_H>1/2\), while reuse of the same edge would give \(cQ_H<1/4\). This gives the same exponential size obstruction at that explicit finite tolerance.

## Exact scope

The argument applies to arbitrary real affine forms, with signs allowed in their coefficients as long as their evaluated probabilities remain in \([0,1]\). Cube preservation on Boolean inputs implies preservation on the full real cube. It also applies in the Euclidean closure with bounded positive normalizing scalars: take a convergent subsequence of the finitely many affine coefficients and bounded scales. Every coefficient is in \([-1,1]\), since it is a difference of two valid cube probabilities. A nonzero target keeps the limiting scalar positive. For fixed edge-count bound, isolated vertices may be discarded and there are only finitely many unsigned graph types.

The arithmetic transfer uses field-valued normalizations outside the real probability interval. The fair counting reductions use modular postprocessing, which is why they can have polynomial-sized, fully nonnegative queries. Neither fits the direct identity above. The support argument gives no result for unrestricted signed formal border projections or for an arbitrary additive offset on the output.

Earlier work gives exponential monotone affine projection lower bounds from the permanent to the Hamiltonian-cycle polynomial using Newton polytopes and extension complexity. The argument here concerns the support of an independent-Bernoulli graph probability under cube-preserving affine forms. [Grochow, *Theory of Computing* (2017)](https://www.theoryofcomputing.org/articles/v013a018/)
