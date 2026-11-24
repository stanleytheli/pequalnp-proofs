# Large fixed-coordinate degeneration orders on subcubic graphs

For a graph \(H\), write \(Q_H\) for the probability under independent vertex choices that no selected edge appears. Each physical vertex \(v\) has its own independent cube coordinate \(x_v\). Consider absence substitutions \(q_v=b_v t^{\ell_v}x_v\) with positive \(b_v\), nonnegative integer \(\ell_v\), and a common output scaling \(B t^{-s}\). There are subcubic graphs on \(N\) vertices having a limit polynomial that forces
\[
 \max_v \ell_v\ \geq\ 2^{\Omega(N)}
\]
for every such realization of that polynomial on the same graph and labeled coordinates. The graphs have pathwidth at most 113, girth at least 21 and a known optimal read-two monotone formula for their Boolean edge predicate. The girth can instead grow at least as \(N^\alpha\), any fixed \(0<\alpha<1\), while the necessary orders remain \(2^{\Omega(N^{1-\alpha})}\). These are bounds on approximation orders when retaining the labeled coordinate factors. Changing the graph or substituting unrelated multivariate affine forms is a different model.

## A rigid source graph

Begin with a five-cycle, every weight one, and mark one vertex. A real vector \(z\) has equal sum on all five maximum independent sets only when its coordinates are equal, by comparing the five nonadjacent pairs. The marked vertex has weight one, degree two, and belongs to some but not all optima.

At each round replace the marked vertex by a fresh five-cycle joined completely to its two former neighbors. Double all surviving old weights; the new weights are one. Each old optimum avoiding the marked vertex survives, and an optimum using it substitutes any nonadjacent pair in the new cycle. These are exactly the new optima: a set entering the module excludes the former neighbors and the maximum module contribution is two. Equality of candidate scores on all these alternatives first forces the five new candidate coordinates to a common value \(u\). Contract the module to one candidate weight \(2u\). The old rigidity then forces the candidate vector to be proportional to the newly prescribed weights. This uses the classical stable-set substitution operation. [Chvátal, *On certain polytopes associated with graphs*](https://doi.org/10.1016/0095-8956(75)90041-6)

Immediately split a vertex \(v\) of the fresh cycle into a three-vertex path \(l-z-r\), all three of weight one. Attach its two exterior neighbors only to \(l\), and attach its two cycle neighbors only to \(r\). Mark \(z\) for the next round. This split raises the maximum weight by exactly one. An old optimum using \(v\) chooses both ends; one omitting \(v\) can choose the middle. Conversely, contract a set containing both ends to \(v\), and a set using at most one of the three to a set omitting \(v\). This loses at most one unit.

The split preserves rigidity. Take a maximum set using the fresh module with a nonadjacent pair avoiding \(v\). The exterior neighbors are absent, so its canonical choice of \(z\) can be exchanged for \(l\). Take instead an optimum avoiding the entire module; one exists because the previous marked vertex could be omitted. Now the inner cycle neighbors are absent, so \(r\) can replace \(z\). Equalities on these alternatives force the three candidate weights to be identical. In general the score difference between the two canonical choices is \(z_l+z_r-z_{\rm middle}\). Here this equals their common candidate value. Contracting the split to this single weight therefore yields a vector constant on all old optima; the known rigidity proves proportionality on the new graph. The new marked middle is chosen and omitted by some optima since the fresh vertex \(v\) could be omitted and chosen, respectively. Both its neighbors are precisely the fresh path ends.

Let \(A_r,k\) be the result after \(r\) rounds. A surviving original vertex doubles at every round, while the new marking always has weight one. Each substitution removes two old incidences, adds ten cross edges and five cycle edges; the three-vertex split adds two more. Each round adds six vertices in total. The two former marked neighbors gain four incident edges in their one round at this interface; new marked neighbors are fresh and each initially has degree three. Thus
\[
 |V(A_r)|=5+6r,\qquad E_r=|E(A_r)|=5+15r,\qquad
 2\le\deg_{A_r}(v)\le7,\qquad \max k=2^r .
\]
For every real candidate vector constant on the maximum-weight independent sets, the above induction gives \(z=\lambda k\).

## Maximal encodings on a subcubic odd subdivision

Replace a degree-\(d\) source vertex \(v\) by a cycle with \(d\) alternating ports and \(d\) guards. Each source edge connects its two dedicated ports on the corresponding cycles. A source independent set \(S\) selects every port in the cycles belonging to \(S\) and every guard in the other cycles. Denote this root configuration by \(R(S)\). It is independent and inclusion-maximal: each unselected root has a selected neighbor in its own cycle. There are \(4E_r\) roots and \(5E_r\) root edges.

Give each root reward \(H>\sum_v k_v\), with an additional \(k_v\) reward at one port of cycle \(v\). A full-size independent choice in a \(2d\)-cycle is one of its two alternating classes. A nonfull cycle loses at least \(H\), more than the total possible bonuses. The maximizing root sets are therefore exactly \(R(S)\) for maximum-weight independent \(S\) in \(A_r\).

Orient root edges arbitrarily and replace each by a path of \(2h+1\) edges, \(h\ge3\). Give odd private positions reward \(C+1\) and even positions \(C\), with \(C\) so large that \(J=C+1-h\) exceeds every old root reward. Add \(h\) to the tail root's reward per oriented edge. For selected endpoint bits \(x,y\), the maximum private contributions for \(00,10,01,11\) respectively are
\[
 h(C+1),\qquad hC,\qquad h(C+1),\qquad(h-1)(C+1).
\]
The conditional maximizers are unique. In state \(00\) or \(01\) select all odd private positions; in state \(10\) select all even private positions. In state \(11\) select all odd private positions except the first. Cardinality dominates all unit bonuses and the listed choices attain all possible bonuses at that cardinality, except when the odd-order eligible segment forces the parity. The table equals \(h(C+1)-hx-Jxy\). Consequently the root compensation restores the old objective and penalizes every conflicting root edge by \(J\). Deleting one endpoint of each conflict improves the score if any conflict exists.

Write \(F(S)\) for \(R(S)\) together with its canonical private choices. Every \(F(S)\) is inclusion-maximal in the physical graph, regardless of the weight of \(S\). An unselected root has a selected root neighbor in its original switch cycle. Along their path the boundary state is \(01\) or \(10\), and the chosen private pattern always puts a selected vertex immediately next to the unselected endpoint. An unselected private vertex must have a selected neighbor since it is part of a positive-reward conditional optimum. The global physical maximizing sets are exactly the \(F(S)\) for maximizing source sets \(S\).

## The fixed-coordinate lower bound

Use the constructed strictly positive integer rewards as exponents in \(q_v=t^{w_v}x_v\) and scale by the least weighted cover cost. In the unscaled graph probability as a polynomial in its independent absence variables, each inclusion-minimal vertex cover \(T\) has coefficient one on its squarefree monomial \(q_T\): in the expansion as a union of minimal cover-absence events, only this cover contributes that monomial. Equivalently the minimum-weight terms in the chosen path come from exact absent sets of least cost, with unit leading coefficient. The resulting polynomial is exactly the sum of \(x_{V(H)\setminus F(S)}\) over optimal source \(S\).

For alternative fixed-coordinate exponents \(\ell\), the *selected reward* of the canonical configuration for any source independent set satisfies
\[
 \sum_{u\in F(S)}\ell_u=K+\sum_{v\in S}\theta_v,\qquad \theta_v\in\mathbb Z .
\]
Each root is selected according to either the membership bit of its source vertex or its complement. On a root edge only the endpoint choices \(00,01,10\) occur. The score of its chosen private pattern is thus affine in the two endpoint bits: use its value at \(00\) and its two corresponding first differences. Summing over edges and roots gives the formula even when \(S\) is empty. Comparing \(S=\varnothing\) with \(S=\{v\}\) shows
\[
 |\theta_v|\le (6h+2)\deg_{A_r}(v)\max_u \ell_u.
\]
These two encodings differ at most on the \(2d\) roots of this switch and the \(2h\) private positions on each of its \(2d+d\) incident or internal root edges.

In the target polynomial, every optimal source set has its distinct complementary minimal-cover monomial. Its coefficient under any alternative monomial substitution is a nonzero constant multiple of precisely its own parameter power; different labeled coordinates do not mix. Consequently all those covers have the same \(\ell\)-cost, hence all associated selected sets have equal reward. Rigidity forces \(\theta=\lambda k\). The empty source set is nonoptimal, while the complement of its encoded physical independent set is still an inclusion-minimal cover. Its squarefree monomial coefficient before scaling is one, and it must disappear in the target. Its cost is strictly greater than the common optimum cost. Equivalently any optimal encoded set has strictly greater selected reward than \(F(\varnothing)\). Therefore \(\lambda>0\). Because a source vertex has weight one, integral \(\theta\) forces \(\lambda\) to be a positive integer. A surviving original heavy vertex now gives
\[
 \max_u\ell_u\ \geq\frac{2^r}{7(6h+2)} .
\]
The same reasoning applies to univariate analytic coordinate multipliers with nonzero positive leading coefficient and integer vanishing order. The order bound uses no assumption on the magnitudes of the positive multipliers.

## Physical parameters

The final graph has \(N=(10h+4)E_r\) vertices and \(5(2h+1)E_r\) edges. Its girth is at least \(3(2h+1)\). The ordinary switch graph has minimum cover size \(2E_r\): either alternating choice covers all internal switch edges, and selecting all ports also covers every external edge. Any switch cover needs at least half of its cycle's vertices. After odd subdivision the minimum cover size is \(5hE_r+2E_r\). For fixed original cover choices, each edge contributes \(h\) private vertices except an edge with neither endpoint covered, which contributes \(h+1\). Completing uncovered old edges gives the lower bound.

The Boolean physical edge predicate has unrestricted circuit size exactly \((15h+7)E_r-1\). An optimal read-two monotone formula is obtained by using all old ports as centers and orienting the source path from a port end. Assign its first physical edge to that port and alternate the private centers. If its other endpoint is also a port, assign the final edge to that old port. Every old port occurs once and every other vertex has degree at most two. The formula uses the edge count plus the cover size minus one. This is the unrestricted physical optimum by the long-subdivision theorem. [Circuit-size theorem and reproduction package](https://github.com/stanleytheli/pequalnp-proofs/tree/a31fcb5bd01e0bd1ba8e58c7c7db40195392c5fa/research/long-subdivision-circuits)

The source graph has a path decomposition with bags of size at most eight. For positive \(r\), begin with the four old vertices left when the first mark is removed. Each round's bag contains its two previous interface vertices, the four surviving vertices of its fresh cycle, and both endpoints of the fresh stretch. Consecutive bags share just the two interface endpoints. The intermediate marked middle is removed by the next substitution; the final middle uses a last three-vertex bag with its endpoints. All edges belong to a bag, and each vertex occurs on an interval. At \(r=0\) a single five-vertex bag suffices. Expand each source bag by the entire switch cycle for every vertex in the bag. Each such cycle has at most 14 vertices, so at most 112 vertices are needed at once. For each edge to be subdivided choose a bag containing its endpoints, duplicate that bag as needed and introduce the private path in consecutive pairs. This adds at most two vertices to a bag. The final width is at most 113 independently of the subdivision length.

With fixed \(h\) the displayed order bound is \(2^{\Omega(N)}\). For fixed \(0<\alpha<1\), choose \(h\) to be a sufficiently large constant multiple of \(r^{\alpha/(1-\alpha)}\), rounded up. Then the girth is at least \(N^\alpha\) and the order bound remains \(2^{\Omega(N^{1-\alpha})}\).

## A facet of the stable-set polytope

The source inequality \(k\cdot z\leq\alpha(A_r,k)\) defines a facet of the convex hull of stable-set incidence vectors. That polytope is full-dimensional because it contains the zero vector and all unit vectors. The vectors having equal scalar products on the optimum vertices form precisely the line spanned by \(k\), so the optimal face has dimension \(|V(A_r)|-1\). The normal is primitive since a coordinate is one.

The final subcubic graph \(H\) also has a stable-set facet with an exponentially large primitive coefficient. Consider the physical face whose vertices are precisely the \(F(S)\) for optimum source sets. Any integer vector \(a\) exposing that face, even a signed vector, satisfies
\[
 \|a\|_\infty\geq 2^r/[7(6h+2)].
\]
Indeed, its values on all the encodings are affine functions of the source bits by the conditional-pattern calculation. They are equal on the optimal source sets and strictly smaller on the empty encoding. Rigidity again forces a positive integral multiple of \(k\). The sensitivity argument uses absolute values throughout, so it also applies to signed \(a\).

Write the physical stable-set polytope using primitive integral facet inequalities, oriented as upper bounds. Take a maximal linearly independent subset of the normals of facets containing the chosen face. There are at most \(N\) such normals. Equality on this subset forces equality on every facet containing the face: compare the values at one point of that face and use the linear span. The sum of the chosen normals therefore exposes exactly the desired face. If \(D\) is the largest absolute coordinate of a primitive facet normal, the sum has norm at most \(ND\). Hence
\[
 D\ \geq\ 2^r/[7N(6h+2)] .
\]
This gives \(2^{\Omega(N)}\) for constant \(h\), and \(2^{\Omega(N^{1-\alpha})}\) at girth at least \(N^\alpha\). These large coefficients coexist with a linear-size extended formulation. Process the bounded-width path decomposition one vertex introduction or removal at a time, keeping the chosen independent subset of the current bag as a state. A unit source-to-sink flow on the resulting layered graph is a convex combination of paths. Project the aggregate flow selecting each vertex at its introduction. The projection is exactly the stable-set polytope, and the fixed width bounds the number of states and transitions per stage by a constant.

For every graph of fixed pathwidth, the exponential rate is also an upper bound. In the same layered representation, let \(a\) be a primitive facet normal. Each arc introducing a selected vertex \(i\) gets weight \(a_i\); other arcs get zero. Let \(J\) consist of arcs on paths maximizing total weight. For a variable \(p_u\) at each layered state and an unknown normal \(a'\), impose on arcs \(u\to v\) of \(J\) the equations \(p_v-p_u=a'_i\) when \(i\) is selected at introduction, and \(p_v=p_u\) otherwise. The given \(a\) is a solution with potentials equal to longest-path prefix scores. Every optimal path has an optimal prefix at each state, because another prefix could be substituted before the same suffix. Conversely any solution gives equal scores on all optimal independent sets by telescoping. Since these sets span a facet, every projected solution \(a'\) is a scalar multiple of \(a\).

For a rank-\(r'\) integer matrix with these equations, a rational nullspace basis can be chosen integral with every coordinate an \(r'\)-rowed minor up to sign. Choose an invertible full-rank minor, set each free variable in turn to its determinant with the others zero, and use Cramer's rule for the pivot variables. At least one such basis vector has nonzero projection onto the normal coordinates. Every row has Euclidean norm at most \(\sqrt3\), giving a bound \(3^{r'/2}\) on its minors. The primitive facet coefficients divide out a common integral factor from that nonzero projection. The rank is at most the number of states plus \(N\), which is \(O(2^{k+1} N)\) for pathwidth \(k\): each vertex enters and leaves exactly once. Thus each primitive coefficient of every graph of fixed pathwidth is \(2^{O_k(N)}\). Together with the construction, exponential growth in \(N\) is sharp already for a fixed width, maximum degree three, and girth at least 21.

The same upper bound holds for fixed treewidth. Use an empty-rooted nice tree decomposition with empty leaves and \(O_k(N)\) bags. Charge a selected vertex at its unique topmost forget operation. At a join, two child subproblems agree on the bag, and no weights of those bag vertices have yet been charged. Replace the unary arc equations at a join by \(p_{\rm parent}=p_{\rm left}+p_{\rm right}\), with \(p_{\rm leaf}=0\). Keep the local choices occurring in at least one optimal global assignment. The true optimum conditional subproblem scores satisfy their equations because any subassignment can be replaced by a better one with the same bag state. Conversely summing the equations over an optimal derivation telescopes to its total score. The same rank and row-norm estimates apply. The construction and these estimates concern coefficients of facets in the original vertex coordinates. Compact extended formulations for bounded-treewidth constraint satisfaction are already known. [Kolman and Koutecký, 2015](https://arxiv.org/abs/1502.05361)

Earlier examples include arbitrarily large primitive coefficients for graphs with no four-wheel minor. The simultaneous pathwidth, degree, girth, exponential-rate, and fixed-coordinate statements here follow from the explicit family and its exposing face. [Barahona and Mahjoub, Section 7](https://www.lamsade.dauphine.fr/~mahjoub/Papers/BM94c.pdf)

## Reproduction

Run `python3 verify_exponents.py` for the exact source-face rank tests, explicit path-decomposition checks, physical maximality tests, and arbitrary-score identity controls using only the Python standard library. Two controls also contract the leading Bernoulli factors directly from every raw physical vertex and edge, recovering the expected order and number of optimum source sets. The source-face rank is evaluated modulo 1009: a full-rank minor there proves the corresponding rational rank lower bound. These numerical controls supplement the arguments above.
