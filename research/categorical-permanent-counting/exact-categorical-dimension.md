# The exact dimension of complementary-face readouts

Let G be a finite bipartite multigraph with at least one perfect matching. Keep
distinct physical edge identifiers and discard any edge in no perfect matching.
Write P for its perfect-matching polytope in the physical incidence coordinates
and d=dim P. A binary readout colors some edges X, some Y, and leaves the rest
blank. It is complete if every perfect matching sees exactly one of X,Y, with
arbitrary repetition within that color. Denote its 0–1 X-indicator by f. This
description includes precisely the splits of the vertices of P into two
complementary exposed faces, allowing the constant cases: a face is given by
forbidding certain coordinates, and the complement of each side of the split
is a hit on its forbidden set. A live edge cannot belong to both forbidden
sets of a complementary pair.

Decompose G into its matching-covered connected components and use a tight-cut
factor tree on each, stopping at the usual large Hall-plus-two braces or small
factors with at most three rows. In every split, a boundary edge keeps its
individual parent identifier on both contracted factors. Let t be the number
of terminal factors with three rows whose underlying simple support graph is
the full K₃,₃.

**Theorem.** As functions on the original perfect matchings, the span over ℝ
of 1 and all complete binary indicators has dimension d+1+t. There is a
universal lift that augments the ordinary physical incidence vector with
exactly t scalar coordinates and realizes every complete readout affinely.
It has a description with at most |E(G)|+6t inequalities and linear equations.
No universal lift carrying the original coordinates can use fewer than t
additional affine dimensions. In particular, t is independent of the chosen
tight-cut factorization.

## Why terminal edge and matching states are available

At a split one global perfect matching is precisely a pair of child matchings
agreeing on their chosen crossing edge. Each child physical edge is live: it
is the retained copy of a live parent edge, and a parent matching using this
edge restricts to a child matching using its copy. In particular, for any
child matching with crossing edge e, the opposite child has a matching using
e. The two glue. Every matching of either child extends to a parent matching.
Induction proves extension to an original matching of the component; choose
any perfect matchings of the other components. This includes arbitrary
compatible choices of parallel copies in any one terminal matching. Labels
placed on a terminal physical edge can therefore be placed on its original
identifier. In a given terminal factor an identifier has only one local copy.

The same split provides probabilistic gluing. Child laws with the same
probability for each crossing edge can be coupled by first choosing that
edge, then drawing the two child matchings from the corresponding conditional
laws. Omit zero-probability edges. This preserves the entire law on each
child. Applied up a tree, any specified terminal laws with matching
boundary marginals glue to a global law. More explicitly, after coupling
the subtree beneath a child, that child still has the original probability
for each of its physical edges: every such edge has a retained descendant
copy, and their incidence is preserved on gluing. In particular the needed
marginals agree at the next split. Components can be sampled independently.

## Local coordinates and parallel copies

For any readout, fix one reference copy in each simple terminal cell. If a
cell offers both colors among its copies, then every other cell that can occur
beside it in a matching has only blank copies. This follows by choosing the
opposite color in the flexible cell. The flexible cell has no blank copy: a
matching using that copy would otherwise read neither color. On a matching
using this cell the difference between its physical indicator and the
reference indicator is precisely a fixed coefficient of its chosen copy.
At most one flexible cell can be used. In a matching with no flexible cell,
switch actual copies to their references one slot at a time. If the
global category changed in one step, that slot would provide both colors,
as the common context cannot provide different colors before and after.
The category therefore stays fixed. Thus an edge-linear correction to the
simple-cell reference readout suffices for parallel copies. This works for
every readout simultaneously in the same incidence coordinates.

On a terminal factor of order at least four the brace argument reads every
category affinely in its physical incidences. For a simple order-three
factor consider the six permutations of the full three-by-three matrix.
Each of its nine cells belongs to one even and one odd permutation. Every
even–odd pair shares exactly one cell, because their relative permutation is
a transposition. A linear dependence on the six incidence columns therefore
requires a_u+a_v=0 on every edge of the K₃,₃ between the parity classes. Its
entire kernel is the one-dimensional space of alternating parity sums.
Every proper subset of the six columns is linearly independent. Hence on a
non-full order-three factor every vertex function is already linear on
cell incidences, and the same holds trivially at orders one and two.
On the full factor, adding just the indicator z of a particular fixed
cell permutation supplies the missing dimension: z does not satisfy the
alternating relation. One may instead use the parity indicator.

For a tight cut at a fixed crossing e, a pure function on the rectangle of
left and right choices satisfies
f(u,v)=f(u,vₑ)+f(uₑ,v)−f(uₑ,vₑ) for reference choices uₑ,vₑ in that state.
Indeed the total multiset of source edges is the same on the two diagonals,
and a pair of pure outputs has the same colors with the same counts when the
underlying union of labels agrees. The reference child readouts are pure:
retain each side's labels and add the fixed partner's offered color, if any,
to the corresponding boundary edge. Conflicting labels on one used edge
are impossible by purity. The correction depends only on the crossing ID.
The alternative dummy-marker construction in CategoricalCut.lean gives
the same affine recurrence. Components satisfy the analogous ordinary
Cartesian-product identity. Induction now expresses every pure indicator as
an affine function of original physical incidences and one z for each
exceptional terminal factor. This proves the dimension upper bound.

## The lift and its inequality count

Use x∈P(G), specified by nonnegative edge coordinates and unit row and column
sums. For each exceptional leaf add its six underlying permutation
probabilities λπ≥0 and equations identifying the cell marginals with the
sum of the retained physical x-coordinates in that cell. The equations also
imply total probability one. For each fixed feasible x the probability
vector has affine solution dimension at most one, by the parity relation;
it is parameterized by the single scalar z=λπ₀ used above. Therefore
five variables per leaf can be eliminated by linear substitution if desired.

This system is exactly the convex hull of augmented global matching vectors.
Any global matching or mixture satisfies its constraints. Conversely fix
x and the prescribed exceptional probabilities. Choose any distribution
on global matchings with marginals x and retain its local marginals as a
starting point. At each exceptional leaf replace its local law: select the
underlying permutation with probabilities λπ and independently draw, in
each selected cell, the physical edge e in proportion to xₑ. A zero-total
cell is used with probability zero. This realizes precisely the specified
λπ and every physical marginal xₑ. All other terminal laws stay as they
were. The gluing above provides a global law preserving these new laws,
so its expected augmented vector is the desired point. The original x
nonnegativities and the six nonnegativities for each exceptional leaf
account for all the inequalities.

## Sharpness of the additional dimensions

Every physical xₑ is itself a pure binary readout: mark e with X and all
other physical edges in its row with Y. Together with 1 these functions
span dimension d+1. For each exceptional leaf i label **all parallel copies**
of (0,0),(1,2) with X and of (0,2),(1,0) with Y, after labeling its rows
and columns 0,1,2. On its six simple permutations the X hit is two on the
three even permutations and one on the three odd permutations in total.
The readout lifts to a pure global indicator fᵢ by using original edge IDs.

Take the uniform law on all original perfect matchings. Every live physical
edge has positive marginal. Every underlying permutation of every exceptional
leaf has positive probability by the extension argument above. At one chosen
leaf i, add ε to each even permutation probability and subtract ε from each
odd permutation probability, choosing ε smaller than the six starting
probabilities. All cell marginals stay fixed. Draw parallel copies by the
same relative marginal rule as above and keep the original laws on all
other terminal factors. Glue. Compare this global distribution to the
original law. Every original physical incidence has the same expectation;
this includes edges copied at more than one cut. For j≠i, fⱼ has unchanged
expectation since its terminal law did not change, even when its labels
share original IDs with leaf i. The expectation of fᵢ increases by ε.
Consequently f₁,…,fₜ are linearly independent modulo the affine functions
of the physical incidences.

Any lift on which all these readouts are affine has dimension at least d+t:
choose one lift for each original matching with all its readout values; the
dimension of restrictions of affine functions is at most one plus the lift
dimension. The exhibited lift attains the bound. With no physical edges
and the empty matching as the only feasible point, the span is the constant
one-dimensional space and t=0.

The local linear expressions can be chosen over the integers. Number the even
and odd permutations e₀,e₁,e₂ and o₀,o₁,o₂. For prescribed integer vertex
values F, first subtract δ=ΣᵢF(eᵢ)−ΣⱼF(oⱼ) times the indicator of e₀.
The remaining even and odd totals agree. Choose integer weights on the
nine cells (eᵢ,oⱼ) realizing the even values as row sums and the odd values
as column sums: put each nonzero-index row's required total in its column
zero, put each nonzero-index column's required total in its row zero,
and use the remaining entry to balance row zero. Equality of totals
balances column zero as well. On a proper set of permutations, prescribe
the unused vertices arbitrarily and then change any one missing value to
balance the totals. No extra indicator is then needed.
