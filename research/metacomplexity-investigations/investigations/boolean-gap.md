# A constant gap above the essential-input floor for succinct Boolean MCSP

The input here is a monotone Boolean circuit. Its size is linear in the
length of the constructed instance, and all N named inputs are essential.
The task asks for the smallest equivalent single-output circuit over the
full basis of sixteen two-input Boolean functions, counting internal gates.
There is an absolute δ>0 for which distinguishing the following promises
is coNP-hard under deterministic polynomial-time many-one reductions:

* The minimum is N−1. The function is an OR of disjoint two-input ANDs.
* The minimum is at least (1+δ)(N−1). Every circuit also needs Ω(N)
  distinct input or gate signals feeding two or more operand slots.

The description can be a **read-two** monotone formula of logarithmic
depth and linear size. In the read-two version the easy function is a
known read-once formula built from disjoint matching and biclique components.
These claims concern succinctly presented
functions. Existing work already establishes hardness of approximate
minimization for succinct inputs. Our special promises are full input
relevance, a fixed read-once easy function, and a lower bound on physical
signal sharing in the hard case. We make no claim of priority.
[Prokopyev and Pardalos on succinct minimization](https://doi.org/10.1023/B:JOCO.0000031414.39556.3a)

## Shared signals give a cheap protocol on one common layout

Trim a binary Boolean circuit to its output cone, and represent each
primary variable by one physical source. Count two slots of the same
gate as two uses. Let b count signals with two or more uses. Cut each
outgoing use of these signals and replace it by a terminal carrying its
value. Keep the original producer, including a one-vertex producer
when a shared signal is a primary input. The result is a forest of trees
rooted at the shared producers and the final output. Each primary
variable belongs to exactly one component. Constant and cut terminals
carry no data variables.

Prune subtrees with no data leaves and suppress unary vertices for
purposes of the variable layout. Join the remaining component trees by
an arbitrary binary tree. For every edge cut of this single leaf layout,
the two parties holding opposite sides can compute the original circuit
with b+1 communicated bits or fewer, with one party receiving the answer.
Broadcast shared signal values in topological order. Each component
lies entirely on one side, except possibly one component split by a
rooted subtree. The latter needs at most one additional bit, namely
the value at the boundary of the subtree once its incoming shared
signals are known. Pruned constant subtrees depend only on earlier
broadcasts or public constants; unary chains can be evaluated locally.
The protocol is valid for arbitrary Boolean gates. Fixed-topology
private coins can be made public, since they are independent of the
data. When some primaries are fixed, they can simply be publicly known
while choosing the layout on essential unfixed data.

For a deterministic circuit with g gates and N essential inputs, its
number of binary operand slots is at most 2g. Every vertex except the
output has an outgoing use. The sum of excess outdegrees over the used
nonoutput vertices is at most 2g−(N+g−1)=g−N+1; additional constant
source vertices only decrease this bound. Thus g≥N−1+b. This convention
counts arbitrary fanout as free in the original gate cost.

## An explicit hard graph

Take the eight-regular Margulis–Gabber–Galil multigraph on m=t² vertices
for even t. Its four forward maps on pairs in Z_t² are
(a+2b,b), (a+2b+1,b), (a,b+2a), (a,b+2a+1), together with their inverses.
The upper nontrivial adjacency eigenvalue is at most 5√2. On a balanced
cut with sides between m/3 and 2m/3 this gives at least
(8−5√2)2m/9 crossing edges counted with multiplicity, by the Rayleigh
quotient of the centered set indicator. For the Boolean function discard
loops, merge parallel edges and add any publicly specified perfect matching.
The resulting graph G has degree at most nine.
[Gabber and Galil](https://doi.org/10.1016/0022-0000(81)90040-4) ·
[Machine-checked expander construction and spectral gap](https://devel.isa-afp.org/thys/Expander_Graphs/Expander_Graphs_MGG.html)

Every balanced cut contains a matching of at least
h=(8−5√2)m/729 crossing edges whose endpoints induce *only* those
edges in the full simple graph G. Greedily choose an original crossing
edge and disallow every remaining crossing slot touching an endpoint
or one of its neighbors in the augmented graph. The two endpoints'
closed neighborhoods together have at most 18 vertices, because the
chosen endpoints are adjacent and each has degree at most nine. This
removes at most 18·9=162 slots per choice. The denominator above follows.
All surviving matching endpoints can therefore carry independent
two-party input bits; set other variables to zero. Detecting a selected
graph edge now computes set intersection on those h coordinate pairs.
The complementary disjointness matrix is the h-fold tensor power of
the invertible two-by-two matrix with rows (1,1) and (1,0). Its rank
is 2^h, giving a deterministic communication lower bound h for the
complementary function (the receiving party can flip the answer).
The standard rectangle partition bound also holds with one party
receiving the answer: the 1-subset of each final transcript rectangle
is still a rectangle. Thus every such layout requires b≥h−1.
For fixed-topology bounded-error randomized circuits, the public-coin
communication lower bound for disjointness gives b=Ω(h).
[Razborov on distributional disjointness](https://people.cs.uchicago.edu/~razborov/files/dis.pdf)

## Switching between a matching and the expander

Replace a 3SAT instance by an equivalent bounded-occurrence width-at-most-three
CNF via occurrence copies and a cyclic implication chain for each original
variable. Each signed literal occurs in at most two clauses. Introduce
two positive inputs p_i,n_i per new variable. Let C(p) be the monotone
CNF obtained by replacing its literals by these inputs. Define

    Clash(p) = OR over i of (p_i AND n_i).
    Match(x) = the edge predicate of the data graph's fixed perfect matching.
    F(p,x)   = Clash(p) OR Match(x) OR (C(p) AND Edge_G(x)).

Take m an even square of order the source length, at least the number
of selector rails. The instance is produced in polynomial time. Each
rail appears in Clash and in at most two clauses. Each data variable
appears at most ten times. Balanced binary OR and AND trees give the
description bounds asserted above. We can assume at least one nonempty
clause. With all p zero the data subfunction is the perfect matching;
with x zero the selector subfunction is Clash. All N inputs are essential
in both cases.

If the source is unsatisfiable, every assignment satisfying C contains
a clash: otherwise extend its chosen literals to a satisfying assignment.
Then F is an OR of a perfect matching on all N variables, of exact size
N−1 by the support bound. If the source is satisfiable, pin p to the
consistent encoding of a solution. The data restriction is Edge_G
because G contains the matching. Choose a balanced edge of the circuit's
layout by weighting only the m data leaves. Such an edge exists in any
binary leaf tree: descend through children of weight greater than 2m/3
until the larger child has weight between m/3 and 2m/3. The protocol
above now forces b≥(8−5√2)m/729−1 in the full circuit. Hence its
size is at least N−2+(8−5√2)m/729. Since N≤2m, a fixed positive δ
works after constant-size padding. The explicit constants are conservative.

The randomized argument asserts a lower bound on the number of shared
signals for one fixed topology whose output is correct with probability
at least 2/3 on every input. Primary random strings or locally generated
coin bits are public to the simulation. This statement requires the
N data primaries to be represented once each. Random selection of a
different topology with an unrelated layout on each run is a different model.

## A read-two input in both cases

There is a second construction where each input appears at most twice
in the *supplied* formula. Let the base eight-regular multigraph have
M=t² vertices. Replace each base vertex by a connected star on eight
port vertices, labelled +1,…,+4,−1,…,−4. For generator j pair the +j
port of v with the −j port of its image. The external edges form a
perfect matching, including for generator fixed points since the two
ports have different signs. The m=8M-vertex simple graph is the union
of this matching and the disjoint internal stars; duplicates are harmless.
Its degree is at most eight. The edge predicate of either part has a
read-once formula. For a star take the center AND the OR of its leaves.

This graph still has a linear induced crossing matching on every
balanced data cut. Write η=8−5√2. If at least ηM/192 stars are split,
each such connected star provides a distinct crossing edge. Otherwise
the set of base vertices whose entire stars lie on the first side has
size between M/4 and 2M/3. Its base multigraph cut has at least ηM/12
edges. At most eight edges per split star can terminate there. At least
ηM/24 base edges therefore cross between two whole stars. These
correspond to distinct matching edges in the port graph. In either
case the simple cut contains at least ηm/1536 edges. Greedily removing
both closed neighborhoods costs at most 2·8² crossing edges per chosen
edge. Thus the gate lower bound above applies with h≥ηm/196608.

For a bounded-occurrence SAT instance, allocate exactly two positive
and two negative ports to each Boolean variable. At most two occurrences
per sign are needed. Give each literal occurrence a different port, and
let C be the monotone clause CNF on these ports, a read-once formula.
Let D be the OR, over variable groups, of the conjunction of the OR of
its positive ports and the OR of its negative ports. This conflict
predicate is read-once too. Unused occurrence ports remain essential
through D. Supply the formula

    D(p) OR ExternalMatching(x) OR (C(p) AND InternalStars(x)).

Each variable occurs at most twice. If the clauses are unsatisfiable,
C implies D, and the first two disjuncts give a single read-once formula
on all N variables. For a satisfying assignment, set all ports on its
chosen sign to one and all other ports to zero. Then D=0,C=1, and the
data restriction is the full port graph. With all data zero each selector
port remains essential in D; with all selector ports zero each data port
remains essential through its matching edge. Taking m at least the
number of selector ports gives N≤2m and hence a constant gap. Balancing
the n-ary operations gives depth O(log N) and at most 2N−1 binary
gates in the input formula. This instance is also a zero-versus-linear
gap for the least possible number of distinct shared signals.

The recognition of read-once functions from certain read-two
descriptions is already coNP-complete. The promise here additionally
separates their *unrestricted binary circuit sizes* by a factor and their
distinct signal-sharing counts by a linear amount.
[Kozachinskiy on read-once recognition](https://arxiv.org/abs/1802.03815)

## Two fixed read-once trees, with only a leaf permutation as input

The upper description can be made the OR of two read-once formulas,
**each containing every one of the N variables exactly once**. Only the
leaf permutation of the second tree depends on the source SAT instance.
The two unlabeled tree shapes and their gate labels are fixed per size.

First make all clauses have three literal occurrences (a repeated
literal is allowed). For each Boolean variable v with more positive
than negative occurrences, add one tautology (¬v OR ¬v OR v) per unit
of imbalance. Treat excess negative occurrences symmetrically. Now
split every occurrence into a separate copy and add the cyclic binary
implications for each original variable. There are equally many
positive and negative payload copies in each group. Pair them, adding
the clause (¬positiveCopy OR negativeCopy) for each pair; it is true
whenever the cycle enforces equality. Each copy now has exactly two
positive and two negative occurrences. With K copies there are K/3
ternary clauses and 3K/2 binary clauses. K is divisible by six.
Optional padding by opposite fresh-variable ternary tautologies
(u,u,¬u) and (¬u,¬u,u) makes K a common multiple of six at a given
source length without changing satisfiability.

Use the four ports per copy in the first tree D OR ExternalMatching
in their fixed order. The second tree C AND InternalStars has prescribed
clause shapes; its selector leaf labels are the permutation assigning
ports to literal occurrences. Its data leaf labels stay fixed. The
resulting formula has exactly 2N−1 binary gates. Distinguishing its
optimal unrestricted equivalent size N−1 from (1+δ)(N−1) is therefore
hard even when the varying description is just this permutation.

The structural argument has a graph-width formulation. Sim-width is
the minimum, over subcubic leaf layouts, of the largest whole-graph
induced matching crossing any layout edge. For a graph H with n
nonisolated vertices, the protocol proves b≥sim-width(H)−1, hence
g≥n−2+sim-width(H). The same inequality uses N in the additive term
for any function of N essential variables having the edge predicate
of H as a restriction. [Kang, Kwon, Strømme and Telle](https://doi.org/10.1016/j.tcs.2017.09.006)

The knowledge-compilation literature gives a related route for small
descriptions. Bounded-degree expander graph CNFs require exponential
DNNF size, and a circuit of treewidth w compiles to a structured DNNF
of size linear in the circuit size times an exponential in w. A tree
layout opened at b shared producers gives a tree decomposition of
width at most b+O(1). The direct communication argument above also
applies to arbitrarily large circuits and preserves the additive N term.
[Bova, Capelli, Mengel and Slivovsky](https://arxiv.org/abs/1411.1995) ·
[Amarilli, Capelli, Monet and Senellart](https://arxiv.org/abs/1811.02944)

## Larger factors for polynomial-size descriptions

A complementary transfer uses an explicit family h on a inputs that
requires ca−o(a) gates over the full binary basis and is uniformly
computable in P. Choose a polynomially larger than the SAT selector
count. For a signed description introduce a fresh input z and use

    D(p) OR (z AND OR_i x_i) OR (C(p) AND h(x)).

On UNSAT the disjoint-variable baseline is read-once on every named
input. On SAT pin a consistent selector, z=0, to recover h. All variables
are essential in both cases: p=0 exposes the z-gated OR, and z=0
at a zero of h exposes D. Thus any fixed gap factor below c follows
for polynomial-size signed descriptions.

For a *monotone* description replace each x_i by two rails u_i,v_i.
Use the OR of all rails in the baseline. Compute a monotone positive
wire and its complement for each source gate of h using input pairs:
write the accepting and rejecting gate-table rows as ORs of positive
two-literal rail conjunctions. On consistent rails (x_i,¬x_i) the
positive output equals h. The circuit size overhead in description is
constant per gate. On the hard restriction, identify both rails with
the appropriate literal of a single data variable. Any negated raw
operand can be absorbed into its next gate's two-input truth table
without increasing size. Constant restrictions can also be propagated
without adding gates. Thus the minimum is at least ca−o(a) while the
full input count is 2a+o(a); on UNSAT the minimum remains its floor.
The same zero of h on consistent rails witnesses relevance of the
selector inputs. This yields every fixed factor below c/2.

Li and Yang's published 3.1a−o(a) theorem supplies c=3.1.
Mishra and Santhanam's November 2026 preprint, revision 1, reports
4a−O(log a) for a function in P; inserting that theorem gives every
fixed factor below four with signed presentations and below two with
monotone ones. These larger factors do not assert read-two input
formulas. Neither transfer claims a stronger explicit Boolean circuit
lower bound for h.
[Li and Yang](https://doi.org/10.1145/3519935.3519976) · [Mishra and Santhanam, revision 1](https://eccc.weizmann.ac.il/report/2026/260/)
