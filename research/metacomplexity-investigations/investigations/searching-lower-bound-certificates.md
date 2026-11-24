# Searching for the strongest minterm–maxterm gate certificate

For an essential n-input monotone Boolean function f, let

    μ(f) = max |M ∩ Z|.

Here M is a minimal set of inputs to set to one to force f=1. Z is a
minimal set of inputs to set to zero to force f=0. The proof-trace
bound gives at least n−2+μ(f) gates for every fan-in-two monotone
circuit for f. The certificate itself is short: a pair of bit vectors.
For an explicit monotone formula, evaluating it and dropping each
chosen coordinate checks both minimality conditions in polynomial time.

We show that finding the strongest certificate is already a MaxSAT
optimization problem on monotone DNFs consisting of graph edges and
one additional long term. This gives an exact correspondence of optimum
values, a parsimonious reduction for full-overlap certificates, and a
matching approximation threshold on the construction from Max-E3-SAT.
The objective is the strength of this particular lower-bound proof.
The minimum circuit size of the DNF can exceed the certified number.

## A graph with a clause vertex for every input clause

Let Φ have n Boolean variables and m≥3 nonempty clauses. Introduce
two literal vertices for every variable, joined by an edge, and one
vertex c_j per clause. Join c_j to each literal appearing in that clause.
The set S of clause vertices is independent. Let f be the OR of all
two-variable edge terms and the one term ∧_{s∈S}x_s. All terms are
minterms: S is independent and has size at least three. Each input is
essential because it lies in a minterm.

For a satisfying assignment of k≥2 clauses, take the independent set
of its n true literals and add the vertices of all unsatisfied clauses.
This is a maximal independent set in the graph: unchosen literal
vertices have their chosen mate as neighbor, and every remaining
clause has a chosen true literal. Its complement Z is a minimal graph
vertex cover and contains exactly k clause vertices. Since it hits
the long term as well, it is a minimal zero certificate for f.
Thus |S∩Z|=k.

Conversely suppose a minimal zero certificate meets S at least twice.
Its long term witnesses the necessity of none of its vertices: deleting
one still leaves a clause vertex in Z. Every vertex of Z must therefore
be necessary for a graph edge. The complement is a maximal independent
set, and its literal vertices specify a consistent partial assignment.
Each clause vertex in Z has a neighbor outside Z, necessarily one of
these chosen literals. Any extension of the partial assignment
satisfies all |S∩Z| such clauses. A zero certificate hitting S only
once cannot improve an optimum of at least two. All other minterms
have size two. Whenever OPT(Φ)≥2 we obtain

    μ(f) = max_Z |S∩Z| = maximum number of simultaneously
                           satisfiable clauses of Φ.

In particular deciding μ(f)≥m is NP-complete. More precisely, the
certificates attaining m are in bijection with satisfying assignments.
If all clause vertices belong to Z, the complementary independent
set contains only literal vertices and must select exactly one per
variable by maximality. These assignments give exactly the certificates
constructed above. Since m>2, the long term is also the unique possible
first member of such a pair. Counting full-overlap pairs is #P-complete.

For NP-hardness and this exact counting statement we may take the
two-variable graph to be subcubic. Replace each occurrence of an
original Boolean variable by a separate Boolean copy and add a directed
cycle of binary implications around its copies to enforce equality.
For a variable with one occurrence no extra clause is necessary.
For a variable with zero occurrences retain its free variable. Each
literal appears in at most two clauses, each clause has width at most
three, and every original assignment has exactly one consistent
extension. Repeating clauses in the source, before splitting occurrences,
handles the lower bound of three clauses without affecting satisfiability
counts. Consequently the explicit monotone DNF is read at most four.

## Approximation and verification

On exact-three-distinct-literal clauses, any random assignment satisfies
7/8 of the clauses in expectation. Conditional expectation constructs
one at least as good in polynomial time; use the complement construction
to obtain a certificate. For every ε>0 it is NP-hard to distinguish a
certificate with full overlap m from one whose maximum overlap is at
most (7/8+ε)m. This is Håstad's Max-E3-SAT gap applied to the exact
identity. The degree-three refinement above is used for exact decisions
and counting; the equality clauses change the approximation ratio.
[Håstad, Theorem 6.5](https://people.kth.se/~johanh/optimalinap.pdf)

In hypergraph terminology μ is the smallest r such that the minterm
hypergraph is r-exact. Prescribing vertices in a minimal transversal
is the transversal extension problem. Maximizing the number of
prescribed vertices in a minimal graph cover is known as Max Ext VC.
These older connections explain why the optimization is difficult.
The conclusions here identify its explicit counting interpretation
and its role in searching for a gate lower bound. Priority for the
particular SAT construction is undetermined.
[Boros et al. on r-exact hypergraphs](https://doi.org/10.1016/j.disc.2010.05.017) ·
[Casel et al. on vertex-cover extension](https://hpi.de/friedrich/docs/publications/2019/CIAC.pdf)

## A fixed formula with universal certificate-extension queries

The proof gives the whole downward-closed family, in addition to its
largest cardinality. For every T⊆S, there exists a minimal zero
certificate Z containing T exactly when the subformula consisting of
clauses T is satisfiable. The forward proof above applies to |T|≥2.
A singleton clause is satisfiable because it is nonempty, and the
empty subformula is satisfiable. For the converse any assignment
satisfying T gives the complement construction, which is a minimal
zero certificate whenever it satisfies at least one original clause.
One can arrange this also when T is empty. The inclusion-minimal
nonextendible requests are therefore exactly the minimally
unsatisfiable subformulas.

A fixed polynomial-size monotone DNF per input length, of the subcubic
one-long-term form above, can consequently realize **every downward-closed
NP/poly predicate** by queries that merely prescribe vertices to be in a
minimal zero certificate. Include a fixed mandatory set of clause
vertices and let each external bit request one more distinct clause
vertex. For the upper bound, guess Z and verify inclusion and
minimality. The family is downward closed under removing requests.

For the converse take a polynomial-size verifier V_n(y,w) for a
downward-closed language. Then x belongs exactly when there are y≥x and
w with V_n(y,w)=1. Use the fixed Tseitin clauses for an accepting
computation as mandatory clauses and one optional positive unit clause
y_i for each external bit. Select the latter exactly when x_i=1.
Use occurrence splitting for the entire fixed formula, including its
optional clauses. The cycle consistency clauses remain mandatory.
Other unrequested clauses impose no constraint by the subformula
identity just proved. Harmless fixed clauses ensure at least three
clause vertices. All graphs, all variable occurrences, and the DNF
are now fixed before receiving x. Only inclusion requests change.

In particular a polynomial-size preprocessing circuit answering all such
queries on all these fixed formulas would imply NP⊆P/poly: the same
construction for unrestricted languages can encode an external input
using both rails, requesting y_i on a one and ¬y_i on a zero.
