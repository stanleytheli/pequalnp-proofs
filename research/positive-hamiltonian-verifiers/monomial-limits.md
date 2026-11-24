# Monomial limits and closure of positive Hamiltonian circuits

Let a finite nonnegative arithmetic circuit have sums, products, and
oracle gates whose choices each take a product of an explicitly bounded
list of slots. An order-k permanent or directed Hamiltonian-cycle gate
is an example. Parameters may be arbitrary nonnegative scalars varying
along a sequence. Suppose the output converges pointwise to a finite
value on a domain of nonnegative data inputs. Each ordinary data leaf
retains the same nonnegative input function. A fixed bound s on circuit
size also allows finitely many topologies, choices of labels and zero
patterns; pass to one subsequence at that size.

## One monomial parameter suffices, with short integer orders

A positive parse contributes c^α m(x), for its nonnegative data monomial
m(x). Among the finitely many parses at fixed size, discard those whose
data monomial vanishes identically on the domain. For every remaining
parse choose one input with m(x)>0. Nonnegativity of all other terms
and pointwise boundedness bound c^α there. Pass to a subsequence where
all these scalar weights converge. Write p_α for each limit. If all are
zero the result is the zero function. Otherwise the logarithmic
projection argument in the support note gives integers w,T exposing
the positive indices: w·α=T if p_α>0, and w·α<T otherwise. Each integer
has O(s²+s log(s+1)) bits for explicit size s.

On the surviving finite set, log p belongs to the real linear span of
the exponent columns: the vectors (Σᵢαᵢ log cᵢ)_α lie in that subspace
and converge there, and finite-dimensional linear subspaces are closed.
Thus choose positive finite constants aᵢ with a^α=p_α simultaneously
for all survivors. A global scale may instead be included by adding a
constant column. Replace cᵢ by aᵢ t^(−wᵢ) and multiply the output by
t^T. At every surviving parse this gives its exact limiting coefficient;
at every other permitted parse the coefficient tends to zero as t→0⁺.
The discarded parses vanish on the domain at every positive t. The new
one-parameter family therefore has precisely the original limit on the
whole domain. Finitely supported monomials and additions require no
interchange of an infinite sum and a limit.

If every parse has some common permitted input (e.g. the all-ones point),
the integer orders have a smaller bound of O(s log(s+1)) bits. Take any
exposing objective from the preceding argument and compute each gate's
maximal attainable score under it. Introduce unknown wᵢ and one unknown
gate height hᵥ. At every live gate impose equality of hᵥ with the selected
child sum on every maximizing choice under the old objective; impose that
all other choice sums be ≤hᵥ−1. Use h=wᵢ on scalar leaves and h=0 on data
leaves. After scaling real scores all strict gaps can be made at least
one. This system has O(s) variables and integral coefficients of size
O(s), even for repeated children. Bound the unknowns in absolute value
by an additional minimized variable and use a vertex and Cramer's rule.
The integer scaled solution has the asserted bit length. It preserves
the same maximizing choices at every live gate by induction. At least
one positive root parse exists, so the maximizing root score is the
threshold for the surviving parses.

## Exact positive simulation of optimal tour faces

With a common permitting input, the surviving parses are exactly those
using local maximizing choices recursively. Keep only maximizing
alternatives at additions, retain all slots of an ordinary product, and
at each Hamiltonian gate keep the directed tours achieving its fixed
integer target score. A Boolean verifier guesses the incident-arc bits
of one tour, deterministically verifies that every indegree/outdegree is
one, checks traversal from vertex 1 visits every vertex, and sums the
signed integer slot scores and compares them to the stored optimum.
There is one input incidence string per tour. No ordering or auxiliary
certificate is guessed in addition to that string. The scores have
polynomial bit length, and this verifier has polynomial size in s.

Use the weighted positive-to-Hamiltonian construction: give the true
flag of each chosen arc the value of the corresponding child gate.
It compiles the sum over maximizing tours into one polynomial-order
ordinary Hamiltonian gate with positive constants and child inputs.
The flags pass the original real child values even though the verifier
itself uses Boolean witnesses. Share each compiled physical gate
throughout the DAG. Use the finite scalar values aᵢ from above.
The resulting monotone Hamiltonian-oracle circuit computes the limit
exactly on the domain with polynomial explicit overhead and no
restriction on intermediate degree. In particular the family of positive
Hamiltonian-oracle circuits is closed up to polynomial overhead under
coefficientwise limits and under finite pointwise limits on the full
Boolean cube. In the latter case its formal polynomial is one representative
of the limiting corner values. This concerns nonnegative parameters and
does not transfer to signed Laurent border complexity.

For a permanent gate, maximizing assignments form a face of the bipartite
assignment polytope. The face is specified by eliminating a set of slots
since the only inequalities are coordinate nonnegativities. Thus an
ordinary masked permanent already computes the maximizing slice. This
recovers the positive-permanent closure on common-permitting domains.

## A single projection on a Boolean promise with bounded degree

Suppose the ordinary total degree of the nonnegative output polynomials
is bounded by Δ, uniformly along the chosen fixed topology. Delete zero
gates and replace each gate computing a scalar-only polynomial by a single
scalar leaf. Its value is a new nonnegative parameter at each step.
Pass to a common fixed zero pattern, then apply the preceding face and
amplitude argument anew to the surviving parses of this simplified
topology. The exposed orders, threshold and amplitudes used below refer
to these new scalar leaves, including their original fixed correlations. A
positive parse now has at most Δ occurrences of nonconstant gates at
each depth: fixing its outer choices and substituting a positive-degree
term independently at each such occurrence gives a root term of at
least that degree. All terms survive because there is no cancellation.
After the scalar simplification, at most O((s+1)²(Δ+1)) total gates and
slots therefore occur in a parse (a deliberately loose bound). A constant
output can be treated separately. This counts every scalar leaf too,
since a single nonconstant occurrence has at most s child slots.

Write the admissible parse in a canonical bounded encoding, including
all local choices in order and a uniquely determined padding. Use a
polynomial-size Boolean verifier for valid choices and for the single
equality w·α=T, where the objective was obtained only from parses permitted
somewhere on the promise. Any accepted parse not permitted anywhere has
zero data monomial on that promise. The remaining accepted parses are
precisely the survivors. Deterministically tabulate multiplicities of
input and scalar leaves. Using unary threshold flags up to the polynomial
parse bound, emit each requested copy of its variable or finite scalar aᵢ.
The weighted verifier compiler now realizes the limiting values by a
single monotone projection, when data leaves are individual variables or
fixed scalars, of a polynomial-order directed Hamiltonian
cycle, on the entire given promise. The argument applies to any nonnegative
input domain, since a parse failing everywhere simply evaluates to zero
there. It also gives the exact non-border flattening of polynomial-size,
polynomial-degree positive Hamiltonian circuits. The proof relies on
explicitly checkable local choices. In particular it permits both
Hamiltonian and permanent gates.

Both parts are nonuniform statements. They require no computation of
the limiting real amplitudes from a specified rate of convergence.
