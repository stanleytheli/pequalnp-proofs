# Fewer witnesses suffice in the fleet's local parity-to-partial-MCSP bound

The public program's L-meta-043 examines a fixed-format q-local reduction
from odd parity to partial MCSP. Its recorded result gives, for n≥4q+1,
a consistent circuit of size (4q+1)s+3(4q+1)² on **every** input, even
those whose target has no size-s completion. The underlying technique
combines circuits that witness membership for neighboring odd inputs.
The record attributes that technique to prior gap work.
[Fleet record L-meta-043](https://data.pequalnp.com/data/lemma/L-meta-043.101d01304a2d.json)

With the fleet's actual two-bit encoding, n≥3q+1 suffices, and the
size bound improves to

    k s + 9k + 10⌈log₂(k+1)⌉ + 10,        k=3q+1.

The q=1 case already has the better bound 3s+4 in the fleet. This
refinement is an independent research result for general q. It has
not been submitted as a project proof or assigned ticket.

## The asymmetry in the encoding

Each encoded output position on a given input has a certificate of at
most q input bits. Fixing those bits forces that output position.
The header, target arity and size bound are fixed, so the positions
for a given table row have the same meaning on every input. An
unspecified row has code 00, a specified zero has 10, and a specified
one has 11. Thus a specified one is forced by preserving its value
bit alone. A specified zero is forced by preserving both bits.
[Locality definition](https://raw.githubusercontent.com/brilliant-hq/pequalnp-proofs/main/lean/PEqualNP/Defs/MetaComplexityLocal.lean) ·
[Partial table encoding](https://raw.githubusercontent.com/brilliant-hq/pequalnp-proofs/main/lean/PEqualNP/Defs/MetaComplexity.lean)

On an odd input a size-s completion already exists. On an even input
x choose k distinct input positions, flip them one at a time, and
choose a size-s completing circuit on each resulting odd neighbor.
Use these same k witnesses for all target rows. On a row specified
one at x, at most q flips hit a certificate fixing its value bit.
At least k−q=2q+1 witnesses vote one. On a row specified zero at x,
at most 2q flips can hit either of its two certificates. At most 2q
witnesses vote one. A threshold at 2q+1 therefore agrees on every
specified row, no matter how the witnesses behave on unspecified
neighbor rows. This also works whenever each negatively classified
source input has k distinct positive neighbors obtained by single-bit
flips. No restriction on the size of other source slices is needed.

## Binary circuit cost

Run the k witness circuits in parallel, sharing their input wires.
A three-input full adder uses at most nine binary AND, OR and unary
NOT gates: compute XOR(a,b) as (a OR b) AND NOT(a AND b), repeat for
the sum with c, and reuse the two internal ANDs in the carry OR.
Compress triples of same-weight bits to a sum bit and a carry bit;
each compression decreases the total number of bits by one. After at
most k compressions there are at most two bits at each weight. No
weight larger than k can occur, as the sum of the formal weights of
all wires begins at k and is preserved. Add the last two rows with
one full adder per weight. At most ⌈log₂(k+1)⌉+1 bits, including the
last carry and cost for constant padding, suffice. Compare the sum
with the fixed threshold from least to most significant: at a zero
threshold bit use OR of the input bit and the prior comparison; at
a one threshold bit use AND. The displayed bound allows a constant
true gate, zero padding, and the leading comparison. An absent output
of a source circuit can be wired to the shared false constant.

## Sharpness for this neighbor-voting argument

For q≥2, any rule that only sees 3q neighbor votes on a single
specified row can receive the same vector on a true and on a false
center. This is sharpness for the rowwise aggregation step. It does
not exclude other global constructions for partial MCSP.

On a false center (the all-zero input), use q variables u_i, q
variables v_i and q dummy coordinates. Define

    U = OR_i [u_i AND (AND over j≠i of NOT v_j)].
    V = OR_j [v_j AND NOT u_j].
    encoded row = (NOT U, V).

U and V are disjoint, so this is always a legal code. Each predicate
and its complement have certificates of size at most q. For U, a
true certificate is one term, and a false certificate selects one
false literal per term. The identical argument applies to V because
q≥2. At the center the row is zero. Flipping any u_i makes it
unspecified, while flipping any v_j makes it one. Choose the q optional
votes to be one and the resulting vote vector has 2q ones followed
by q zeros. On a true center, keep presence one and define the value
to be the conjunction of the q negated dummy bits. Those same 3q
neighbors now produce exactly the same votes. The certificate
conditions and even the multiplicities of false and true votes thus
cannot improve the threshold count for this method.

A one-hot encoding of partial rows would permit 2q+1 witnesses,
since each defined label would then be forced by its own single bit.
Changing encodings changes certificate complexity. The 3q+1 result
above uses the encoding fixed by the fleet.

## Polynomial output length gives a constant approximation factor

One need not use a new witness for every possible damaged direction.
Suppose an even input has m positive one-flip neighbors of the same
format. Let R₀ and R₁ be its numbers of specified zero and one rows.
Draw k neighbor directions independently with replacement. A threshold
t (output one if at least t votes are one) works for every row whenever

    R₁ · binom(k,k−t+1) (q/m)^(k−t+1)
      + R₀ · binom(k,t) (2q/m)^t < 1.

Indeed, a positive row can fail only on a sample containing at least
k−t+1 hits in its at-most-q potentially damaged directions. A negative
row needs t hits in its at-most-2q such directions. A union bound
over candidate subsets of sample positions and then over the rows
proves existence. Repeated directions may share their witness circuits.
Choosing k=1 in particular shows an exact negative instance must obey
q R₁+2q R₀≥m. Given the actual neighbor tables, samples can also be
chosen by conditional expectation in polynomial time for fixed k.
Finding a source neighbor's promised completing circuit is separate.

## Recovering a common format even when the reduction may vary it

Assume only that every odd input maps to a member of partial MCSP
and that every output string has length ≤M. No promise on the formatting
of even outputs is necessary in the following regime. Put
h=⌊log₂(M+1)⌋. At a center x, fix its output length L by certifying
the symbol at L is absent and, if L>0, that the symbol at L−1 is present.
These two certificates use at most 2q positions. For this length there
are at most h candidate size bounds, since L=s+1+2^(a+1) for target
arity a. For each candidate s, a malformed output violates its unary
header at one symbol or has an illegal 01 row at two symbols. Freeze
one such violation per candidate. If n>2q(h+1), at least one source
direction remains free. An even malformed center would then have an
odd malformed neighbor, a contradiction. All even outputs are valid.

At a valid center, freeze the same length information, the zero
delimiter at the actual size bound s and the true bit at each *earlier
candidate delimiter*. Larger bounds are excluded by that zero. This
uses at most q(h+2) source positions. Every odd neighbor outside these
positions is a member and therefore a valid table of exactly the
center's arity and size bound. We can take m≥n−q(h+2).
This argument relies on certificate locality of absent as well as
present output symbols, exactly as in the project's definition.

For M≤n^d, q≤n^(1−ε), with fixed d>0 and ε>0, m=n−o(n). Take
r=⌊d/ε⌋, k=2r+1, t=r+1. Since R₀+R₁≤M, the bound above tends to zero:
ε(r+1)>d. Beyond a finite threshold every even output therefore has
a completion with at most k s+O(k+log k) gates, including when arity
and s depend on the input. Thus these reductions cannot achieve a
diverging multiplicative gap measured against s+1. This statement
concerns local maps from parity; arbitrary deterministic polynomial-time
reductions to partial MCSP remain open. The probabilistic sparsification
is an application of the established neighboring-witness method.
[Allender, Ilango and Vafa](https://eccc.weizmann.ac.il/report/2018/173/) ·
[Murray and Williams](https://www.theoryofcomputing.org/articles/v013a004/v013a004.pdf)

## Average-case and randomized local maps

The same calculation applies even if the map makes errors. Call an
output small when it belongs to the project's ordinary partial MCSP
language at its own stated bound. For k=2r+1 call an output large when
it is malformed or no circuit of size ks+9k+10⌈log₂(k+1)⌉+10
completes its table at its own bound s. Outputs between the promises
do not count as correct on either input parity. Define

    B = max(2q(h+1), q(h+2) + 2q [M binom(k,r+1)]^(1/(r+1))).

For an arbitrary center with more than B small one-flip neighbors,
the malformed-output test leaves at least one small neighbor, hence
the center is valid. Freezing the center's format leaves more than
2q[M binom(k,r+1)]^(1/(r+1)) small neighbors of the proper arity
and bound. The sample bound gives a k-witness majority completion.
In particular, **every large center has at most B small neighbors**.
This is a local assertion about one map, without a reduction hypothesis.

Let p be the fraction of even inputs mapped large and o the fraction
of odd inputs mapped small. Each of the n coordinate flips bijects
the even slice with the odd slice. Count the pairs from an even input
to a small odd neighbor. Dividing by n·2^(n−1) gives

    o ≤ 1−p + p·B/n.

Thus the map's success on uniform parity inputs, (o+p)/2, is at most
1/2+B/(2n). A mixture of maps obeys the same bound, with no
independence assumption between their bits. For a randomized local
reduction the per-seed map must satisfy the same uniform bound on
output length and per-bit certificate complexity. For M≤n^d,
q≤n^(1−ε), r=⌊d/ε⌋, the advantage bound tends to zero, at rate
O(n^(−ε) log n + n^(−ε+d/(r+1))). In particular there is no
bounded-error reduction of this type to the indicated constant-factor
gap, even if correctness is only required on uniformly random source
inputs. Exact membership, general polynomial-time reductions and
reductions without the stated locality promise are different questions.

The row-count dependence has a matching exponent for this majority
method. Fix r and suppose r+1≤q≤n. Partition the n directions into
blocks of size at most ⌊q/(r+1)⌋. For each union of r+1 or fewer
blocks, create a center-one row with constant presence and value the
AND of the negations of the directions in the union. All its output
bits are q-local. Every sample of 2r+1 directions, including repeats,
has its first r+1 directions in one of the displayed unions. The
resulting majority is incorrect on that row. There are
O_r((n/q)^(r+1)) rows, matching the sufficient bound's exponent for
fixed r. Pad to a power of two with unspecified rows to obtain a partial truth table. This construction addresses witness-majority aggregation
locally and does not purport to be a parity reduction.

## A fixed family of sparse SAT inputs inherits the obstruction

Take n≥3 Boolean variables in a cycle. For each edge add the two
clauses enforcing x_i XOR x_{i+1}=z_i, with indices taken modulo n.
When z_i=0 the pair is (¬x_i OR x_{i+1}) and (x_i OR ¬x_{i+1}).
When z_i=1 the pair is (¬x_i OR ¬x_{i+1}) and (x_i OR x_{i+1}).
Keeping the positions of the literals fixed, each bit of the encoded
formula is constant, a single input bit, or its complement. Each
variable occurs four times. The cycle has exactly two satisfying
assignments if the parity of z is even, and none if it is odd. Flip
the initial z bit to put satisfiability on the odd source slice.

Any q-bit certificate for a bit of a map on the resulting SAT inputs
pulls back to at most q parity bits, even when these certificates are
specified only under the promise that the input lies in this family.
Hence the entire randomized average-case obstruction applies directly
to partial-MCSP gap reductions from SAT, already on one fixed cycle
incidence pattern with random constraint signs. In a fixed-width
literal encoding the formula length is N=O(n log n). If M≤N^d and
q≤N^(1−ε), the same k=2⌊d/ε⌋+1 works. The extra logarithmic factors
in the bound tend to zero against the strict exponent ε(r+1)−d>0.
For syntactically full three-literal clauses with distinct variables,
replace each binary clause C by C OR u and C OR ¬u with a separate
fresh u per binary clause. This preserves satisfiability, the
bit-local indexing, linear clause count and bounded occurrences.

More generally at one center one may replace the coordinate flips
with arbitrary neighbors whose changed sets of input coordinates are
pairwise disjoint. Every certificate still meets at most q of these
sets. The proof of the local cap B therefore gives the same bound
on the number of small neighbors from such a collection at any
large center. For a worst-case randomized reduction, a negative
input with m disjoint sensitive blocks thus has at least one input
among the center and its m positive neighbors with success probability
at most 1/2+min(1,B/m)/2. To see this, give the center half the mass
and give its neighbors the other half, uniformly. For each seed, a
correctly classified center has at most B correctly classified
neighbors. An incorrectly classified center earns success at most
1/2 on this distribution. Averaging over the seed proves the bound.
This last statement requires no global cube parity structure.
