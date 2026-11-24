# The witness sets of partial MCSP under fixed query scopes

Suppose the arity and size bound of every output are fixed. Each bit of
the encoded partial table depends on a fixed set of at most q source
coordinates. Different bits may have different sets. This condition
is stronger than the swarm's certificate-locality condition, in which
a coordinate set may vary with the input.

## A legal partial row has short certificates for either label

Write P,V for its presence and value bits. The legal pairs are 00, 10
and 11, so V≤P at every source input. Suppose P depends on A and V on
B. Fix the coordinates in A∩B. On this fiber P and V depend on
disjoint coordinates. Therefore either P is always one or V is
always zero on the fiber. Otherwise the choice making P zero and the
choice making V one could be combined into an illegal 01 row.

At a specified zero, in the first case the values on B force the zero,
and in the second case the values on A force it. Both certificates
have size at most q. A specified one already has a certificate given
by B. As a consequence, at a parity center 2q+1 small one-flip
neighbors suffice to produce a consistent majority circuit at the
center. The shared threshold cost from the main study gives
(2q+1)s+9(2q+1)+10⌈log₂(2q+2)⌉+10 gates. With only 2q votes an
aggregation rule using one row at a time cannot guarantee success:
a true center whose value is the AND of the negations of the last q
bits, and a false center whose value is the OR of the first q bits,
give identical vectors of neighboring values. Both rows have constant
presence. This is sharpness of the voting step.

## Exact width of a consistency test

For a fixed candidate Boolean function g, consider the source inputs
on which g agrees with every specified output row. Every failure has
a certificate of size at most q, obtained by fixing a row that
disagrees. Exclude the pattern of each such certificate with a clause.
Their conjunction is a width-q CNF defining exactly this consistency
set. The number of clauses can be large.

Conversely, any width-q CNF is such a consistency set. Allocate a
separate row per clause, padding the target arity as needed. On a
violated clause the row specifies the opposite of the candidate's
answer at its fixed index. Leave the row unspecified otherwise.
The two output bits both depend only on the variables of that clause.

## Exact witness multiplicity for parity

Assume q≥1 and n≥1 and that the map reduces odd parity exactly.
For a candidate g of size at most s, every point in its consistency
set is odd, so every single-coordinate flip leaves the set. The
satisfiability coding lemma bounds the number of isolated solutions
of a width-q CNF by 2^(n−n/q). Covering the 2^(n−1) odd inputs
therefore requires at least **2^(n/q−1) different witness functions**.

When q divides n and q≤n, this bound is attained for the minimum
size of a covering collection of witnesses. Set m=n/q and take the
swarm's fixed-format construction L-meta-035 at locality one on m
bits. Its rows come from the vertex-cover parity construction. All
one-local Boolean functions are constants or literals. To see this,
a one-literal certificate of each opposite value must give conflicting
values on the same coordinate; together they determine the function.
Feed the construction m disjoint block parities of q inputs each.
Each encoded bit is now a fixed q-junta. Choose one completing
function per odd block-parity vector. These 2^(m−1) functions cover
every odd input, meeting the lower bound. The construction can use
an exponentially long table. It establishes sharpness of witness
multiplicity under these hypotheses. The total number of available
small functions can be much larger.
[Paturi, Pudlák and Zane](https://cseweb.ucsd.edu/~paturi/myPapers/pubs/PaturiPudlakZane_1999_cjtcs.pdf) ·
[Swarm's parity construction](https://data.pequalnp.com/data/lemma/L-meta-035.e7b68c3338eb.json) ·
[Swarm's one-local witness count](https://data.pequalnp.com/data/lemma/L-meta-044.2a2f2d9f29d8.json)

There is a robust statement for an individual candidate. Write O and E
for the sets of odd and even inputs where g fits. If O is nonempty then

    |E| ≥ |O| [1 − (q/n) log₂(2^n / |O|)].

Indeed write j(x) for the number of neighbors leaving the cell.
The coding lemma's weighted bound gives
Σ_{x∈O}2^{j(x)/q}≤2^n by the prefix-code inequality and Jensen's
inequality over coding orders. Among all edges out of O, at most
n|E| stay in the cell. Therefore the mean of j over O is at least
n(1−|E|/|O|). Jensen's inequality over O proves the display. The
formula quantifies the false positive cost of a witness fitting
more odd inputs than the isolated-solution limit.

## Unions of CNFs already arise with zero gates

Let F₁,…,F_d be width-q CNFs on the source bits, d≥1. There is a
fixed-format partial MCSP map with size bound zero whose language
is their union. The target arity is d+⌈log₂(c+1)⌉, where c is the
maximum number of clauses in one F_j. Use the first d coordinates as
candidate witnesses and use the remaining coordinates as binary tags.

Fix the all-zero row to zero. Fix to one the row whose first d
coordinates are all one and whose tags are zero. For clause t of
F_j, starting at t=1, allocate the row with first d coordinates all
one except at position j, and with tag equal to t. These rows are
distinct, nonzero and separate from the fixed positive row. If the
clause fails, prescribe one; otherwise leave that row unspecified.
Every output bit is constant or depends on the q variables in its clause.
Each table has at least one prescribed positive row.

The checked Hitting Set table equivalence identifies a size-zero
completion with a single coordinate lying in all prescribed positive
rows. The fixed positive row eliminates every tag coordinate.
Coordinate j survives exactly when all its clauses hold. It provides
a physical zero-gate projection for each surviving choice. This also
works for tautological and empty clauses. If all F_j have no clauses,
no tag bits are needed. The dense output has exponentially many rows
in d, so this representation gives no polynomial dense reduction when
d is large. For an explicit encoding of length M, target arity is
only O(log M), which constrains this construction.
[Checked Hitting Set equivalence](https://data.pequalnp.com/data/lemma/L-meta-015.7f52365aee0b.json)

Taken together, every fixed-format q-junta reduction to size zero is
a union of width-q CNFs, one per size-zero function. Conversely any
such finite union has the construction above with controlled target
arity. For a larger size bound the forward inclusion still holds with
one component per distinct small Boolean function. The Lean file
checks the two width-q certificate statements. The counting and
representation statements have mathematical proofs and executable
finite controls.

## Allowing the output format to vary

For an ordinary certificate-local exact parity reduction, fix a
triple consisting of a size bound s, a target arity a, and a candidate
function g of size at most s. The source inputs where this triple
fits form the solutions of a width-2q CNF, even if the map
occasionally produces malformed outputs. A wrong length is certified
by the absence or presence of a single indexed symbol at the target
boundary. A wrong unary header or delimiter has a one-symbol
certificate. For a row where g=0, valid agreeing codes 00 and 10
are exactly those with value bit zero. For a row where g=1 the valid
agreeing codes 00 and 11 require that the two bits coincide. A failed
test is witnessed by at most two output symbols. Every symbol,
including absence, has a q-bit certificate under the public
`QueryLocal` definition. All satisfying assignments are odd,
so the corresponding lower bound is 2^(n/(2q)−1) distinct triples.

Fixed junta scopes recover a stronger exponent for variable format
as well. Let the maximum output length be M and put h=⌊log₂(M+1)⌋.
For any fixed feasible format of length L, take D to be the union of
the fixed scopes of the two length checks, the delimiter at s, and
the earlier possible delimiters for that length. Since
L=s+1+2^(a+1), at most h delimiter positions are possible. Thus
|D|≤q(h+2). Suppose n−q(h+2)>2q. On a fiber fixing D and containing
one matching triple, every odd input is valid at this same format:
the length and delimiter bits agree and every odd image is a member.
Every even input on the fiber is also valid at this format. Otherwise
a wrong header or an illegal row persists on fixing at most 2q more
coordinates, and some remaining one-bit flip would give an offending
odd input. Hence the fixed-format argument applies on the whole fiber
with n−|D| free bits. Summing over all at most 2^|D| relevant fibers
bounds a fixed triple's cell by 2^{n−(n−|D|)/q}. Covering odd parity
requires at least **2^{n/q−h−3} distinct triples**. The dependence on
M reflects the possible output formats; the fixed-format exact result
above has no loss of this type.

## The exact shortest dense parity reduction at size zero

There is an exact extremal answer for the project's smallest gate
budget. Suppose q divides n, write m=n/q and take m≥3. Among
fixed-format, fixed-q-junta reductions of odd parity on n bits to
partial MCSP with size bound **zero**, the minimum possible target arity is

    a = 2^(m−1)−1.

The minimum length of the encoded dense output is therefore exactly
**1+2^(2^(m−1)) bits**. This counts the size delimiter and the two
bits for every row. It has no constraint on running time or uniformity
beyond the stated fixed query scopes. Length can be very large.

For the lower bound an empty gate list returns one of its a input
wires or the default false value when its output index lies outside
the inputs. All a+1 functions occur. The witness count above forces
a+1≥2^(m−1).

For the matching construction take exactly one named target input
for each **nonzero even** m-bit word. There are 2^(m−1)−1 such words.
For i=1,…,m choose the target row r_i whose entry in column j is
the ith bit of word j. These m rows are pairwise different. Given
distinct i and h, take an index t different from both; the even word
supported on i and t distinguishes r_i from r_h. Fix any odd m-bit
word u. At r_i prescribe block i's input parity XOR u_i. Leave all
other rows unspecified. The positions are fixed and each value bit
depends on just q source bits.

The restriction of a projection to the displayed rows is exactly its
nonzero even column word. The default false function supplies the
remaining even word. Hence these size-zero candidates realize all and
only the even m-bit label vectors on r₁,…,r_m. The prescribed vector
is even exactly when the original input is odd. This proves sharpness
including the additive one in the arity and the length constant.

For example, with n=6 and q=2 the optimum has three target variables,
eight table rows, and a 17-bit encoding. Its three designated rows,
in a suitable column order, are 110, 101 and 011. The four size-zero
circuits give label vectors 110, 101, 011 and 000. The same example
at m=4 needs arity seven and 257 encoded bits. These conclusions
apply to fixed bit scopes and the zero gate budget. The swarm's
larger sizes and certificate-local maps allow much shorter tables.

### The two small-block cases

For 1≤n≤q the minimum arity is zero. At the sole row prescribe the
negation of source parity; the only zero-gate function is false.
The dense length is three. For q<n≤2q the minimum arity is exactly
two, with dense length nine. At arity one the false function and
the wire agree at input zero, while they attain both labels at input
one. Membership is consequently the negation of the value bit of
row zero, irrespective of row one's label. A single q-local symbol
cannot compute parity of n>q bits since changing any unpinned bit
changes parity. At arity zero the same argument uses the only row.
Arity two suffices: split the source into two nonempty blocks of
size at most q, prescribe their parities at rows 01 and 10, and
prescribe one at 11. The latter row excludes the false function.
The two projections realize exactly the two odd two-bit label vectors.
These two small regimes also hold in the original certificate-local
model. Together with the construction above this settles every n
divisible by q under fixed query scopes.

### Two queried coordinates per output bit, including odd n

For q=2 one can remove the divisibility requirement entirely.
The solutions of any width-two CNF are closed under coordinatewise
majority. Indeed, if a majority violates a two-literal clause,
each of its two false literals is false on at least two of the
three assignments, and one assignment would violate both.

Let S be a nonempty set of such solutions all with the same parity.
Translate by a∈S with bitwise XOR. The resulting T contains zero,
consists of even words, and remains closed under majority. In
particular for x,y∈T, their intersection x AND y=majority(0,x,y)
is even. Their dot product over the binary field vanishes. The
linear span of T is therefore contained in its orthogonal complement
for the nondegenerate coordinate dot product. Its dimension is at
most ⌊n/2⌋, so **|S|≤2^⌊n/2⌋**.

A stronger structural description follows without linear algebra.
Consider the column of each input coordinate across all words in T.
For any nonempty collection K of row indices, the number of columns
that have a one on every row of K is even: it is the weight of the
intersection of those rows, which lies in T. Descending inclusion on K
now shows that every nonzero column pattern occurs an even number of
times. Pair identical nonzero columns, and pair the all-zero columns
with one another as far as possible. Undoing the translation, S is
contained in a relation specifying equality or disequality on each
of ⌊n/2⌋ disjoint coordinate pairs, plus one fixed coordinate when n
is odd. Equality in the cardinality bound holds exactly when the pairs
can each choose their bit independently and the optional extra bit is
fixed. Conversely every such relation has a width-two CNF.

Any set of small witnesses covering odd parity must consequently
have at least 2^(⌈n/2⌉−1) members. For m=⌈n/2⌉≥3 use the same
nonzero-even-column construction on m blocks, with a final one-bit
block when necessary. It meets this bound and attains optimal arity
2^(m−1)−1 at size zero. For m=1,2 the small-block answers above
apply. For general q, positive n not divisible by q, and m=⌈n/q⌉≥3,
the argument gives the interval
⌈2^(n/q−1)⌉−1 ≤ a ≤ 2^(m−1)−1. No claim of exact rounding for
q≥3 is needed for the stated theorems.

### Three blocks of unequal sizes

For every 2q<n≤3q, the optimal arity is three in the fixed-junta
model. The three-block construction uses any three nonempty blocks
of size at most q. For the converse suppose arity were two. At the
target row 00 every zero-gate candidate answers zero. On rows 10,
01,11 their signatures are 000,101,011. The only forbidden
three-label pattern for which each pair of labels occurs in at
least one of these signatures is 001. Every other contradiction is
already seen on one or two rows. At an even center a one- or two-row
contradiction would be preserved by fixing at most 2q source bits.
A flip elsewhere then gives an odd input with the same contradiction.
Thus every even center must prescribe 001 on these three rows.
Each encoded bit of these labels is constant on the even slice, so
it is constant everywhere: from an odd input flip a coordinate
outside its q-certificate. This would reject the odd inputs too.
Arity zero or one was already excluded by the row-zero argument.

An isolated 2-CNF solution bound has special algebraic structure.
For width three, the six even four-bit words of weight two already
form a 3-CNF: require every three bits to contain a one and a zero.
Thus the stronger rounded single-cell estimate 2^(n−⌈n/q⌉) valid
at width two would fail here (six exceeds four). This example
concerns witness cell cardinality; it does not determine every
minimum table length at larger widths.
