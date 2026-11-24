# Equal marginals can conceal a superpolynomial algebraic circuit-size gap

## The input and the claim

A succinct input consists of one directed graph whose arcs have labels 1
or individual variables. Its polynomial sums the product of the arc labels
over directed Hamiltonian cycles, counted once up to cyclic rotation.
Absent arcs represent zero. We allow maximum indegree and outdegree three.
The task is to estimate the size of an ordinary arithmetic circuit for
the resulting formal polynomial. The input graph is explicit. Its
coefficient list can be exponentially longer. We also consider the
Laurent-series border model of the cited lower bound.

Fix a field of characteristic zero. There is a deterministic polynomial-time
reduction from equality of two #SAT counts to the following promise problem.
On equal counts the polynomial has ordinary arithmetic size O(m²+t).
On unequal counts both its exact and its border size are
2^{Ω((log m)^{4/3})}. The parameters m and t can both grow polynomially in
the source input length, for example m=t equal to that length plus three.
This gap uses Anthropic's released Hamiltonian-cycle lower bound as an
input theorem. All remaining steps of the transfer are given below.

Both cases have exactly the same support, the vertices of a product of
simplices. In the hard case there is an easy comparator with the same
coefficient histogram. Summing coefficients over either value of any
one selector bit gives the same result for both polynomials, even
conditional on the entire row map and all other selector bits. Every
coefficient is a positive integer. Padding can make the ratio of the
largest coefficient to the smallest arbitrarily close to one.

## The two polynomials

Let A and B be two positive integers represented as the numbers of accepting
witnesses of Boolean circuits. Add the same two dummy accepting witnesses
to both #SAT counts. For an m by m variable matrix x write

    U = product over i of (sum over j of x[i,j]).
    H = sum over directed spanning cycles π of product over i of x[i,π(i)].

U contains once every function from the rows to the columns, including
functions with collisions. H selects (m−1)! of these row maps. Take
selector variables y[h,0], y[h,1] for 1 ≤ h ≤ t, where t ≥ 1. Write

    V = product over h of (y[h,0] + y[h,1]).
    D = product over h of (y[h,0] − y[h,1]).
    F = (A+B) U V + (A−B) H D.

On a noncycle map every coefficient is A+B. On a cycle it is 2A on
even selector parity and 2B on odd parity. These three formulas are
positive, and they agree when A=B. For a comparator replace H by

    Q = product over i of (sum over j in S[i] of x[i,j]),

where the m row-set sizes are 1, 1, 2, …, m−1. This selects (m−1)!
maps as well. The easy comparator E uses O(m²+t) arithmetic gates.
It even has a positive circuit of that size. Compute the sums for row
maps that are still inside their allowed sets and for maps that have
already failed, updating these two states once per row. For selectors
track the two parities by the same two-state recurrence, then assign
the three positive coefficients to the corresponding states.

Each map selected by H or Q contributes equally many even and odd
selector vectors. This proves equality of the full coefficient histograms.
For every individual map, summing across any one selector removes the
parity correction. As polynomials F−E=(A−B)(H−Q)D. On the subspace
y[h,0]=y[h,1] for all h, every derivative of total order below t
vanishes for F−E. More generally it suffices that a pair is set equal
and no derivative hits that block. Also F and E agree identically in y
after setting every x[i,j] to one. With a common extra 2^b dummy
witnesses, the largest/smallest coefficient ratio is at most
1+|A−B|/(min(A,B)+2^b). A b-bit free witness suffices for this branch.

## Extracting the hard polynomial

For A=B the formula is a scalar times U V. Otherwise substitute
y[h,0]=1 and y[h,1]=0 for every h. Then V=D=1 and

    H = (F restricted to these y − (A+B) U)/(A−B).

This adds O(m²) ordinary gates with field constants to any proposed small
circuit. The same operation on Laurent-series circuits preserves the
constant coefficient and the vanishing of every negative-order term.
Hence the exact and border lower bounds for H both transfer, after
subtracting O(m²) and decreasing the absolute exponent constant for all
sufficiently large m. This reasoning also works in characteristic p when
A−B is nonzero in the field. In that setting it detects congruence of
counts modulo p. Positivity and the full-support assertions concern the
integer polynomial, or its interpretation in characteristic zero.
[Released definitions and theorem statements](https://github.com/anthropics/formal-math/blob/11b6c7e3c927df2658f513b6b68ea7f8929c62c5/vp-vnp/Statement.lean)

## Constructing the succinct input without knowing either count

Guess one canonical row map and selector vector. Check row-map indices,
parity and the single-cycle condition deterministically. On a noncycle
guess whether to run verifier A or B. On an even cycle run A with one
extra free bit. On an odd cycle run B with one extra free bit. Branches
of different lengths pin their unused witness bits to zero. To emit the
monomial, deterministically compute one flag per row-column choice and
per selector value. A true flag emits its variable and other flags emit 1.
The number of accepting assignments bearing each monomial is exactly its
stated coefficient. All operations have Boolean circuit size polynomial
in the size of the source, m and t.

The weighted witness compiler included with this packet turns the
verifier into one positive directed-tour projection. It uses a
parsimonious NAND-to-exact-one encoding and a three-vertex switch that
enforces complementary choices while preserving the selected label.
The resulting simple directed graph has maximum indegree and outdegree
three. Its long tour can use polynomially many arcs labelled 1. Polynomial
degree in x,y therefore remains exactly m+t. Both original counts remain
implicit throughout construction.
[Weighted compiler](weighted-verifiers.md)

Under the structural promise that the input has the displayed coefficient
pattern, equality is also in C_=P. Pick one explicitly specified cycle
and the all-zero selector, then toggle one selector bit. The two
coefficients are #P counts of tours with specified labels and are equal
exactly in the easy case. Equality of #SAT counts is complete for C_=P
by parsimonious circuit encoding. For sufficiently large parameters this
is therefore a promise-C_=P-complete distinction. Dropping the structural
promise retains the hardness statement. The input representation differs
from both full truth-table MCSP and a dense list of arithmetic coefficients.

## What is verified

The attached program compares row maps, selector marginals, histograms,
all-ones slices and the extraction identity on finite cases. It also
constructs Boolean verifiers for both coefficient patterns and checks their
accepting counts against independent enumeration. These checks supplement
the mathematical arguments. The transfer has no claim of priority or
independent peer review.
