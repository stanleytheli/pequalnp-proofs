# Certifying small arithmetic complexity with hidden coefficient changes

Fix m ≥ 3 and t ≥ 1. Use n = m²+ℓ+t variables: the m² entries x of
a square matrix, ℓ tag variables z and t selector variables w. All
polynomials below are multilinear. A coefficient query specifies any
squarefree exponent vector. Queries outside this table return zero.
An interactive verifier can have unlimited computation and communicate
arbitrarily with a prover. Its only input-dependent observations are
the queried coefficient values and the side information specified below.

Write L(v)=∏(1+v_i). Let H be the directed Hamiltonian-cycle polynomial
on x, and Q the product of m row sums from the companion note, selecting
exactly (m−1)! row maps. Choose the row order with the first row restricted
to its diagonal column. Then an explicit m-cycle supplies a monomial of
H outside Q. Define

    D(w) = ∏(1−w_i),
    E    = 2 L(x)L(z)L(w) + L(z) Q(x) D(w),
    F_σ  = E + z^σ (H(x)−Q(x)) D(w),       σ ∈ {0,1}^ℓ.

The public easy input E and every hard F_σ have full multilinear
support. Every coefficient belongs to {1,2,3}. For each tag, including
the hidden one, they have exactly the same coefficient histogram, even
separately at each fixed selector vector. Marginalizing over any one
selector yields exactly the easy table for every setting of all other
coordinates. Every derivative of total order below t at the all-ones
point is the same. Indeed D vanishes to order t there. These invariants
can all be supplied to the verifier at no cost.

E has arithmetic circuit size O(n). Each hard input has both exact and
Laurent-border size ≥2^{Ω((log m)^{4/3})}−O(n) in characteristic zero:
substitute z=1,w=0, subtract E at the same inputs, and add Q. This
recovers H because the hidden tag monomial evaluates to one. The constants
needed in the easy expression are permitted arbitrary field constants.
If m grows as a positive power of n, the lower bound is superpolynomial
in n. The coefficient oracles themselves are uniformly computable in
polynomial time given σ and the easy/hard flag: recognize a row-map
exponent, then test a single directed cycle or the row-wise choices of Q.
[Hamiltonian-cycle lower bound](https://github.com/anthropics/formal-math/blob/11b6c7e3c927df2658f513b6b68ea7f8929c62c5/vp-vnp/Statement.lean)

## Exact query cost up to a constant, even with interaction

Let c>s be the completeness and soundness probabilities for certifying
that the input is easy. Fix an honest prover strategy on E of acceptance
probability at least c. On F_σ a dishonest prover can simulate that same
strategy. Couple all random bits. Until the verifier queries a coefficient
in the tag slice σ, every answer and message is identical. Thus, for every
σ, it must hit that tag on its E run with probability at least c−s.
Summing these inequalities shows an expected cost of at least
(c−s)2^ℓ individual coefficient queries **on the one public easy input**.
The argument allows adaptive algorithms, arbitrary witnesses, many rounds,
and public or private randomness.

A deterministic verifier checks exactly one known cycle outside Q at
selector exponent zero for each tag. E gives 2 everywhere and a hard
input gives 3 at precisely its hidden tag. Thus 2^ℓ probes suffice,
and a certificate of hardness needs just the tag and one probe. The
asymmetry concerns this explicit promise family and coefficient-oracle
access. Evaluating the polynomial at an arbitrary field vector is a
different operation.

For every fixed 0<δ<1 one may reserve O(n^δ) variables for the hard
block and selectors, with m polynomial in n. This gives
2^{n−O(n^δ)} necessary queries. Alternatively take
log₂ m comparable to (log₂ n)^{4/5}, reserve m²+t=n^{o(1)}
variables and put the rest in the tag. Then the hard size is
2^{Ω((log n)^{16/15})}, still superpolynomial, while the verifier needs
2^{n−n^{o(1)}} probes. One can also allocate Θ(n) selector variables
to preserve linearly many orders of derivatives with exponentially
many tag slices remaining.

The verifier only sees an entry oracle. Giving it an explicit Boolean
circuit for the coefficients would disclose additional information.
The hard and easy tables differ in an exponentially small fraction of
entries. This result addresses exact certification under the promise.

## A symmetric version with two coefficient values

Take n data variables and t≥1 selector variables. Pad H on m² of the
data variables by multiplying it by a single squarefree monomial on
k−m fresh data variables, where k=⌊n/2⌋, k≥m, and m²+k−m≤n.
Permute all n data variables with a hidden permutation π and write Pπ
for the result. It consists of h=(m−1)! distinct monomials of degree k.
For an integer B≥2 use the public easy input and planted hard inputs

    E = B L(x)L(w) + L(x)D(w),
    Fπ = E − 2Pπ(x)D(w).

For each individual data exponent the selector coefficients have the
same histogram: half B−1 and half B+1. On the planted support their
parities merely exchange. Every proper selector marginal conditional
on every fixed data exponent and the remaining selectors agrees exactly,
and the derivatives through order t−1 at all ones still agree. On all
nonnegative real inputs, Pπ(x)≤L(x) and |D(w)|≤L(w), so
|Fπ/E−1|≤2/(B−1). Thus one can also make all nonnegative evaluations
arbitrarily close in relative terms. Setting w=0, subtracting E, and
scaling by −1/2 gives Pπ. Undoing the permutation and setting the
padding variables to one gives H. This transfers the same characteristic
zero exact and border lower bounds, with O(n+t) additional gates.

Under a uniform hidden permutation any queried data exponent of weight
k hits the planted support with probability h/binomial(n,k), by
transitivity. All other exponents miss. On the public E transcript,
the random choices of the verifier and prover are independent of π.
The union bound, including for a random number of queries by summing
over the queries made on that transcript, gives

    expected probes on E ≥ (completeness − soundness) binomial(n,k)/h.

The proof applies unchanged with the identical side information above.
Uniform random probes on the k-layer at one fixed selector exponent
give a matching bounded-error upper bound up to a constant. A single
planted monomial certifies hardness against the easy input. Precise
numerical estimates concern the input oracle model. They do not preclude
a fast coefficient algorithm when the hidden permutation is supplied.

## Quantum queries and interactive proofs

In the usual reversible coefficient-query model, the corresponding
bounded-error quantum query costs on these promises are Θ(√(2^ℓ))
for hidden tags and Θ(√(binomial(n,k)/h)) for the symmetric version.
The verifier can use arbitrary computation and an untrusted interactive
quantum prover. Honest verification of the easy input fixes a strategy
and an initial state. A dishonest prover on a hard input can run that
same strategy. Purify the joint system, deferring measurements; all
between-query transformations in the two runs are now the same. The
prover has no trusted independent input oracle.

For a hidden hard input j, let p_{i,j} be the squared query magnitude
on positions where the two input oracles differ, just before query i of
the easy run. Two reversible oracles with identical values outside this
set differ in norm on that state by at most 2√p_{i,j}. Telescoping the
two unitary evolutions and using norm preservation bounds final state
distance by 2∑_i√p_{i,j}. A completeness–soundness probability gap γ
requires distance at least γ. Under a uniform hidden input the expected
p_{i,j} is ≤ρ, with ρ=2^(−ℓ) for tags and ρ=h/binomial(n,k) for
the symmetric construction. Concavity gives γ≤2q√ρ, for worst-case
q queries. This is the quantum search hybrid argument applied to the
actual coefficient oracles; entangled auxiliary registers do not change
the query magnitude inequality. [Bennett, Bernstein, Brassard and Vazirani](https://arxiv.org/abs/quant-ph/9701001)

The matching upper bounds use quantum search for a differing
coefficient on the same subdomain used by the classical algorithm.
The marked fraction is exactly ρ in the hard case and zero in the easy
case. This needs no prover. In the opposite direction a classical
hardness witness still needs just one deterministic probe.
[Boyer, Brassard, Høyer and Tapp](https://arxiv.org/abs/quant-ph/9605034)
