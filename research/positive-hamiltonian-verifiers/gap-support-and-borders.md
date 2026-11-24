# Gap squares, positive Hamiltonian-cycle circuits, and a conditional obstruction to positive VNP completeness

For an n-bit string b, present the 2n graph-data bits in n pairs, with only
the entry (i,bᵢ) equal to one in each pair. Call this the one-hot input for b.
Consider polynomial-size arithmetic circuits with nonnegative real constants,
addition, multiplication, and explicitly wired directed Hamiltonian-cycle
oracle gates. Size charges matrix slots, wires and gates. The languages for
which the output is positive at precisely the accepting one-hot inputs are
exactly NP/poly. The same characterization holds for pointwise limits of
the outputs of such circuits at a fixed polynomial size bound, assuming
finite limits on the one-hot inputs. No bound on other inputs or intermediate
values is required. Constants are arbitrary positive reals and may diverge
along the limiting sequence.

This gives a necessary condition for the first part of Grochow's Question
5.5. If every nonnegative real VNP polynomial is a monotone projection of
the Hamiltonian-cycle polynomial, then coC_=P is contained in NP/poly
and P^#P is contained in Σ₂^p/poly. The same implication holds even if
one allows general positive Hamiltonian-cycle circuits, or their pointwise
limits, and requires only the correct zero-versus-positive behavior on the
one-hot inputs of the specific family below. The implication is conditional.
It gives neither a separation of these Boolean classes nor an unconditional
answer to Question 5.5. The second part of that question allows an arbitrary
positive VNP-complete family whose support could itself be harder to verify.

## Exact support

A positive sum can be certified by a positive child and a positive product
by positive children in every slot. At a Hamiltonian gate guess a single
spanning directed cycle and certify its entries. Use one certificate per
physical gate. The verifier may guess a set of positive gates and check
only the requested witnesses at those gates. Induction down the DAG proves
soundness. A finite positive circuit uses only polynomial advice to
describe its wiring and which constants are zero. No real constant has
to be represented exactly. This gives the NP/poly upper bound.

Conversely any NP/poly predicate reduces in nonuniform polynomial time
to existence of a directed Hamiltonian cycle. The Boolean computation of
its adjacency matrix has polynomial size. On one-hot inputs, both a bit and
its complement are available. Track both polarities of each Boolean wire:
AND and OR on either rail use multiplication and addition in their truth
semantics, and negation exchanges rails. Arithmetic rail values may exceed
one, but their positivity has exactly the required semantics. One positive
Hamiltonian gate at the output recognizes the language. This converse
asserts recognition, with no quantitative claim on nonzero values.

## Why a fixed-size positive border still has a short Boolean certificate

Fix n. By passing to a subsequence fix the circuit topology and zero
pattern among constants. Treat the remaining scalar inputs c₁,…,c_d as
positive parameters. A parse makes one choice at addition, takes all
slots of a product, and chooses a single directed tour at a Hamiltonian
gate before recursively expanding the chosen slots. Reusing a child
contributes separate occurrences. A parse which can survive on any
one-hot input has weight c^α there, where α records the multiplicities
of the scalar inputs. Its variable leaves specify which inputs permit it.
Discard parses inconsistent with every one-hot input. Each remaining
weight is bounded along the sequence by the value at some permitting
input, because every parse contributes nonnegatively there. For fixed n
there are finitely many parses. Pass to a subsequence on which every
remaining weight converges. On an accepting input at least one permitted
parse has positive limit, and on a rejecting input every permitted parse
has limit zero.

There is a single short integer objective exposing exactly the exponent
vectors with positive limiting weight among these consistent parses.
If all weights tend to zero the language slice is empty. Otherwise choose
a surviving α₀ and let D be the real span of the differences α−α₀ for
the other survivors. For L=log c, all scalar products L·(α−α₀) on a
basis of D are bounded, hence the orthogonal projection of L to D is
bounded. Subtract that projection from L. The new vector has equal
scores on all survivors, and its score gap at each dying vector relative
to α₀ tends to minus infinity. At some finite index the gaps for all
dying vectors are at most −1. The case of no dying vectors allows the
zero objective.

The resulting linear equalities and inequalities have integer entries.
For an explicit circuit of size s all coordinates of α are at most
2^O(s). Indeed, the largest parse is bounded by the product of (1+arity)
along a DAG path, and the sum of explicit arities along any such path
is O(s). There are at most s scalar parameters. Adjoin a variable
bounding the absolute values of all objective entries and minimize it.
There is a vertex optimum because the optimum slice is nonempty and
bounded. Cramer's rule on its active independent constraints, followed
by multiplying out their common determinant, gives an integer objective
w and threshold T=w·α₀, with polynomially many bits. Its size is
independent of the number of consistent parses. The topology, zero
pattern, w and T can all be taken as polynomial advice.

On a given mask b, a nondeterministic verifier guesses a single local
choice at each gate it uses. It checks the selected tours, that every
selected variable input is permitted, and computes the resulting optimality
certificate by adding integer weights down the DAG with the multiplicities
of selected slots. A constant input has its w-coordinate as score, and a
permitted variable has score zero. The root must have score T. No need
to check that the advice is optimal: it is fixed to a correct exposing
objective for the size-n slice. If a permitted parse of score T exists,
one deterministic choice per visited physical gate suffices. In fact,
maximizing the additive score among permitted parses is a bottom-up
recurrence; replacing every occurrence of a shared gate by a maximizing
local parse preserves admissibility. Every permitted parse is consistent
and has score at most T, so this recurrence attains T precisely at an
accepting input. Scores have polynomial bit length from the same bound
on parse multiplicities. This proves the upper bound for the limit model.

## A constant-free set-multilinear test family

Let g be an integer GapP function. Form the homogeneous, set-multilinear
polynomial with 2n variables

    F_n(X) = Σ_{b∈{0,1}ⁿ} g(b)² ∏_{i=1}ⁿ X_{i,bᵢ}.

Its coefficients are nonnegative integers, and this is a VNP family over
the reals using only the constants 0, 1 and −1. Write g(b) as a signed
sum over polynomial-size Boolean witnesses with polynomial-time
computable contributions in {−1,0,1}. Arithmetize two independent
witnesses and multiply their signs. To keep the formal degree polynomial
even for a deep Boolean computation, introduce Boolean bits for all
gate outputs, multiply constant-degree gate-consistency indicators, and
sum out those bits. Their consistent evaluations are unique. Also use
∏ᵢ((1−bᵢ)X_{i,0}+bᵢX_{i,1}) to choose the data monomial. The product
has polynomial degree and size before the outer VNP sum. On the one-hot
input for b exactly one summand in the displayed polynomial can survive,
and its value is g(b)².

Thus a positive Hamiltonian representation even of these supports would
put every nonzero-GapP predicate in NP/poly. One can use a single language
comparing the numbers of accepting assignments of two Boolean circuits:
inequality of the two counts is complete for coC_=P. If this containment
holds, equality of any #P value to a claimed binary number is in
coNP/poly, since their difference is a GapP function. To simulate a
deterministic polynomial-time machine with a #P oracle, existentially
guess its answers and verify the resulting adaptive transcript. A
universal check covers each claimed equality using the coNP/poly
certifier with advice for all polynomially many possible query lengths.
The answers have polynomial bit length. This gives P^#P ⊆ Σ₂^p/poly
and hence PH ⊆ Σ₂^p/poly by Toda's theorem. These are nonuniform
conclusions. No uniform hierarchy collapse is asserted.

The exact support certificate also works with any oracle whose positive
local alternatives have polynomial-size verifiable descriptions. The
border argument additionally needs each chosen alternative to be a
product of an explicitly bounded list of slots. Both hold for ordinary
permanent gates along with Hamiltonian gates.

[Grochow, Question 5.5](https://toc.cs.uchicago.edu/articles/v013a018/v013a018.pdf).
[Fenner, Fortnow and Kurtz, Gap-definable counting classes](https://www.cse.sc.edu/~fenner/papers/gaps.pdf).
[Toda, PP is as hard as the polynomial-time hierarchy](https://doi.org/10.1137/0220053).

## A matching characterization on the signed side

Assume a constant-free VNP verifier has polynomial *formal* degree when
every input, including ±1 and zero, starts with degree one; addition takes
the maximum and multiplication adds the two degrees. Under this convention,
the one-hot support languages of nonnegative-coefficient such VNP families
are exactly coC_=P/poly. The characterization still holds with homogeneous
set-multilinear outputs. The formal-degree hypothesis on the verifier
prevents repeated squaring of a scalar from generating integers with
exponential bit length.

For the upper bound, use the verifier circuit as advice, guess its Boolean
witness, and expand its signed arithmetic circuit into parse trees.
Each such tree has at most the formal degree many leaves, and at most
(s+1) times that many occurrences for verifier size s, because a branch
has depth at most s. A nondeterministic polynomial computation encodes
the ordered tree canonically: visit slots in a fixed order, make one
binary choice at a sum or signed difference, take both slots at an
ordinary product, and give any padding a unique encoding. Trees with a
zero leaf contribute zero. The difference of the numbers of positive
and negative trees gives the output on the one-hot input. This difference
is GapP/poly, and nonnegative coefficients ensure its positivity predicate
equals its nonzero predicate. For the reverse direction, apply the gap-square
construction to a GapP/poly witness relation. Its nonuniform advice is
hardwired into the Boolean gate-consistency checks and both the actual
and formal verifier degrees are polynomial.

In particular, on this concrete family of supports, equality of the signed
and positive Hamiltonian models is equivalent to coC_=P/poly = NP/poly.
NP/poly lies in coC_=P/poly by taking the number of accepting witnesses.
This equivalence concerns one-hot support languages; it says nothing
about reproducing the positive values or polynomial coefficients.

## Replacing Hamiltonian gates by bipartite matching gates

For permanent gates the corresponding positive-border support languages are
exactly P/poly on one-hot inputs. Use the same polynomial-bit exposing
objective. At each circuit node compute the best score among parses
permitted by the given input, or mark it unavailable. Addition takes the
maximum and multiplication adds the child scores when every slot is
available. At a permanent gate, solve the maximum-weight bipartite
perfect matching problem with the unavailable slots forbidden and the
computed integer scores on all other slots. Polynomial-time assignment
algorithms work for signed integer weights and also detect infeasibility.
All score bit lengths and the number of oracle slots are polynomial.
This gives a deterministic Boolean circuit with polynomial advice.
Conversely a dual-rail translation of an arbitrary Boolean circuit on
one-hot data already gives the P/poly lower inclusion, with no oracle
gates required. The deterministic and nondeterministic upper bounds
also hold on Boolean promises other than one-hot whenever the input
leaf permissions are efficiently decidable and the finite limits exist
on all promised inputs. The converse inclusions above use the one-hot
representation to supply both data polarities.

Thus the one-hot expressive classes for these three models are P/poly for
positive permanent borders, NP/poly for positive Hamiltonian borders, and
coC_=P/poly for nonnegative outputs of constant-free bounded-formal-degree
signed VNP verifiers. These identities give conditional distinctions
between models, independently of whether the three Boolean classes differ.
