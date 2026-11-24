# Positive Hamiltonian projections for counting witnesses

Let a polynomial-size Boolean circuit accept some of its bit assignments.
On an accepting assignment b, emit a monomial by multiplying independently
specified labels for the two values of each designated bit. Each label is
an input variable, a nonnegative scalar, or 1. The sum over accepting
assignments is a monotone projection of a directed Hamiltonian-cycle
polynomial of polynomial order. The following elementary construction
preserves weight and has maximum indegree and outdegree at most three.
It also gives exact counting completeness with discrete constants.

## A parsimonious Boolean encoding

Use NAND gates. Introduce a pair of positive variables for the two values
of each Boolean wire and require exactly one in each pair. A constraint of
arity two can be padded with a fixed false variable. One set of all-positive
ternary constraints pins constants uniquely: require exactly one in each
of (a,b,c), (a,b,d), (c,d,e), (e,a,c). The equations give c=d=0,
e=1, a=0, b=1. These names are fresh. Pin the accepted output by setting
its false wire to zero with the known true and false constants.

For a NAND gate on A,B add four new bit selectors t00,t01,t10,t11.
Require exactly one in each of the following groups, where A₀,A₁ are
the two flags for A and likewise for B and the output Z:

    (A₀,t10,t11), (A₁,t00,t01),
    (B₀,t01,t11), (B₁,t00,t10), (Z₁,t11,false).

Exactly one selector is chosen; its indices give the inputs. The last
constraint says Z₁=1−t11 as required. Thus all auxiliary values are
unique given the original inputs. Each bit appears in a clause. If
desired, output a bit-dependent factor by marking the true branch of its
wire-value flag with that factor. Distinct designated flags can emit many
copies of a data variable. The parsed truth table and all auxiliary flag
values were exhaustively checked for a NAND gate.

## A three-vertex directed XOR with persistent marked arcs

Start from a directed ring of at least three vertices. Between successive
vertices put one layer per Boolean variable, with two parallel choices,
and one layer per positive exact-one clause, with one choice per occurrence.
Extra singleton layers pad tiny cases. Every spanning directed cycle takes
exactly one option in each layer and has a unique traversal up to rotation.

For two distinct physical arcs a→b and c→d, remove both. Introduce fresh
p,q,r with both directions on p—q—r, and attach a→p, r→b, c→r and p→d.
In any spanning cycle q has two distinct cycle neighbors. Its only possible
neighbors are p and r, so the cycle traverses the entire private path in
one direction. In the forward direction it enters at a and leaves for b.
In reverse it enters at c and leaves for d. Contraction gives exactly one
selected old arc. Conversely any old spanning cycle using exactly one has
a unique lift. It keeps all external vertices in exactly the same cyclic
order. Transfer each old arc label to its corresponding entry connector
and label other new arcs 1. The two entry connectors remain exact tests
for selection of their old arcs. Therefore a persistent mark can be
replaced again by the same construction. Reverse the order of insertions
to contract a full sequence unambiguously.

For every clause option, place an XOR between its marked arc and the
current false-option mark of its variable. The selected clause options are
exactly the true incidences; because a clause admits just one option,
every accepted assignment has exactly one cycle and vice versa. All
weights are preserved. Every clause option is replaced, and every variable
is used in a clause, so each original parallel bundle retains at most one
of its original arcs. Every replacement introduces fresh internal vertices
and creates no parallel arcs. The final graph is simple. The replacement
preserves in- and outdegree at existing vertices, and new vertices have
in- and outdegree at most two. Its adjacency matrix is a monotone projection
with one label per entry.

The standalone generator implements the XOR with persistent edge IDs and
the exact-one layer construction. The general graph construction here does
not require planarity. Parsimonious directed-Hamiltonian-cycle reductions
from positive 1-in-3 SAT with more restrictive planar cubic hosts already
appear in the literature; Theorem 3.1 and its variable gadgets are
particularly relevant. The purpose here is an explicit weighted compiler
and its consequences for positive borders.
[Planar directed Hamiltonicity, Theorem 3.1](https://www.jstage.jst.go.jp/article/ipsjjip/28/0/28_987/_pdf).
[Maksimenko on faces realizing SAT polytopes](https://www.mathnet.ru/eng/da655).

## Coefficient characterization

Consider families of nonnegative-integer polynomials with polynomially
many variables and polynomial degree, using a canonical padded binary
encoding of exponent vectors. Their coefficients are #P/poly functions
if and only if the families are monotone projections of polynomial-order
directed Hamiltonian cycles using zero, one, and data variables. Allowing
additional nonnegative-integer constants with polynomial bit length gives
the same class. A nondeterministic verifier guesses a tour canonically by
starting at a specified vertex, counts data labels, rejects a mismatched
exponent, and for an arc of constant weight c makes c accepting choices
with unique binary encodings. A zero-weight arc is unusable.

Conversely, given a #P/poly verifier for a coefficient, guess one canonical
exponent vector α and one of its accepting witnesses. Reject out-of-range
encodings, and deterministically calculate the flags [αᵢ≥j] for 1≤j≤D,
where D is the polynomial degree bound. Give each such flag true label Xᵢ.
The weighted compiler sums exactly the intended monomial with exactly its
coefficient. The same reasoning realizes a scalar times the polynomial by
a forced arc. In particular with polynomial-bit nonnegative rational
constants the characterization is that there is a per-length positive
integer denominator of polynomial bit length for which all scaled
coefficients are #P/poly. In the forward direction, multiply once by the
product of all physical arc denominators. A guessed tour can realize its
scaled coefficient by multiplying a selected arc's numerator and each
unselected arc's denominator. The converse uses one reciprocal scalar.

For constant-free signed VNP verifiers of polynomial formal degree
(counting constants as degree one), the analogous nonnegative-integer
coefficient class is the everywhere-nonnegative part of GapP/poly.
Guess a VNP witness and a canonically encoded signed parse tree of
polynomial size, check the exponent, and take the difference of counts.
Conversely the existential signed-tableau construction for a GapP
coefficient emits its exponent in unary threshold flags. In particular
the integer-normalized restriction of Grochow's first Question 5.5,
on this bounded verifier class and with integer projection constants of
polynomial bit length, is equivalent to every everywhere-nonnegative
GapP/poly function being #P/poly. To see the reverse implication for
functions, encode an arbitrary such g as the coefficient of the
one-hot monomial for b in a set-multilinear family. This leaves the
unrestricted real-constant question open. Its necessary condition on
support is described in the companion note.
