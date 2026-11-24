# From signal reuse to arithmetization and equivalence testing

For a Boolean circuit over arbitrary binary truth tables, b is the
number of distinct primary variables or gate outputs used in two or
more operand slots of its trimmed output cone. Unfolding repeated
signals into separate occurrences restores a formula but duplicates
the corresponding data. Conditioning once on each shared Boolean
value avoids this duplication.

Delete the outgoing uses of the b shared signals, retaining their
producers as separate roots. For each of the 2^b guessed bit vectors
turn each deleted use into its guessed bit. Every remaining component
is a tree; all the data leaves in the whole forest are pairwise distinct.
For each shared producer require its tree output to equal the guessed
bit. Also require the original output tree to be true. Multiply these
b+1 Boolean indicators and sum over the guesses. On every Boolean
input exactly its actual shared-wire values satisfy all consistency
requirements, by induction in the original topological order.

This identity also constructs the **unique multilinear extension**
over every field. A binary truth table with values h(i,j) takes
independent child interpolants u,v to

    ∑_{i,j in {0,1}} h(i,j) u^i(1−u)^(1−i) v^j(1−v)^(1−j).

Child supports are disjoint, as are all component supports, so no
multilinearization operation is needed after multiplication.
Complements use 1−u. The final result is multilinear and agrees
on the Boolean cube, proving uniqueness. Construction time and size
are O(2^b(s+n)) for s gates and n inputs. If only circuit size
matters, simplify constant subtrees and compose unary Boolean maps
after guessing. At most O(n+b+1) gates per guess remain even when
s is arbitrarily large; a tree with d distinct live data leaves needs
at most d−1 genuinely binary gates, with unary literals absorbed.
Thus b≥log₂(L/O(n+b+1)) when the extension has arithmetic size L.

An immediate decision algorithm tests equivalence of two supplied
circuits in randomized O((2^b+2^{b'})(s+s'+n) poly(log n)) bit time
using a prime field of polynomial size and one random field point,
up to the time to obtain that field. If the Boolean functions differ,
their multilinear extensions differ over every characteristic because
they differ at a Boolean point. Total degree is at most n, so a field
of size at least 3n gives one-sided error at most 1/3. A prime can
also be found by elementary deterministic search with polynomial
overhead. The test never declares equal functions different.

The earlier explicit graph family with a hard multilinear extension
now forces Ω((log n)^{4/3}) *distinct* shared signals in every binary
Boolean circuit by Anthropic's arithmetic lower bound and the
specialization to Hamiltonian cycles. This conclusion allows arbitrarily
large Boolean circuits. For expanders a direct argument in the
Boolean gap note proves the stronger Ω(n) bound by communication.
The usefulness of the arithmetization criterion is its application
to other families for which only an arithmetic lower bound is known.
[Explicit graph specialization](https://github.com/stanleytheli/pequalnp-proofs/tree/87ceac00554a50a9c7d5967ef582db41766846f6/research/read-twice-multilinear-circuits)

For a common binary layout of the component trees, each conditioned
product also has matrix rank at most two across each layout edge.
Inside one component, the computed Boolean value of the cut subtree
is a one-bit message; outside the component the remaining factors
are separated. Across a join of components the product has rank one.
Adding the 2^b matrices gives rank at most 2^{b+1} on each such cut
of the original truth tensor. The component layout and the location
of the cut do not depend on the guessed values. The deterministic
communication protocol in the companion note is a stronger structural
statement; a low matrix rank alone would not construct that protocol.
