# Positive Hamiltonian computations and their limits

This packet connects exact counting via Hamiltonian cycles to Boolean
verification. The results are research manuscripts with independent finite
controls. Their priority has not been established. The general theorems in
this packet are written proofs. They have received internal review;
they do not yet have complete Lean proofs or outside peer review.

| Model on one-hot Boolean inputs | Languages recognized by positive output |
| --- | --- |
| Nonnegative arithmetic circuits with bipartite permanent gates, including pointwise limits | P/poly |
| Nonnegative arithmetic circuits with directed Hamiltonian-cycle gates, including pointwise limits | NP/poly |
| Constant-free signed VNP verifiers of polynomial formal degree with nonnegative output coefficients | coC_=P/poly |

These are unconditional class characterizations. They imply no
unconditional difference between the three Boolean classes. For the
real-constant models, the upper bounds allow unbounded intermediate
values along the approximating sequence. Finite limits are required
on the specified inputs.

## Counting coefficients

A weighted three-vertex switch compiles an accepting Boolean computation
to precisely one directed Hamiltonian cycle per witness. Named arcs
carry independently selected monomial labels. It gives an elementary
positive projection for any nonnegative-integer coefficient family in
#P/poly, with a converse for projections using polynomial-bit nonnegative
integer constants. The family has polynomial degree and polynomially many
variables. The compiler and its receipt are in the checks directory.
[Weighted verification](weighted-verifiers.md)

## Consequence for Grochow's Question 5.5

For any GapP function g, one nonnegative integer coefficient in an explicit
set-multilinear VNP family equals g(b)² on each encoded input b. If every
nonnegative VNP family had a monotone Hamiltonian-cycle projection, then
coC_=P would lie in NP/poly and P^#P would lie in the second level of the
nonuniform polynomial hierarchy. Even the zero-versus-positive tests of
this particular family imply the same. The unrestricted completeness
question remains open. [Proof and model definitions](gap-support-and-borders.md)

## Positive border with exact numerical values

A fixed-size positive circuit limit on a nonnegative input domain has
a one-parameter realization with finite positive amplitudes and scalar
powers of the parameter. The exponents have polynomial bit length.
With a common input permitting every parse, polynomial-size positive
Hamiltonian-oracle circuits are closed up to polynomial overhead under
these limits. If polynomial degree bounds the number of nonconstant
occurrences, a single larger positive Hamiltonian-cycle projection
computes the limiting values even on a promise. [Monomial limits](monomial-limits.md)

## Verification

The Python programs require only the standard library. Run from the root
of the extracted packet with Python 3.9 or later.

```sh
python3 checks/check_marked.py
python3 checks/check_gap_support.py
```

The first enumerates actual weighted directed tours before and after
individual switches, compares complete exact-one graphs against an
independent truth table, and exhausts auxiliary flags for a NAND gate.
The second compares exposing-face prediction and a shared-gate dynamic
program against direct parse expansion and exact rational evaluations on
promised inputs. It separately checks the signed gap-square construction.

The border arguments use positivity. Anthropic’s signed, all-field
Laurent-border lower bound and the direct read-twice reduction from it
are separate results. [Anthropic’s release](https://github.com/anthropics/formal-math/tree/11b6c7e3c927df2658f513b6b68ea7f8929c62c5/vp-vnp).
[Direct read-twice reduction](https://github.com/stanleytheli/pequalnp-proofs/tree/87ceac00554a50a9c7d5967ef582db41766846f6/research/read-twice-multilinear-circuits).
