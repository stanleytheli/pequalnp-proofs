# Counting hardness for minimizing a positive bilinear form

For k ≥ 2 take the k by k matrix M with off-diagonal coefficient A and
diagonal coefficient B, where A,B ≥ 2 are positive #P counts, and the
polynomial f(x,y)=xᵀMy. A positive bounded-degree tour projection for
this polynomial is generated without evaluating the counts: guess one
row i and column j, run the verifier for B when i=j and for A otherwise,
and emit x_i y_j. Each accepted witness yields exactly one labelled tour
by the included weighted compiler.

Over characteristic zero, if A=B, rank M=1. Otherwise rank M=k: on the
sum-zero subspace the eigenvalue is B−A and on the all-ones vector it
is B+(k−1)A. The minimum number of nonscalar multiplications in a
division-free circuit with free affine-linear operations is precisely
rank M, also for Laurent border complexity. The upper bound is a rank
decomposition. For the lower bound, differentiate at the zero input.
A product gate contributes a new Hessian term uvᵀ+vuᵀ for its input
gradients u,v, in addition to scalar multiples of earlier Hessians.
Its new term has rank at most two. The root Hessian is a linear
combination of at most one such term per nonscalar product. Its two
off-diagonal blocks are M and Mᵀ, hence its rank is 2 rank M. Over the
Laurent field the same argument bounds all ranks of the approximate
Hessian. All oversized minors vanish identically. The output has
power-series coefficients, so specialization to order zero preserves
the vanishing minors and gives the same rank bound at the target.

## A gap in total monotone gate count

Allow free nonnegative scalar weights and binary addition and
multiplication, with individual variables and constants as leaves.
Count internal gates. For A=B the exact minimum is 2k−1: add each
side separately and multiply the sums, absorbing the scalar into a
weight. Dependence on 2k variables requires at least 2k−1 binary gates.
For A≠B every such circuit needs at least 3k−2 gates. This also lower
bounds ordinary positive circuits with charged scalar operations. In
that convention equal coefficients can be handled with at most 2k gates.

Discard dead and zero gates, absorb scalar-only operations into edge
weights, and bypass zero input edges. Every remaining useful gate is
bihomogeneous. Fix one parse using it in a particular location. Every
monomial of the gate survives with the same fixed outer context by
nonnegativity, including when other occurrences of this gate are in
the parse tree. All must give the root bidegree (1,1). Useful nonscalar
gates therefore have type x-linear, y-linear, or bilinear.

Let p and q count additions of the two linear types. Merge two groups
of variables whenever a new linear addition first combines their supports.
At the end there are c≥k−p x-groups and d≥k−q y-groups. Each linear
factor lies inside one group. Let h be the number of products taking
one x-linear and one y-linear factor. Each is rank one and all bilinear
expressions above them are linear combinations. Hence h≥rank M=k.
Every one of the cd pairs of groups contains a positive matrix entry,
and a given product covers only one pair. Thus h≥cd≥c+d−1. At least
h−1 binary bilinear additions are needed to connect these h products
to the output, since the trimmed downstream addition network depends
on every product as a syntactic input. Consequently

    size ≥ p+q+2h−1 ≥ 2k−c−d+2h−1 ≥ 3k−2.

The same bound holds for coefficientwise limits of fixed-size weighted
nonnegative circuits over the reals. Fix a topology along a subsequence,
prune identically zero gates and normalize each live polynomial by its
positive value at all ones. A product becomes the product of the
normalized children, and a sum becomes a convex combination of them.
These edge weights have simultaneous finite subsequential limits.
The root normalization converges to the target's value at all ones,
since a fixed-size circuit has bounded degree. The limit circuit of
the same size computes the target exactly. This argument also applies
to positive real-parameter Laurent families approaching a finite target.

The count-equality reduction makes these promise distinctions C_=P-hard.
Under the stated coefficient pattern they belong to C_=P: compare the
numbers of tours for one diagonal and one off-diagonal monomial. There
is no invocation of the Hamiltonian-cycle arithmetic lower bound here.
The rank and gate argument is elementary and independent of that paper.
[Nisan and Wigderson on bilinear circuit complexity](https://www.math.ias.edu/~avi/PUBLICATIONS/MYPAPERS/NW95/proc.pdf)
