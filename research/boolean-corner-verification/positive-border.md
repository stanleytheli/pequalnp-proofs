# Positive affine borders on bipartite graph probabilities

Suppose a sequence of graph probabilities, multiplied by positive real scalars, converges on every Boolean input to a function \(f\ge0\) with \(f(x)\ge1\) wherever it is positive. The graph may change along the sequence. Suppose each graph is bipartite, has at most \(N\) nonisolated vertices, and each vertex receives an arbitrary affine probability mapping the \(n\)-variable Boolean cube into \([0,1]\). Its target's Boolean support can be decided by a circuit of size polynomial in \(n+N\), independently of the magnitudes or descriptions of the affine coefficients and scalars. This remains true for singular positive rescalings which diverge.

Consequently a polynomial-size family of such approximants to real directed Hamiltonian-cycle counts would imply \(\mathrm{NP}\subseteq\mathrm{P/poly}\). This is a conditional obstruction for this specific real, probability-preserving model. Algebraic border over arbitrary fields permits operations and parameters outside it. [Karp, *Reducibility Among Combinatorial Problems* (1972), directed Hamiltonian circuit](https://www2.seas.gwu.edu/~simhaweb/champalg/tsp/papers/KarpOriginal.pdf)

## A weighted vertex cover estimates each probability multiplicatively

Write \(q_v(x)=1-p_v(x)\). Cube preservation gives the exact normal form
\[
 q_v(x)=b_v+\sum_{j=1}^n a_{vj}\ell_{vj}(x),\qquad b_v,a_{vj}\ge0,
\]
where \(b_v\) is the minimum on the cube, \(a_{vj}\) is the absolute value of a coefficient, and its literal is either \(x_j\) or \(1-x_j\) according to the sign. All coefficients and minima are at most one. Let \(d_v(x)\) be the maximum of \(b_v\) and the coefficients whose literal equals one, treating an empty or all-zero collection as zero. Then \(d_v\le q_v\le(n+1)d_v\).

Set
\[
  S(x)=\max_{C\text{ vertex cover}}\prod_{v\in C} d_v(x).
\]
The following bounds hold even when some probabilities equal zero or one:
\[
 2^{-N}\,S(x)\le Q_H(p(x))\le [2(n+1)]^N S(x).
\]
For the upper bound, the absent vertices in any accepted configuration form a cover. Its probability is at most the product of their \(q_v\), and this is at most \((n+1)^N S\). There are at most \(2^N\) configurations. For the lower bound, take a maximizing cover \(C\) and also omit every vertex outside \(C\) with \(p_v<1/2\). The complement remains independent. Each original cover vertex contributes at least \(d_v\), and every remaining vertex contributes at least \(1/2\) in that single configuration.

At fixed \(n,N\), choose one approximant for which \(cQ>1/2\) on all positive inputs and \(cQ<1/[4(4(n+1))^N]\) on all zero inputs. Finiteness of the cube permits this single choice. With \(A=[2(n+1)]^N\), it follows that \(cS>1/(2A)\) on positive inputs and \(cS<1/(4A)\) on zero inputs. Choosing that much precision is needed only for existence of an advice string.

## Removing arbitrary real advice

Put \(w_v(x)=-\log d_v(x)\), with the value \(+\infty\) for zero. Each \(w_v\) is a minimum of fixed weight labels selected by literals. Maximizing the preceding product is equivalent to minimizing \(\sum_{v\in C}w_v(x)\). Comparison with the threshold \(T=\log(2Ac)\) separates the two sets strictly. A family with no positive inputs is trivially decidable. Otherwise \(S\le1\) gives \(T>0\).

There are at most \(D=1+N(n+1)\) finite labels and the threshold together. Preserve pairwise comparisons of finite labels, and preserve whether each finite sum of cover weights falls below, equals, or exceeds \(T\), for every choice of one available label per covered vertex. The resulting finite family of linear conditions in \(D\) real unknowns has integer coefficients bounded by \(N+1\). Equalities are homogeneous and strict inequalities have a positive gap. A joint rescaling replaces every strict positive gap by a gap of at least one, since the family is finite. Impose nonnegativity on weights and threshold. The resulting nonempty rational polyhedron is pointed and has a vertex; for example, minimize the sum of coordinates before taking a vertex of that compact optimal face. Cramer's rule gives one common denominator and integer numerators of bitlength \(O(D\log(D(N+1)))\). Multiplication by the denominator preserves all needed comparisons. Infinite labels can be represented by an integer greater than the threshold and all finite labels. Any cover using such a weight is above threshold.

The advice specifies this polynomial-size integer table, masks of absent labels, each input literal's polarity, the bipartite graph and its bipartition. On an input, computing the selected minimum at every vertex is polynomial-time. Minimum-weight bipartite vertex cover with nonnegative integer weights reduces to minimum cut: join the source to the left vertices with their weights, the right vertices to the sink with theirs, and give each left-to-right graph arc capacity exceeding the sum of every integer vertex weight after infinite labels have been replaced. A cut below that capacity corresponds exactly to the cover made of left vertices on the sink side and right vertices on the source side. Therefore a nonuniform polynomial-size Boolean circuit can compute the support.

## Ordered Puiseux interpretation

If the parameters and positive scale are real Puiseux germs preserving the probability interval for positive sufficiently small parameter, there is an exact tropical statement. Take weights \(w_v=\operatorname{ord}(1-p_v)\) and use \(+\infty\) for the zero germ. The order of the no-edge probability equals the minimum cover weight. All configuration terms are nonnegative with nonnegative orders. Given a finite-weight minimizing cover, include every vertex for which \(\operatorname{ord}p_v>0\), at zero additional \(w_v\) cost, so its complementary independent assignment attains exactly that order. If every cover has infinite weight then every legal configuration has identically zero probability. Positivity excludes cancellation. The real approximation argument above also covers arbitrary nonanalytic sequences of affine parameters.
