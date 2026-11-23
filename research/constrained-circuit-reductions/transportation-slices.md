# Permanent hardness on prescribed-margin and symmetric prescribed-diagonal slices

Let \(P_{r,s}(A)=\sum_{\sigma:[r]\hookrightarrow[s]}\prod_i A_{i,\sigma(i)}\) for \(s\ge r\). Write \(\operatorname{per}_m=P_{m,m}\). All statements concern polynomial identities over a field \(K\) of characteristic different from two, including finite fields. Affine slice coordinates mean independent coordinates on the affine solution space. An ordinary circuit uses field constants and binary arithmetic gates. A border circuit may use Laurent-series constants and must give the target as its coefficientwise constant term with zero negative coefficients.

## Rectangular matrices with prescribed margins

Fix row margins \(a\in K^r\) and column margins \(b\in K^s\) with equal totals. The northwest \((r-1)\times(s-1)\) submatrix gives affine coordinates on their common fibre. The last entry in each of the first \(r-1\) rows or \(s-1\) columns is its prescribed sum minus the preceding entries, and equality of totals makes the southeast entry consistent.

**Theorem 1.** Set \(m=r-2\ge1\). From a size-\(S\) ordinary or border circuit for \(P_{r,s}\) on this fibre, in the displayed coordinates, one obtains a circuit of the same kind for \(\operatorname{per}_m\) of size \(3S+O(1)\). The overhead is independent of \(s\) and of the margins.

**Proof.** In the free coordinates place an \(m\times m\) generic matrix \(X\) in the northwest corner. Set the southeast *free* coordinate to \(w\) and pin every remaining free input to zero. Write \(Y(w)\) for the completed matrix. Its slope in \(w\) is the signed two-by-two square \(\left(\begin{smallmatrix}1&-1\\-1&1\end{smallmatrix}\right)\) on the two last rows and columns. Put \(F(w)=P_{r,s}(Y(w))\). This polynomial has degree at most two in \(w\). To obtain degree two, the last two rows must use both last columns. Their two bijections each give coefficient one. The remaining rows see the matrix \([X\;0]\) on the remaining columns. Thus \([w^2]F=2\operatorname{per}_m(X)\) and

\[
  F(1)+F(-1)-2F(0)=4\operatorname{per}_m(X).
\]

Three input pinnings and a fixed linear combination prove the claim. Over a Laurent-series field, each pinning is independent of the deformation parameter. Its finite coefficient sums preserve regularity and reduction of the output. This proves the same implication for border circuits. ∎

**Ambient-input convention.** A circuit that reads all matrix entries can be converted to free-coordinate form by forming the missing row and column, with \(O(rs)\) gates in general. In the direct three pinnings only the \(m\times m\) core varies. Its row and column sums supply every nonconstant completion input with \(O(m^2)\) additional gates, independently of the width. This gives the same asymptotic consequence for either representation.

## Symmetric matrices with prescribed row sums and diagonal

**Theorem 2.** For any \(N\ge9\), fix vectors of row sums and diagonal entries in \(K^N\), without consistency restrictions. A size-\(S\) ordinary or border circuit for the permanent on the symmetric matrices satisfying those prescriptions gives a circuit of the same kind for \(\operatorname{per}_m\) of size \((N+S)N^{O(1)}\), with \(m=(N-4)/2\) for even \(N\) and \(m=(N-7)/2\) for odd \(N\). This applies to ambient matrix inputs and to any affine-linear coordinate chart of the fibre.

**Proof.** Reserve four vertices, and put \(q=N-4\). On the remaining \(q\) vertices form a symmetric core

\[
 B(t)=\operatorname{diag}(d_1,\ldots,d_q)+tH,\qquad
 H=\begin{pmatrix}0&X\\X^{\mathsf T}&0\end{pmatrix}.
\]

In odd dimension adjoin to \(H\) a separate three-vertex zero-diagonal block with every off-diagonal entry one. Let \(\kappa=1\) for even \(N\) and \(\kappa=2\) for odd \(N\). Every permutation supported on the displayed bipartite block induces two independently chosen bijections, one in each direction. The triangle has two directed three-cycles. Therefore \(\operatorname{per}(H)=\kappa\operatorname{per}_m(X)^2\). Homogeneity gives \([t^q]\operatorname{per}(B(t))=\operatorname{per}(H)\).

Complete \(B(t)\) symmetrically to the prescribed data. Send each core row's deficit to its edge to the first reserved vertex and set the other edges from it to reserved vertices to zero. Give the four reserved vertices their prescribed diagonals. Let \(h_i\) be their residual sums, numbered \(0,1,2,3\). Set \(x_{03}=h_3\), \(x_{13}=x_{23}=0\), and put \(g_0=h_0-h_3,\ g_1=h_1,\ g_2=h_2\). The triangle on \(0,1,2\) supplies the remainder by putting \(x_{ij}=(g_i+g_j-g_k)/2\) for the three distinct indices. This gives a completed symmetric matrix \(Y(t)\). All entries use polynomially many gates and are affine-linear in the entries of \(B(t)\).

On the four reserved vertices only, take the symmetric marker

\[
 D=\begin{pmatrix}0&C\\C&0\end{pmatrix},\qquad
 C=\begin{pmatrix}1&-1\\-1&1\end{pmatrix}.
\]

It has zero diagonal, zero row sums, and permanent \(\operatorname{per}(C)^2=4\). The entire pencil \(Y(t)+wD\) belongs to the given fibre. Its permanent has degree at most four in \(w\). Selecting four marker entries exhausts the reserved rows and columns, so

\[
[t^q][w^4]\operatorname{per}(Y(t)+wD)=4\kappa\operatorname{per}_m(X)^2.
\]

Compute both coefficients by simulating each gate over the truncated rings \(K[w]/(w^5)\) and \(K[t]/(t^{q+1})\). Truncated multiplication uses quadratically many base gates in the number of coefficients, and the two constant divisors \(4,\kappa\) are units. This argument works over finite fields without selecting any interpolation points.

To extract the unsquared permanent, perform the preceding computation with \(X\) replaced by \(I+z(X-I)\) over \(K[z]/(z^{m+1})\). Let \(g_k\) denote the coefficients of the resulting square. The polynomial \(f(z)=\operatorname{per}_m(I+z(X-I))\) has degree at most \(m\) and \(f(0)=1\). Set \(f_0=1\) and recursively form

\[
 f_k=\tfrac12\left(g_k-\sum_{i=1}^{k-1} f_i f_{k-i}\right)\qquad(1\le k\le m).
\]

Then \(\sum_{k=0}^m f_k=f(1)=\operatorname{per}_m(X)\). The additional gate factor is polynomial in \(N\). For a border circuit each of the three truncated simulations operates over \(K((\varepsilon))\). After substitution, the coefficients at its output are regular in \(\varepsilon\), because the original output coefficients are regular and all substitutions have coefficients in \(K\). Reduction modulo \(\varepsilon\) commutes with the finite arithmetic operations, coefficient extractions and square-root recursion. Intermediate gates may have poles. An arbitrary affine coordinate chart can be evaluated from the completed symmetric entries with polynomial overhead by a left inverse of its linear part. ∎

## Consequences and scope

The main theorem in Anthropic's `formal-math/vp-vnp` states that for each characteristic other than two, over every field of that characteristic, the generic \(m\times m\) permanent requires more than \(m^{c(\log_2 m)^{1/3}}\) arithmetic gates for all sufficiently large \(m\), including border circuits. Applying that bound to either reduction gives \(r^{\Omega((\log r)^{1/3})}\) in Theorem 1 or \(N^{\Omega((\log N)^{1/3})}\) in Theorem 2. Polynomial simulation costs only shrink the eventual absolute constant. The threshold may depend on characteristic. [Upstream theorem statement, pinned](https://github.com/anthropics/formal-math/blob/11b6c7e3c927df2658f513b6b68ea7f8929c62c5/vp-vnp/Statement.lean)

Over the reals, take row sums one and diagonal entries one-half throughout Theorem 2. The matrix with all off-diagonal entries \(1/(2(N-1))\) is strictly positive entrywise. Its eigenvalues are one in the all-ones direction and \((N-2)/(2(N-1))>0\) on its orthogonal complement. An open set in the real affine fibre therefore consists of positive-definite, strictly positive stochastic matrices. A polynomial agreeing with the permanent on this set agrees on the entire fibre, by the polynomial identity principle. The exact circuit lower bound holds even under this promise. This consequence concerns exact arithmetic evaluation. The fixed small dimensions and maximal constant-level affine spaces from the project remain separate questions.
