# Additive directions in rectangular permanent level spaces

**Theorem.** Let \(p\ge3\) and \(q\in\{p,p+1\}\). Write \(J\) for the all-ones \(p\times q\) matrix, and \(P(B)=\sum_f\prod_i B_{i,f(i)}\), summing over injections from the rows to the columns. Let \(L\) be any complex linear space on which \(P(J+X)=P(J)\). The subspace of \(L\) consisting of matrices \(X_{ij}=u_i+v_j\) has dimension at most \(p-2\).

Thus any proposed seven-dimensional 4×5 example and any proposed eight-dimensional 5×5 example must have at least five independent images under double centering. Here double centering subtracts the row and column means and adds the overall mean. The theorem applies to arbitrary complex spaces and does not require an invariant group or a preassigned row or column.

## Parameterization by row and column offsets

The linear term of \(P(J+X)\) is a nonzero multiple of the entry sum. Hence every \(X\in L\) has total sum zero. An additive matrix in \(L\) has unique centered offsets \(u\in H_p,\ v\in H_q\), where \(H_m=\{x\in\mathbb C^m:\sum_i x_i=0\}\). They are simply its row and column means. Let \(K\subset H_p\oplus H_q\) be the space of these offset pairs. We use the complex bilinear dot product throughout.

For arbitrary lists \(a,b\), selecting the \(k\) factors supplied by \(b\) gives
\[
 P((a_i+b_j)_{ij})=\sum_{k=0}^p k!\frac{(q-k)!}{(q-p)!}\,e_{p-k}(a)e_k(b).
\]
Pure row offsets satisfy \(P(J+(u_i)_{ij})=P(J)\prod_i(1+u_i)\). Thus \((u,0)\in K\) implies \(u=0\), by scaling the direction and looking at the univariate product. In particular projection of \(K\) to \(v\) is injective.

For pure column offsets, \(P(J+(v_j)_{ij})=p!\,e_p(\mathbf1+v)\). Its terms of degree \(k\) for \(1\le k\le p\) are nonzero multiples of \(e_k(v)\). When \(p=q\), a pure column direction must therefore be zero. When \(q=p+1\), a nonzero pure column direction \(b\) has \(e_1(b)=\cdots=e_{q-1}(b)=0\) and \(e_q(b)\ne0\). Its \(q\) coordinates are the distinct roots of \(t^q+c\) for a nonzero constant \(c\).

Suppose this last direction occurs. For any \((u,v)\in K\), differentiate \(P(J+(tb_j+s(u_i+v_j))_{ij})\) in \(s\) at zero. Each row offset \(u_i\) has the same coefficient by row symmetry, so the row terms cancel. The column contribution is
\[
 0=p!\sum_j v_j e_{p-1}(\mathbf1+t b_{\widehat j}).
\]
In the coefficient of \(t^d\), \(0\le d\le p-1=q-2\), the multiplier of \(e_d(b_{\widehat j})\) is \(\binom{q-1-d}{p-1-d}\ne0\). Removing coordinate \(j\) from the elementary polynomials and using \(e_1(b)=\cdots=e_{q-1}(b)=0\) gives \(e_d(b_{\widehat j})=(-b_j)^d\). Thus \(v\) belongs to the null space of the \(q-1\) Vandermonde rows \((b_j^d)_j\) with \(0\le d\le q-2\). This space has dimension one. Projection to the column offset is injective, so \(\dim K\le1\) in this case.

It remains to treat \(\dim K\ge2\), when the projection to \(u\) is injective. If \(\dim K\ge p-1\), equality holds and \(K\) is the graph of an injective linear map \(T:H_p\to H_q\). Its image is either all of \(H_q\) or a hyperplane in \(H_q\).

## Restriction of the power sums

The pure column degree-\(k\) contribution to the translated permanent, divided by \(P(J)\), is \(\binom pk/\binom qk\) times \(e_k(v)\), while the pure row coefficient is \(e_k(u)\). Each mixed term in degrees two and three contains one of the two centered first elementary functions and vanishes. On a centered space \(e_2(x)=-\sum_i x_i^2/2\) and \(e_3(x)=\sum_i x_i^3/3\). Therefore
\[
 \sum_j (Tu)_j^2=c\sum_i u_i^2,\qquad
 \sum_j (Tu)_j^3=d\sum_i u_i^3,\qquad
 c=-\frac{\binom q2}{\binom p2}<0,\quad
 d=-\frac{\binom q3}{\binom p3}<0.
\]
The image \(V=T(H_p)\) is nondegenerate for the dot product, since its pullback is \(c\) times the nondegenerate form on \(H_p\).

We next show that \(V\) is the complexification of a real space with positive definite real dot product. For \(q=p\) this follows from \(V=H_q\). Suppose \(q=p+1\) and take a nonzero normal \(n\in H_q\) to \(V\). Its square \(n\cdot n\) is nonzero by nondegeneracy of both \(V\) and \(H_q\). The polynomial \(F_m(x)=\sum_i x_i^3\) is harmonic on \(H_m\) for its intrinsic Euclidean Laplacian. Indeed the diagonal entries of the orthogonal projector onto \(H_m\) are all \(1-1/m\), and the ambient Hessian of \(F_m\) is \(\operatorname{diag}(6x_i)\). Its contraction on \(H_m\) is zero since \(\sum x_i=0\). This remains valid after complexification.

The conformal relation for the quadratic forms and the identity \(F_q\circ T=dF_p\) show that \(F_q|_V\) is also harmonic in the intrinsic metric of \(V\). Subtracting its trace from the trace on \(H_q\) gives \(\sum_i n_i^2 v_i=0\) for every \(v\in V\), because the missing normal contribution to the trace is \(6\sum_i n_i^2 v_i/(n\cdot n)\). Hence \(n^2\) lies in \(\operatorname{span}(\mathbf1,n)\), where \(n^2\) denotes the coordinatewise square. Its coordinates solve a single monic quadratic. There must be exactly two distinct values, as \(n\) is nonzero and centered. The relation between those two values from centering is a negative rational ratio. After a scalar normalization \(n\) is real. Equivalently \(V\) is the subspace with the sum zero separately on each of the two blocks of equal coordinates of \(n\).

## Contraction of the cubic

For a nondegenerate space, the complete metric contraction of two copies of its symmetric cubic tensor is the sum of the squares of all ordered tensor coefficients in any complex orthonormal basis. It is independent of that basis by orthogonality. For \(F_m\) restricted to \(H_m\), denote this scalar by \(C_m\). The cubic tensor is the sum of the third tensor powers of the coordinate covectors, whose mutual inner products on \(H_m\) are \(\delta_{ij}-1/m\). Consequently
\[
 C_m=\sum_{i,j}(\delta_{ij}-1/m)^3
     =\frac{(m-1)(m-2)}{m}.
\]
In particular \(C_p>0\). Write \(C_V\) for the contraction of \(F_q\) restricted to \(V\). It is nonnegative real, as both \(V\) and this cubic are defined over the reals and \(V\) has a real orthonormal basis. More explicitly it is \(C_q\) in the square case and \(C_k+C_{q-k}\) for block sizes \(k,q-k\) in the adjacent rectangular case.

Choose a square root \(\alpha\) of \(c\). The map \(T/\alpha\) is an isometry onto \(V\), so the contraction on \(H_p\) of \(F_q\circ T\) is \(c^3 C_V\). By the cubic identity it is also \(d^2 C_p\). The former is nonpositive real, while the latter is strictly positive. This excludes \(\dim K=p-1\), proving the result.

Finally, in the total-sum-zero matrix space the kernel of double centering is exactly the additive subspace. Rank-nullity gives the stated lower bounds on the images.
