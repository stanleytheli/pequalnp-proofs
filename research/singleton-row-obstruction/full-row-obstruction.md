# A row-projection obstruction for seven-dimensional complex permanent levels

Let \(J\) be the all-ones \(4\times5\) matrix and let
\[
 P(A)=\sum_{\sigma:\{1,2,3,4\}\hookrightarrow\{1,2,3,4,5\}}
              \prod_{i=1}^4 A_{i,\sigma(i)}.
\]
Suppose \(L\subset\mathbb C^{4\times5}\) is linear, \(\dim L=7\), and \(P(J+X)=120\) for all \(X\in L\). Then at least one of the following holds.

1. \(L\) contains a nonzero matrix supported on at most two rows.
2. Some row projection of \(L\) has dimension at most three.
3. Some four-dimensional row projection of \(L\) has a normal covector with a zero coordinate.

This theorem restricts the possible seven-dimensional spaces in L-gct-179. Their existence in the three cases above remains open. The proof uses the linear and quadratic permanent coefficients and the factorization of the entire permanent on pairs of sparse rows. The final finite calculation is over the complex numbers, with finite-field rank certificates and exact Gaussian-rational identities.

## The pair constraints

Suppose none of the three alternatives holds. Every row projection has dimension four, since a surjective projection would let a translated row become zero. Normalize its normal to a row covector \(w^{(i)}\) of coordinate sum one. The sum is nonzero by the same zero-row argument. The projection of \(L\) onto any two rows is injective and hence has dimension seven.

For two translated rows \(a,b\), put \(w=w^{(i)}\) and \(z=w^{(k)}\). The two normalizations \(w\cdot a=z\cdot b=1\) and one further affine constraint describe their image. Absorb its constant into either normalization. Since the normals have full support, the constraint has the form
\[
 \sum_j w_j s_j a_j=\sum_j z_j r_j b_j=t.
\]
Both \(s\) and \(r\) vary across the columns, since the individual projections have dimension four. Put \(d_j=s_j-r_j\). Each \(d_j\ne0\), or the pair could be supported in the same single column \(j\).

For columns \(j,k\) with both \(s_j\ne s_k\) and \(r_j\ne r_k\), restrict the two rows to these two columns. The first row's entries there are \((t-s_k)/(w_j(s_j-s_k))\) and \((s_j-t)/(w_k(s_j-s_k))\), and the second row has the same expressions with \(w,s\) replaced by \(z,r\). The remaining two rows are affine in \(t\) by the pair isomorphism. The full permanent factors into \(a_jb_k+a_kb_j\) and the two-row permanent of the remaining three columns. Both factors are nonzero constants. Writing \(\rho_j=w_j/z_j\), the quadratic and linear coefficients of the first factor give \(\rho_j=-\rho_k\) and \(d_j=d_k\). When \(s_j=s_k\) but \(r_j\ne r_k\), fix \(t=s_j\) and vary the first row. Constancy gives \(w_jb_j=w_kb_k\), hence \(\rho_jd_k=-\rho_kd_j\). When only the \(r\)'s agree, exchange the two rows to get \(\rho_kd_k=-\rho_jd_j\). Indices with the same \((s,r)\) have the same ratio by comparison with any different pair.

Consequently any two distinct points \((s_j,r_j)\) determine a horizontal, vertical, or slope-one line. If they are collinear, their line must have slope one, and the ratios alternate in sign at every distinct pair, so there are exactly two points. There are two groups of columns with ratios \(R,-R\). Both points have the same \(d\). The shared affine constraint on variations reduces to equality of the sums on one group, weighted by \(w\) on the first row and \(z\) on the second. The normalizations give the same equality on the complementary group. This implies
\[
 w\cdot\delta b = R^2 z\cdot\delta a .
\]
The base point also requires \(R^2\ne1\). Indeed let \(u\) and \(v\) be the two distinct values of \(s\), and \(B\) the \(-R\) group. The shared affine constraint at the all-ones pair becomes \(0=d+(v-u)(w(B)-z(B))\). From the two normalizations \(w(B)-z(B)=-(R^2-1)/(2R)\), whereas \(d\ne0\).

Otherwise a noncollinear triangle has vertices \((s,r),(s+h,r),(s,r-h)\), up to relabeling, with \(h\ne0\). No fourth point fits the three directions. On the horizontal or vertical through the first vertex the other two vertices leave only those already present. On the diagonal through the first vertex, comparison with the second leaves the candidate \((s+h,r+h)\), which the third excludes. Denote the three groups by \(A,B,C\) in that vertex order and put \(\gamma=(s-r+h)/(s-r)\). The edge identities give \(\rho_B=-\rho_A/\gamma,\ \rho_C=-\rho_A\gamma,\ \rho_B=-\rho_C\), so \(\gamma=\pm\mathrm i\). Thus the three ratios are \(R,R\gamma,-R\gamma\). The homogeneous constraint on row variations is
\[
 \sum_{j\in B}w_j\delta a_j+\sum_{j\in C}z_j\delta b_j=0.
\]
At the all-ones pair its affine counterpart gives
\[
 w(B)+z(C)=(1-\gamma)^{-1}=(1+\gamma)/2.
\]
Both choices of the order of the two opposite groups must be tested. We call a pair with three ratio values a three-group pair.

## Finite fourth-root profiles

Write the four normals as \(w^{(i)}_j=E_{ij}x_j/s_i\), where \(E_{ij}\in\{1,-1,\mathrm i,-\mathrm i\}\), \(x_j\ne0\), and \(s_i=\sum_j E_{ij}x_j\ne0\). Obtain this representation by choosing a base row and absorbing one ratio per remaining row into its scaling. Row and column phase scalings allow the first row and the first column of \(E\) to be all ones. For a two-group pair the phase ratios therefore are \(1,-1\), and its additional necessary condition is \(s_i\ne\pm s_k\).

For an oriented three-group pair with upper row \(i\) and lower row \(k\), let \(a,b,c\) be the sums of \(E_{kj}x_j\) over \(A,B,C\). If the center phase ratio is \(\phi\), then \(s_k=a+b+c\) and \(s_i=\phi(a+\gamma b-\gamma c)\). The preceding base-point equation gives the homogeneous conic
\[
 a^2-b^2+c^2-2(1+\gamma)bc=0.                                      \tag{1}
\]
Indeed substitute \(w(B)=\gamma b/(a+\gamma b-\gamma c)\) and \(z(C)=c/(a+b+c)\) and clear the nonzero denominators.

In transformed coordinates \(Z_{ij}=x_jX_{ij}/s_i\), let \(D\) be the space cut out by the following ten covectors.

- Row \(i\) gives \(\sum_j E_{ij}Z_{ij}=0\).
- A two-group pair gives \(\sum_j E_{ij} Z_{kj}-\sum_j E_{kj} Z_{ij}=0\).
- An oriented three-group pair gives \(\sum_{j\in B} E_{ij}Z_{ij}+\sum_{j\in C}E_{kj}Z_{kj}=0\).

The transformed \(L\) lies in \(D\). Every two-row projection of \(D\) has dimension seven because it contains a seven-dimensional image of \(L\) and satisfies the three independent constraints on that pair. If \(M\) is the ten-row constraint matrix, this requires \(\operatorname{rank}M-\operatorname{rank}(M|_{\text{other two rows}})=3\).

The verifier enumerates every profile by representing fourth roots by exponents modulo four. After the first row and column have been normalized, the remaining three rows are selected from the \(4^4\) possible rows starting with one. Every pair must have exactly two opposite phase values, or exactly three values. The program selects all unordered triples of compatible distinct rows, sorts the five columns, and quotients by permutations of the four rows and rephasing. Choosing any column as the first normalized column is included. This gives 656 profiles, and choosing orientations at each three-group pair gives 29,808 cases. Two-group adjacency is equality, up to common sign, of the squared phase rows, so it partitions the rows into equivalence classes. The number of three-group pairs is \(0,3,4,5,\) or \(6\).

The pair-projection test leaves 12,185 cases. Each matrix entry is a Gaussian unit or zero. Every square minor of order at most ten has absolute value at most \(10^5\) by the row-norm bound and Hadamard's inequality. The program computes both split-field ranks at \(1,000,000,009\), using the two images of \(\mathrm i\). If a Gaussian integer of this size vanishes in both embeddings, its real and imaginary parts are zero. Thus the larger of the two ranks is exactly the characteristic-zero rank.

Six surviving cases have only two-group pairs. The accompanying [two-group proof](two-group-proof.md) excludes all of them by linear algebra and the differentiated matching coefficients. Of the remaining cases, 156 have five distinct columns and exactly three three-group pairs. The dedicated curve calculation below handles those 156. The other 12,023 have the finite certificates described next.

## The quadratic rank obstruction

The degree-one permanent identity is total entry sum zero. The polarized quadratic, up to a nonzero scalar, is
\[
 G(X,Y)=\sum_{i\ne k,\ j\ne l}X_{ij}Y_{kl}.
\]
Its \(20\times20\) matrix is nonsingular. Twelve times its inverse is the integer matrix with entries \((3\delta_{ik}-1)(4\delta_{jl}-1)\). Convert the ten covectors defining \(D\) to the physical \(X\) coordinates, clearing the row-sum denominators, and append the total-sum covector. Explicitly put \(u_i=(E_{ij}x_j)_j\). Its row constraint is \(e_i\otimes u_i\). A two-group pair contributes \(-s_k e_i\otimes u_k+s_i e_k\otimes u_i\). A three-group pair contributes \(s_k e_i\otimes(u_i|_B)+s_i e_k\otimes(u_k|_C)\), where restriction extends by zero. Write the resulting \(11\times20\) matrix as \(F\). The four row covectors have degree one in \(x\), the six pair covectors degree two, and the total degree zero.

**Necessary rank bound.** If \(L\subseteq W=\ker F\) is seven-dimensional and \(G\)-isotropic, then
\[
                 \operatorname{rank}(F G^{-1}F^t)\le 6.               \tag{2}
\]
Indeed if \(r=\operatorname{rank}F\), then \(W\) has dimension \(20-r\) and the rank of \(G|_W\) is at most \(2(20-r-7)\). Its radical has dimension at least \(r-6\). The orthogonal complement \(W^\perp\) has dimension \(r\) and the same radical, \(W\cap W^\perp\). Its Gram matrix on the spanning vectors from \(F\) is \(F G^{-1}F^t\). This includes dependent constraint rows.

## Finite case certificates

If two columns of \(E\) agree, equation (1) depends only on the sum of their \(x\)-weights. Let \(n\) be the number of distinct columns and use their aggregate weights as homogeneous coordinates. Every singleton weight and every \(s_i\) must be nonzero. Every two-group pair also requires the two linear forms \(s_i+s_k,s_i-s_k\) to be nonzero. The successful finite cases have four or five distinct columns.

Take degree \(d=n+1\). Form the Macaulay matrix of all monomial multiples of (1) of degree \(d\), and let \(\mathcal E_d\) be its right kernel on the degree-\(d\) monomial coordinates. For any potential nonzero solution \(x\), its monomial evaluation row \(v_d(x)\) lies in this kernel, with the usual identification of row and column coordinates. The program recovers a Gaussian-rational basis from paired modular kernels, checks linear independence in their free columns, and verifies every row of the original integer matrix against every recovered basis vector. The modular rank supplies a lower bound on the characteristic-zero rank. The independent verified vectors provide the reverse bound. Rational reconstruction can fail to find a basis, but success only follows from these exact checks.

For a linear form \(u=\sum_j u_jx_j\), contraction sends a degree-\(d\) evaluation to \(u(x)v_{d-1}(x)\). On any monomial-dual row \(v\), its coordinate of index \(\alpha\) is \(\sum_j u_jv_{\alpha+e_j}\). The verifier may contract the entire current row space along one of the necessary nonzero forms and replace it by its exact row span. At a valid point this retains the evaluation of the next lower degree, up to a nonzero scalar. Exact row-space identities check every such replacement.

When a linear form \(\ell\) gives an injective contraction of the current row space, and all coordinate contractions lie in its image, the program computes coordinate multiplication matrices. Concretely take a row basis \(E\), \(U=\operatorname{contract}_\ell(E)\), and find \(T_j\) with \(\operatorname{contract}_{x_j}(E)=T_j U\). All identities are checked by fraction-free arithmetic, up to a recorded common nonzero scalar. If the coefficient row of a potential evaluation in \(E\) is \(v\), then \(\ell(x)\ne0\) and \(v T_j=(x_j/\ell(x))v\), with the same common scaling for every \(j\). This argument only uses common left eigenvectors, so it also applies after contractions and without a separate assertion of saturation or reducedness.

Compute the operator \(H\) given by the product of all the necessary nonzero forms. At a valid point its eigenvalue is nonzero. A nilpotent \(H\) therefore excludes the case. Otherwise the candidate row lies in the row space of \(H^m\) for each \(m\), since it is a nonzero-eigenvalue eigenvector. The verifier chooses a power at least the matrix size, takes an exact row basis of this image, and restricts the coordinate operators to it. It checks the spanning and restriction identities exactly. Common scalar factors can be removed throughout these homogeneous tests.

With five aggregate coordinates, substitute the resulting matrices in \(F G^{-1}F^t\). Choose an integer \(7\times11\) projection \(A\) and form the \(7b\times7b\) block matrix of \(A F G^{-1}F^t A^t\), where \(b\) is the size of the restricted operators. Its invertibility modulo a split prime proves its invertibility in characteristic zero. If a putative common eigenvector saw scalar rank at most six, the scalar projected matrix would have a nonzero left kernel \((c_i)_{i=1}^7\). The block row \((c_1v,\ldots,c_7v)\) would then annihilate the block matrix, a contradiction.

With four aggregates there is one doubled column. Restore its two weights as \(u+t,u-t\), doubling all singleton weights. This changes only the common normalization. The row sums are independent of \(t\). Exchanging these two columns fixes every phase constraint and preserves the Gram form, so the block Gram is a pencil in \(z=t^2\). Its coefficient of \(z\) factors through the four row coordinates on the column-difference direction and has rank at most \(4b\). Indeed the two varying columns of every constraint derivative are opposite and all other columns are zero. Consequently every projected block determinant has degree at most \(4b\). The verifier interpolates the determinants modulo a prime. A constant gcd and at least one determinant attaining the bound exclude every complex \(z\). One proof homogenizes all determinants to that upper degree. The full-degree determinant excludes infinity, and the gcd excludes a common projective zero in the special fiber. Equivalently one can work in the quotient by that determinant, whose leading coefficient is a unit at the prime.

## Three three-group pairs and five distinct columns

In this case three rows lie in one sign class, and the fourth row, \(g\), is joined to all three by three-group pairs. Orient the description of each pair so that \(g\) is lower. When the pair order is reversed, interchange \(B,C\) and keep \(\gamma\) unchanged. The two parity blocks of the columns are the same for all three pairs. Each pair's center group is one entire parity block. The other block consists of its \(B,C\) groups.

Set \(z_j=E_{gj}x_j\), and let \(A,B\) now denote the two parity-block totals of \(z\). For each of the three pairs, let \(U\) be its center total, let \(T\) be the opposite total, and write \(y\) for the difference between its two signed groups there. Equation (1) becomes
\[
                    y^2-(1-\gamma)T y+(1-\gamma)U^2-T^2=0.          \tag{3}
\]
Thus \(2y=(1-\gamma)T+v\) with \(v^2=(4-2\gamma)T^2-4(1-\gamma)U^2\). The pair \((U,\gamma)\) is one of four types. For repeated types the verifier enumerates both relative sign choices of the same radical. It takes the two signs independently for the remaining distinct types, which also covers points at which a radical vanishes. A nonzero \(s_g=A+B\) ensures that \([A:B]\) is a projective point.

For 152 cases, the five linear forms \(A,B,y_1,y_2,y_3\) recover the five original \(z_j\). The coefficient matrix has integer entries \(0,1,-1\). Its adjugate gives the original weights up to common scale, without rational denominators. Across these cases, 236 relative-sign branches have a weight, row sum or required difference identically zero by direct coefficient cancellation.

For each other branch choose seven projected covectors, mixing within each of the three degrees of rows of \(F\). If \(n_1\) degree-one and \(n_2\) degree-two covectors are used, the projected scalar Gram determinant is homogeneous of degree \(2(n_1+2n_2)\) in \(A,B\) and the radicals, all given weight one. With \(k\) distinct radical types, multiply this determinant over all \(2^k\) sign choices. The resulting norm is a Gaussian-integer polynomial in \(A,B\), homogeneous of degree at most \(2(n_1+2n_2)2^k\). Any valid point makes every projected norm vanish. The verifier uses the chart \(A=t,\ B=1-2t\). In \(\mathbb F_{65521}\) and its quadratic extension every required specialized square root exists, so scalar interpolation at one more point than the degree bound determines the entire reduced norm. At least one norm attains its degree bound and therefore excludes the omitted projective point.

On 64 branches the reduced norms have gcd one. On the other 56 the gcd is exactly \(t-1\), at which \(A+B=0\). To justify division before passing back to characteristic zero, the verifier checks that \(t-1\) divides every selected norm over \(\mathbb Z[\mathrm i]\) itself. At \(A=1,B=-1\) each radical has the exact square roots \(\pm(1+\gamma)\). Evaluating the corresponding Gaussian-integer Gram determinants shows a vanishing factor for each norm. The sign choice can depend on the projection. Dividing by \(t-1\) now gives coprime reduced norms, preserving the full-degree witness at infinity. All 56 branches are excluded.

In the last four cases the five forms are dependent. After the displayed choices of orientation there is the relation \(y_2=-y_1\), and these two forms have the same center total \(A\), opposite total \(B\), and parameter \(\gamma\). Subtracting their two equations (3) gives \(B y_1=0\). If \(y_1=0\), the corresponding two sign rows have row sums equal up to sign because each is its center phase times \(A\), and the two center phases differ by a sign. This violates the two-group condition. Otherwise \(B=0\), so normalize \(A=1\). There are only the two independent signs in \(y_1^2=-1+\gamma_1,\ y_3^2=-1+\gamma_3\). The remaining free weight is a scalar parameter \(v\), and all five original weights are affine-linear in \(v\) with row sums independent of \(v\). Hence the Gram is quadratic in \(v\), and its projected determinants have degree at most 14. All these square roots split at 65521. In every residual sign case the verifier obtains coprime projected determinants with a full-degree witness. The same projective argument excludes every complex value of \(v\).

The six sign cases, the 12,023 finite certificates and the 156 curve cases exhaust the exact pair-projection list. This proves the stated obstruction.

## Reproducing the calculation

Run the [standalone verifier](verify_full_rows.py) with Python 3.10 or newer and an existing NumPy installation. It generates every profile, orientation, polynomial and projection from the stated data. It reads no input certificates and makes no network requests.

```sh
OPENBLAS_NUM_THREADS=1 python3 verify_full_rows.py
```

The options `--part profiles`, `--part curves`, and `--part finite` run individual parts. For parallel reproduction, `--shard INDEX COUNT` assigns disjoint portions of the case list, with indices starting at zero. The calculation uses exact Gaussian integers for final identities and modular ranks for lower bounds. The small Gaussian-unit expressions that form the original coefficient arrays are represented by integer-valued real and imaginary parts within exact binary64 range. Modular interpolation and determinants use integer arithmetic.
