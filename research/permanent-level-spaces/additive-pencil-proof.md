# A 4×5 permanent level space has at most one additive direction

**Theorem.** Let \(L\) be a complex linear space of \(4\times5\) matrices. Suppose the injective permanent of \(J+X\) equals 120 for every \(X\in L\), with \(J\) all ones. Then the intersection of \(L\) with the matrices of the form \(X_{ij}=u_i+v_j\) has dimension at most one. This is sharp. Taking \(u=0\) and \(v\) proportional to the five distinct fifth roots of unity gives a line on the level. Thus any seven-dimensional example for L-gct-179 must have at least six independent images under double centering.

The proof excludes a projective family of possible two-dimensional spaces by a finite calculation over the algebraic closure of the field with 65,521 elements. The accompanying Python verifier uses only the standard library. Its interpolation and univariate polynomial operations certify the algebraic closure calculation.

## Reduction to a pencil of tetrahedral row coordinates

The property of being a two-dimensional subspace of the additive matrices on which the translated permanent is constant is a closed condition on a Grassmannian over \(\mathbb Z\). On each integral affine coordinate chart it is the vanishing of the coefficients of the translated permanent on two independent vectors. Equivalently these coefficients define the zero locus of a section on the Grassmannian of planes in the additive matrix space. If that locus has a complex point, it has a point over a number field, since it is of finite type over \(\mathbb Q\). Grassmannian properness extends that point to the valuation ring at any prime of the number field over 65,521. Reduction would give a plane over \(\overline{\mathbb F}_{65521}\). We work over this algebraically closed field from now on. All small integer divisions below are valid.

The linear coefficient gives total entry sum zero. Write the unique centered row and column offsets as \(u\in H_4,\ v\in H_5\), with \(H_m=\{x:\sum x_i=0\}\). A pure row offset must be zero, since \(\prod_i(1+\lambda u_i)=1\) for every \(\lambda\). A pure nonzero column offset \(b\) satisfies \(e_1(b)=\cdots=e_4(b)=0\) by expanding \(24e_4(\mathbf1+\lambda b)\), so its coordinates are five distinct roots of \(z^5+c\). Differentiate the level equation at this pure direction along any \((u,v)\) in the putative plane. By row symmetry the row terms are proportional to \(\sum u_i=0\). The column terms give \(\sum_j b_j^d v_j=0\) for \(0\le d\le3\), since \(e_d(b_{\widehat j})=(-b_j)^d\). These four rows are independent by Vandermonde. The projection to column offsets is injective, so a plane cannot contain a nonzero pure column offset. Consequently the row projections of any plane form a plane \(U\subset H_4\), with the column offsets depending linearly on the two parameters.

Use tetrahedral coordinates for the row offsets
\[
 u=(x+y+z,\;x-y-z,\;-x+y-z,\;-x-y+z).
\]
The plane \(U\) now has normal \(n=(n_1,n_2,n_3)\) in three-space, up to a nonzero scalar. For a parameter basis \(X,Y\) on \(U\), write the five column offsets as \(s_j X+t_jY\). Set \(M_d=\sum_j(s_jX+t_jY)^d\). For \(d=2,3,4\), counting the chosen row and column factors in the permanent gives
\[
\begin{split}
 M_2&=-\tfrac{20}{3}(x^2+y^2+z^2),\\
 M_3&=-60xyz,\\
 M_4&=\tfrac{260}{9}(x^4+y^4+z^4)-\tfrac{200}{9}(x^2y^2+y^2z^2+z^2x^2).
\end{split}
\]
Indeed, in elementary coordinates the respective equations are \(e_2(u)+3e_2(v)/5=0\), \(e_3(u)+2e_3(v)/5=0\), and \(e_4(u)+e_2(u)e_2(v)/10+e_4(v)/5=0\). These follow by choosing the column-supplied factors in \(\sum_{k=0}^4 k!(5-k)!\,e_{4-k}(\mathbf1+u)e_k(v)\). Newton's identities then give the displayed power sums. Also \(M_0=5,\ M_1=0\).

## The projective condition from the fourth moments

Write \(m_{ij}=\sum_h s_h^i t_h^j\); it is the coefficient of \(X^iY^j\) in \(M_{i+j}\) divided by \(\binom{i+j}{j}\). In the monomial list \(\mathcal B=(1,s,t,s^2,st,t^2)\) form the symmetric six-by-six matrix \(H_{ab}=m_{a b}\), where subscripts \(ab\) denote multiplication of monomials. It is \(E^\mathsf{T}E\) with \(E\) the five-by-six evaluation matrix on the five points \((s_j,t_j)\). In particular its determinant vanishes.

Define \(a=n_1^2,b=n_2^2,c=n_3^2\), and \(A=a+b+c,\ B=ab+bc+ca,\ C=abc\). For the parameterization \((x,y,z)=(n_3X,n_3Y,-n_1 X-n_2Y)\), the determinant equals
\[
 \frac{16000000}{177147}n_3^8
 [-2200 A^4+39285 A^2B-59049 B^2-249318 AC].
\]
The verifier checks the identity on the full \(17^3\) grid in \(n_1,n_2,n_3\). Both sides have degree at most 16, so these grid evaluations prove the identity as a polynomial over the field. Permuting coordinates lets us choose a nonzero \(n_3\). Therefore the bracket vanishes for every possible normal.

Suppose \(A\ne0\), and normalize \(A=1\) by scaling the normal. With \(T=B\) we have
\[
 C(T)=(-2200+39285T-59049T^2)/249318.
\]
The three squared normal coordinates are then the roots of \(h_T(z)=z^3-z^2+Tz-C(T)\). For \(C(T)\ne0\), parameterize the plane by
\[
 x=n_2n_3 X,\quad y=n_1n_3 Y,\quad z=-n_1n_2(X+Y).
\]
The formulas for \(M_2,M_3,M_4\) are polynomial in \(a,b,c\). A moment of order \(d\) has total degree \(d\) in these variables. We now impose that these truncated moments arise from five equal-weight points.

## Equal-weight moment conditions

For each omission of one quadratic monomial from \(\mathcal B\), let \(\mathcal D\) be the remaining five monomials and \(b_*\) the omitted one. Write \(D\) for their square evaluation matrix, \(G=D^\mathsf{T}D\), \(g=\det G\), and \(J_G=\operatorname{adj}G\). The conic
\[
  Q=g b_*-\sum_{a\in\mathcal D}
      (J_G(m_{b b_*})_{b\in\mathcal D})_a a
\]
vanishes on all five points. The elementary matrix identity \(D J_G D^\mathsf{T}=gI\) proves this even for singular \(D\). That identity follows first for a generic invertible matrix and hence identically as a polynomial.

There are six unknown degree-five moments \(m_{5-i,i}\). Summing \(Q(s_j,t_j)\) times each degree-three monomial gives four linear equations in them. Write \(K_s=D^\mathsf{T}\operatorname{diag}(s_j)D\) and define \(K_t\) similarly. The conditions \(\operatorname{tr}(J_G K_s)=g\sum s_j=0\) and \(\operatorname{tr}(J_G K_t)=0\) add two more. For this six-by-six system let \(d\) denote its determinant and \(N_i\) the Cramer numerator for the \(i\)-th unknown. At every genuine solution \(N_i=d\,m_{5-i,i}\), including when \(d=0\).

Build \(\widehat K_s,\widehat K_t\) from the fixed moments multiplied by \(d\) and the Cramer numerators. They equal \(dK_s,dK_t\) for every solution. Therefore three necessary polynomial identities, one for each ordered choice \(l,m=(s,s),(s,t),(t,t)\), are
\[
 R_{lm}=\operatorname{tr}(J_G\widehat K_l J_G\widehat K_m)-(gd)^2 m_{lm}=0.
\]
These again follow from \(D J_G D^\mathsf{T}=g I\) and hold for singular matrices. Repeating with the three omissions gives nine polynomials.

For each of the nine expressions \(R\), multiply by each weight \(1,a,b,ab,a^2,a^2 b\) and sum over all six permutations of \(a,b,c\). The resulting 54 expressions are symmetric in the roots of \(h_T\). They are polynomials in \(T\), since the elementary functions are \(1,T,C(T)\). Every genuine level pencil makes all 54 vanish because each ordered choice parameterizes an equivalent plane. Sign changes of the normal coordinates are harmless: the tetrahedral degree-three polynomial changes at most by a sign upon a coordinate reflection, which can be offset by negating all column covectors. The second and fourth moments are unchanged.

For exact interpolation, the determinant \(g\) has degree 12, and entry \((i,j)\) of \(J_G\) has degree \(12-\deg i-\deg j\) for monomials \(i,j\in\mathcal D\). The four conic equations have degree-12 coefficients for their unknowns and degree-17 right sides. The two trace equations have degree-8 coefficients and degree-13 right sides. Thus \(d,N_i\) have degrees 64 and 69, and every \(R\) has degree 154. The weight increases this to at most 157. Replacing the elementary symmetric functions by \(1,T,C(T)\) cannot increase total degree in \(T\), since \(C(T)\) has degree two and the third elementary function has weight three. Thus 158 distinct samples in the prime field determine each trace polynomial everywhere, including at repeated-root parameters. The verifier uses \(T\) with three distinct prime-field roots and four further checks. It computes the greatest common divisor of the 54 polynomials by Euclid's algorithm. Its complete factorization, up to scalar, is
\[
 (T-12224)^{28}(T-25076)^{38}(T-45496)(T-57004)
 \quad\text{in }\mathbb F_{65521}[T].
\]

The roots \(12224,25076\) have \(C(T)=0\). For them, choose \(a=0\) and \(b+c=1,\ bc=T\). Use \(x=n_2n_3X,\ y=n_3Y,\ z=-n_2Y\). The moment formulas are symmetric in \(b,c\), hence prime-field calculations in \(T\) suffice. The verifier excludes each case by a nonzero trace residual or by an inconsistent Cramer system.

For \(T=45496,57004\) the cubic has distinct roots over the algebraic closure. The verifier interpolates the six weighted permutation sums of \(d\) and of each \(N_i\), now using 73 sample values because their weighted degrees are at most 72. For the omission of \(s^2\), all six weighted sums of \(d\) vanish at both candidate parameters. The six weight functions form a basis of functions on the six distinct ordered triples: for each of three distinct values of \(a\) there are two distinct values of \(b\), and interpolation first in \(b\), then in \(a\), supplies all six functions. Thus \(d=0\) at every ordering. A weighted numerator trace is 35289 or 12462, respectively, and is nonzero. Some Cramer numerator must be nonzero at an ordering, contradicting \(N_i=d\,m_{5-i,i}\).

## Isotropic normal and sharpness

When \(A=0\), the determinant condition gives \(B=0\). Up to scaling, sign changes, and permutation, the normal can be taken as \(n=(1,\omega,\omega^2)\), with \(\omega\) a primitive cube root. Its orthogonal plane has coordinates \((x,y,z)=(X+Y,X+\omega Y,X+\omega^2Y)\). Hence
\[
 M_2=-20X^2,\qquad M_3=-60(X^3+Y^3),\qquad M_4=20X^4+480XY^3.
\]
The resulting moment matrix has rank five. The principal minor omitting \(st\) is 21661 in the prime field. Its \(st\) column is minus twice its \(t\) column. Since \(H=E^\mathsf{T}E\) has rank five, \(E^\mathsf{T}\) is injective, and therefore \(t_j(s_j+2)=0\) for all five points. We have \(\sum t_j^3=-60\ne0\) and \(\sum t_j=0\), so at least two of the \(t_j\) are nonzero. At least two of the \(s_j\) must equal \(-2\). But Newton's identities from \(M_d(X,0)\) give their monic root polynomial as
\[
 z^5+10z^3+20z^2+45z-e_5(s).
\]
Its derivative at \(-2\) is 165, nonzero in the chosen field. This contradiction exhausts the final projective normal.

There is consequently no additive level plane over the algebraic closure in this characteristic, hence none in characteristic zero. The fifth-root column construction in the theorem gives equality. The entire argument concerns a restricted part of an arbitrary level space; existence of an unrestricted seven-plane remains open.
