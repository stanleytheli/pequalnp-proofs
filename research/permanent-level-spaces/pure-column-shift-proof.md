# A pure column offset excludes a seven-plane on the 4×5 permanent level

**Theorem.** Let \(L\) be a complex linear space of \(4\times5\) matrices on which the injective permanent \(P(J+X)\) is constantly 120. If \(L\) contains a nonzero matrix with four identical rows, then \(\dim L\le6\).

The proof combines a rank-three bundle calculation on the complex projective plane with a reproducible exact calculation over the algebraic closure of \(\mathbb F_{241}\). The verifier requires only Python's standard library.

## The quadratic forms on the complement of the offset

For a pure column offset \(\mathbf1 b^\mathsf{T}\), the polynomial \(24e_4(\mathbf1+s b)\) is constant. Hence \(e_1(b)=\cdots=e_4(b)=0\), so up to scaling and permutation \(b=(1,\zeta,\zeta^2,\zeta^3,\zeta^4)\) for a primitive fifth root. Write \(B=\mathbf1 b^\mathsf{T}\). For any \(X\in L\) let \(v_j\) be its column mean. Differentiate \(P(J+s B+t X)\) at \(t=0\). At the background with identical rows only the column means contribute, and the result is \(24\sum_j v_j e_3(\mathbf1+s b_{\widehat j})=0\). Because \(e_d(b_{\widehat j})=(-b_j)^d\) for \(0\le d\le3\), the first four Vandermonde rows annihilate \(v\). Hence \(v\) is proportional to \(b\). Subtracting a multiple of \(B\) yields a variation with all columns centered.

Suppose \(\dim L\ge7\), and retain seven dimensions including \(B\). The centered-column complement \(K\) has dimension six in \(V=H\otimes\mathbb C^5\), where \(H=\{\sum_{i=1}^4 h_i=0\}\) has its nondegenerate complex bilinear dot product. For centered columns \(x_i,x_j\in H\), the sum of the ordered products on distinct rows is \(-x_i\cdot x_j\). The coefficient of the second order in two such variations about \(J+sB\) is therefore governed by the symmetric five-by-five matrices \(G_0,G_1,G_2\). Their diagonals are zero. For \(i\ne j\) write
\[
  (G_m)_{ij}=\sum_{\ell=0}^m b_i^\ell b_j^{m-\ell}\qquad (0\le m\le2).
\]
Indeed \(e_2((\mathbf 1+s b)_{\widehat i,\widehat j})=3-2s(b_i+b_j)+s^2(b_i^2+b_i b_j+b_j^2)\). Thus \(K\) is simultaneously isotropic for the three forms \(\langle-,-\rangle_H\otimes G_m\).

Let \(G=xG_0+yG_1+zG_2\). Its determinant is the following homogeneous quintic:
\[
 f=4x^5-72 y^5+72 z^5+220xy^3z-140x^2yz^2.
\]
This formula and smoothness are verified at the split prime 241. For the formula in characteristic zero, one can also take the column Fourier basis \(e_k=(b_j^k)_j\). Apart from the common factor 5, \(G_m(e_k,e_l)\) vanishes unless \(k+l+m=0\bmod5\). On that antidiagonal the entry is \(4-m\) if \(k\in\{0,-1,\ldots,-m\}\) and \(-(m+1)\) otherwise. The ordinary determinant is recovered by dividing the determinant of this Fourier Gram matrix by the square determinant of the basis change, which is \(5^5\). Smoothness in characteristic zero already follows from smoothness of the modular determinant by properness of the projective singular locus.

## A common isotropic six-plane meets a radical

We prove this over \(\mathbb C\). Otherwise \(K\) would intersect none of the radicals at points of \(\mathbb P^2\). Choose a complement to \(K\) in \(V\). In block form the family of fifteen-by-fifteen symmetric matrices is
\[
 \begin{pmatrix}0&A\\ A^\mathsf T&C\end{pmatrix}.
\]
Here \(A\) has six rows and nine columns of linear forms. It has rank six everywhere, since failure of full rank is exactly a radical direction supported in \(K\). Hence
\[
 0\longrightarrow E\longrightarrow\mathcal O^9
   \xrightarrow{A}\mathcal O(1)^6\longrightarrow0
\]
defines a rank-three bundle on \(\mathbb P^2\). Restrict \(C\) to \(E\); this gives a symmetric map \(E\to E^*(1)\). Splitting the six hyperbolic pairs locally shows that the corank of this restricted form equals that of the fifteen-by-fifteen form. On the reduced quintic \(f=0\), the scalar matrix \(G\) generically has corank one, and the tensor product has corank three. Hence the restriction on \(E\) vanishes generically on each component and, since the divisor is reduced, is divisible by \(f\). This gives a map \(E\to E^*(-4)\). It is nondegenerate off \(f\). Its determinant is a section of \((\det E)^{-2}\otimes\mathcal O(-12)=\mathcal O\), so it is everywhere nondegenerate.

The bundle \(F=E(2)\) is now an orthogonal rank-three bundle of trivial determinant. Fix an orientation by normalizing a trivialization of its determinant. Its Chern classes satisfy \(c_1(F)=0,\ c_2(F)=21-24+12=9\), using the displayed exact sequence. But \(SO_3(\mathbb C)\cong PGL_2(\mathbb C)\) through the adjoint action on trace-zero matrices. The resulting projective bundle lifts to a rank-two vector bundle \(M\): the obstruction lies in the Brauer group of the complex projective plane, which is zero. Equivalently the analytic lifting obstruction in \(H^2(\mathcal O^*)\) vanishes by the exponential sequence, since \(H^2(\mathcal O)=H^3(\mathbb Z)=0\) on \(\mathbb P^2_\mathbb C\). Thus \(F=\operatorname{End}_0(M)\). Writing down the Chern roots of this adjoint representation gives \(c_2(F)=4c_2(M)-c_1(M)^2\), which is 0 or 3 modulo 4. This contradicts 9. [Conrad, *Linear Algebraic Groups I*](https://math.stanford.edu/~conrad/252Page/handouts/alggroups.pdf) [Uematsu, *Brauer group of projective spaces*](https://ccmath.meijo-u.ac.jp/~uematsu/paper/Brauer_group_of_projective_spaces.pdf)

Thus some \(\lambda\in\{f=0\}\) has a nonzero \(h\otimes c\in K\), where \(c\) spans \(\ker G(\lambda)\) and \(0\ne h\in H\). The kernel is a line everywhere on the smooth discriminant. We show that no such incidence can occur.

## Conditions on the two factors

All remaining constraints, including membership of \(h\otimes c\) in a level six-plane \(K\), are closed conditions on a product of projective spaces and a Grassmannian. They are defined over the cyclotomic integers with small denominators inverted. A complex solution would give one over a number field, hence would reduce at the chosen prime over 241 by projectivity. Nonzero vectors are represented by projective points. We therefore finish the exclusion over \(\overline{\mathbb F}_{241}\), choosing \(b_j\) as the five fifth roots there.

On a smooth discriminant, the adjugate of \(G\) is a nonzero scalar times \(cc^\mathsf T\). Thus the three numbers \(c^\mathsf T G_m c\) cannot all vanish: they give the three partials of \(f\) up to one common nonzero factor. The three quadratic isotropy constraints on \(h\otimes c\) imply \(\sum h_i^2=0\). Expanding the cubic and quartic permanent coefficients of this rank-one variation about \(J+sB\) gives the following alternatives:
\[
 e_3(h)\ne0\ \Longrightarrow\
 e_3(c)=0,\quad
 \sum_{i<j<k} c_i c_j c_k\!\!\sum_{\ell\notin\{i,j,k\}}\! b_\ell=0;
 \qquad
 e_3(h)=0\ \Longrightarrow\ e_4(c)=0.
\]
For the second implication, \(e_1(h)=e_2(h)=e_3(h)=0\) makes the four entries of \(h\) scaled fourth roots of unity, so \(e_4(h)\ne0\). Row permutation and scaling then allow \(h=(1,\mathrm i,-1,-\mathrm i)\).

For this fixed \(h\), let \(G'=h\otimes c\). For \(d=2,3,4\) write \(T_d\) for the symmetric multilinear form obtained by summing products of entries of its \(d\) arguments over assignments with distinct rows and distinct columns. The translated permanent's degree-\(d\) polarization is a nonzero constant times \(T_d\). On rank-one arguments \(r_a\otimes v_a\), it is the product of the two respective sums over distinct row and column indices.

On the fifteen-dimensional centered-column space \(V\), form the six linear functionals \(T_d(Y,(G')^a,B^{d-1-a})\) for \(1\le a\le d-1\), and put them in the rows of a matrix \(D\). Any possible \(K\) lies in their common kernel. The six symmetric bilinear forms \(Q=T_d(Y,Z,(G')^a,B^{d-2-a})\) for \(0\le a\le d-2\) all vanish on \(K\). For any linear combination \(Q\), the following rank cap is necessary:
\[
 \operatorname{rank}\begin{pmatrix}Q&D^\mathsf T\\D&0\end{pmatrix}\le18.
\]
Indeed if \(l=\operatorname{rank}D\), the bordered rank equals \(2l+\operatorname{rank}(Q|_{\ker D})\). A six-dimensional isotropic space in the \((15-l)\)-dimensional kernel gives \(\operatorname{rank}(Q|_{\ker D})\le2(15-l-6)\). No assumption about independence of the six functionals is needed.

## Exact elimination and rank calculation

The accompanying verifier uses prime-field arithmetic, univariate polynomial division and Euclid's algorithm, together with explicitly represented finite extensions. It first checks the determinant formula on a full six-value grid by degree-five interpolation. At \(x=0\) the quintic has five simple points. On \(x=1\), a singular point could have neither \(y=0\) nor \(z=0\). Put \(s=z/y^2,\ t=y^5\). The two partials force
\[
 -360+660s-140s^2=0,\qquad 360s^4 t=280s-220.
\]
After substitution into \(4+(-72+220s-140s^2)t+72s^5t^2=0\) the two resulting univariate polynomials have greatest common divisor 1.

For affine points \(x=1\) use projection \(u=y+3z\). The leading coefficient of \(f(1,u-3z,z)\) in \(z\) is a nonzero constant. Let \(c'\) be the first column of the adjugate. It has degree at most four, and can vanish at some points. Every genuine candidate still gives a root of the resultant in \(z\) of \(f(1,u-3z,z)\) and \(e_d(c')\), where \(d=3\) or 4 for the two alternatives. By the resultant degree bound this is a polynomial of degree at most \(20d\) in \(u\). The verifier reconstructs it exactly by interpolation at \(20d+1\) prime-field points and checks three extra evaluations. At each point the resultant is calculated as a determinant of multiplication modulo the quintic; this differs from the usual resultant only by the fixed leading-coefficient factor. The verifier factors the resulting polynomial, certifies irreducibility of each factor by Frobenius and Euclid, and certifies that the factors exhaust all roots.

Over the finite extension furnished by each factor, the verifier takes the univariate gcd of the quintic with the required conditions for **every** adjugate column. This removes incidental zeros of the selected primary column. It includes both equations in the cubic alternative. All remaining gcds split linearly over the represented fields, after removing multiplicities. The five points on \(x=0\) are checked separately. The outcome is:
  
| Radical condition | Degree of initial resultant | Actual points over the algebraic closure |
|---|---:|---|
| Both cubic conditions | 60 | None |
| Quartic condition | 80 | Ten prime-field points with three nonzero coordinates and three degree-ten orbits with five nonzero coordinates |

At each of the forty quartic candidates, evaluation in the appropriate field gives bordered rank 19, already for \(Q=T_3(Y,Z,B)\). The rank is invariant under Frobenius conjugation. Hence every candidate violates the necessary cap of 18. This finishes the projective incidence exclusion and the theorem.
