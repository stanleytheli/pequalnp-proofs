# A full centered column bounds a 4×5 permanent level space by six

**Theorem.** Let \(L\) be a complex linear space of 4×5 matrices. Write \(J\) for the all-ones matrix and \(P(B)=\sum_f\prod_{i=1}^4 B_{i,f(i)}\), summing over injections from four rows to five columns. Suppose \(P(J+X)=120\) throughout \(L\) and \(L\) contains every matrix supported on one designated column with sum zero. Then \(\dim L\le6\). A seven-dimensional example for the unrestricted search problem L-gct-179 must therefore avoid every such column. The bound is attained: use an arbitrary centered fifth column and an arbitrary centered vector in the first four positions of row one, with all other entries zero. Their dimensions add to six. The only possible mixed term factors through the sum of that row vector, so the translated permanent is constant.

Throughout, dot products are complex bilinear, with no conjugation. Products of vectors without a dot are coordinatewise. We use \(T(u,v,w)=\sum_hu_hv_hw_h\), and \(M(u_1,\ldots,u_d)\) for the sum of products on distinct ordered coordinate indices. For centered vectors \(M(u,v,w)=2T(u,v,w)\), by inclusion–exclusion.

## Cofactors and quadratic forms

Take the designated column to be the fifth. Let \(E\) be the projection to the first four columns and denote its rows by \(A_i\in\mathbb C^4\). Its kernel has exactly the three centered directions on the fifth column, since the linear part of the level equation forces the total entry sum to be zero. If \(\dim L\ge7\), one can choose a seven-dimensional subspace containing those three directions. It is enough to exclude \(\dim E=4\).

Let \(g_i\) be the 3×4 injective permanent of the first four translated columns \(J+A\) after omitting row \(i\). Translation along the full centered fifth column makes all four \(g_i\) equal as polynomials on \(E\). Their linear parts force the four row sums \(\sum_h A_{ih}\) to be one common linear form \(S\). The sum of the entries in the fifth column is then \(-4S\). By subtracting centered fifth-column vectors we may use \(-S\) in every position of that column.

Set \(r_i=(A_i,-S)\) and \(D_{ij}=r_i\cdot r_j=A_i\cdot A_j+S^2\) for \(i\ne j\). The centered rows \(r_i\) and the quadratic level identity give \(\sum_{i<j}D_{ij}=0\). The quadratic part of each \(g_i\) is \(2\sum_{j<k,\ j,k\ne i}(2S^2-D_{jk})\). Equality of the four parts implies that the sum of the three \(D\)'s on any three indices is zero: the four such sums are equal and add to twice the total pair sum. It follows that opposite pairs are equal,
\[
 D_{12}=D_{34},\quad D_{13}=D_{24},\quad D_{14}=D_{23},
 \qquad D_{12}+D_{13}+D_{14}=0.
\]

The cubic part of \(g_i\) on the other three rows is \(4S^3+2T(A_j,A_k,A_l)\), by inclusion–exclusion and the three-pair sum just proved. Thus all four triple products \(T(A_j,A_k,A_l)\) agree. The full cubic level identity is proportional to \(\sum_{j<k<l}T(r_j,r_k,r_l)\), because the five-coordinate rows are centered. It gives
\[
 T(A_j,A_k,A_l)=S^3\quad\text{for all distinct }j,k,l.
\]
Counting completions of one and two entries in three rows gives
\[
 g_i=24+18S+12S^2+6S^3,\qquad
 \operatorname{per}_4(J+A)=24(1+S+S^2+S^3+S^4).
\]
The second equality follows from \(P(J+X)=\operatorname{per}_4(J+A)+4(1-S)g_i\).

If \(S=0\), every three-row deletion of \(E\) is a row-centered 3×4 level space: the pair sum vanishes by the \(D\) identities, and its triple moment vanishes by the formula for \(T\). The checked theorem L-gct-157 bounds each of these images by three dimensions. Thus the four-dimensional space \(E\) contains a variation supported on each individual row, giving four independent shifts with some nonzero centered row vectors \(v_i\). The pair identities make these four vectors pairwise orthogonal in \(H=\{{\bf1}\}^{\perp}\subset\mathbb C^4\). At least one, \(v\), is isotropic, since four pairwise orthogonal nonisotropic vectors would be independent. All the others lie in the tangent plane \(v^\perp\cap H\), whose quotient by \(\mathbb Cv\) is a one-dimensional nondegenerate space. At most one of the other vectors can have nonzero projection to that quotient. Thus at least three rows use the line of \(v\). Their cubic coefficient gives \(\sum_hv_h^3=0\); together with the first two vanishing power sums this makes \(v\) proportional to a permutation of \((1,\mathrm i,-1,-\mathrm i)\). The remaining vector \(u\) satisfies \(v\cdot u=0\) and \(v^2\cdot u=0\) by the pair and mixed cubic coefficients. Hence it too is proportional to \(v\). The quartic coefficient on the four independent row shifts is a nonzero multiple of \(24\prod_hv_h\), contradicting the constant square permanent. [Checked L-gct-157](https://data.pequalnp.com/data/lemma/L-gct-157.8e02a0bd6f80.json)

Assume from now on \(S\ne0\). Write \(H=\{u\in\mathbb C^4:\sum u_h=0\}\), a nondegenerate three-dimensional space. Put
\[
 z_i=A_i-\tfrac14 S{\bf1},\quad Z=\sum_i z_i,\quad Y_i=2z_i-Z.
\]
We have \(D_{ij}=z_i\cdot z_j+5S^2/4\). The sum of the three \(D\)'s incident to any index is zero. Consequently the four maps \(Y_i:E\to H\) have the common quadratic form
\[
 Y_i\cdot Y_i=Q=Z\cdot Z+15S^2,\qquad \sum_iY_i=-2Z.
\]
Together they are injective: if they all vanish at one element of \(E\), then \(Z=z_i=0\) there, and the displayed formula forces \(S=0\), whence all \(A_i=0\).

## Only two isotropic directions can occur

If \(\operatorname{rank}Q\ge2\), all four maps \(Y_i\) have nondegenerate images. In a nondegenerate three-space, a degenerate plane has rank one and a line has rank at most one. Each map therefore kills the radical of its pullback form \(Q\). Joint injectivity gives \(\operatorname{rad}Q=0\), impossible since \(\dim E=4\) and \(Q\) is pulled back from dimension three.

If \(Q=0\), each \(Y_i\) has at most a one-dimensional isotropic image. Joint injectivity and \(\dim E=4\) then make the four scalar coefficients on these lines independent coordinates on \(E\). On each individual coordinate axis \(Z\) is isotropic, which forces \(S=0\) there by the formula for \(Q\). These axes span \(E\), contradicting \(S\ne0\).

Hence \(Q=\ell^2\) for a nonzero complex linear form \(\ell\). Let \(G=\ker\ell\), of dimension three. The image \(Z(G)\) has dimension at most one. If \(S,\ell\) are proportional, \(Z\) has zero Gram form on \(G\) and \(H\) has Witt index one. If they are independent, \(Z\cdot Z=\ell^2-15S^2\) has rank two, so \(Z(E)\) is a nondegenerate plane. Its restriction to \(G\) has rank one, and any rank-one pullback into a nondegenerate plane has one-dimensional image.

On \(G\), each \(Y_i\) belongs to a fixed isotropic line or is identically zero. Let \(m\) count its nonzero images. Their scalar coefficients embed \(G\) into \(\mathbb C^m\), so \(3\le m\le4\). Summation maps \(\mathbb C^m\) onto the span of their directions, and sends the embedded \(G\) into the line or zero space \(-2Z(G)\). Its full image has dimension at most \(1+(m-3)\le2\). A plane contains at most two distinct isotropic lines in \(H\): its projective line meets the nondegenerate projective conic in at most two points.

### One line

If all nonzero directions are on \(\mathbb Cv\), then \(Z(G)\) is isotropic, \(S=0\) on \(G\), and \(G=\ker S\). Write \(A_i=z_i=a_i v\) on \(G\). The amplitude forms span a three-dimensional space, so at least three are nonzero. Applying \(T(A_j,A_k,A_l)=0\) to three active rows shows \(\sum_hv_h^3=0\). Together with \(\sum v_h=\sum v_h^2=0\) this implies \(v\) is proportional to a permutation of \((1,\mathrm i,-1,-\mathrm i)\), since its first three elementary symmetric functions vanish.

The degree-four part of the square permanent on \(G\) is \(24(\prod_hv_h)\prod_i a_i\). The cofactor formulas make it zero, so some amplitude vanishes identically. Dimension three gives independent shifts along \(v\) on the other three rows. For any index \(k\) choose two of those independent rows avoiding \(k\). The bi-affine coefficient in the two shifts in the triple identity gives \(v^2\cdot A_k=0\) and hence \(v^2\cdot z_k=0\), since \(\sum v_h^2=0\). The opposite-pair identities also give \(v\cdot z_k=0\): varying a single active row \(i\ne k\) changes \(D_{ik}\) but leaves its opposite pair fixed. The common orthogonal space in \(H\) of \(v,v^2\) is \(\mathbb Cv\). All \(z_k\) therefore lie on this isotropic line everywhere on \(E\), making all incident \(D\)'s equal \(5S^2/4\). Their sum cannot be zero.

### Two lines

Suppose the directions on \(G\) are the distinct isotropic lines of \(v,w\). Then \(m=4\). Summation \(C:\mathbb C^4\to\operatorname{span}(v,w)\) has a two-dimensional kernel; it kills exactly the separate coefficient sums in the \(v\) and \(w\) groups. The three-dimensional image of \(G\) in coefficient space maps to at most one dimension, so it contains the whole kernel \(R=\ker C\). On \(R\) we have \(Z=S=0\), hence \(z_i=Y_i/2=A_i\).

If three positions are on the line of \(v\), any supported pair difference \(v,-v\) in those positions occurs in \(R\), up to scaling. For any row \(k\), choose a pair \(a,b\) avoiding it. The quadratic coefficient in the triple identity on the rows \(a,b,k\), after translating along that difference, is \(-T(v,v,A_k)=0\). Therefore every \(z_k\) belongs to the plane \(P=H\cap(v^2)^\perp\), and so do all \(Y_i\). The plane is proper because \(v^2\) cannot be constant for a nonzero isotropic \(v\). It contains both \(v,w\), whose dot product is nonzero, so it is nondegenerate. Each rank-one map \(Y_i:E\to P\) now has one-dimensional nonisotropic image and kills \(G\), contrary to joint injectivity.

The remaining multiplicities are two and two. Arrange the rows so that \(R\) consists precisely of
\[
 (av,-av,bw,-bw).
\]
The two group parameters are independent. The triple identities, using the pair differences, show \(T(v,v,w)=T(w,w,v)=0\). The quartic coefficient on \(R\) gives \(M(v,v,w,w)=0\).

We classify these two isotropic lines directly from the three moments. Let \(d=v\cdot w\ne0\), \(p_h=v_hw_h\) and \(n=4p-d{\bf1}\). The vector \(n\) is centered. The mixed cubic identities give \(n\cdot v=n\cdot w=0\). In the centered fourth-moment identity
\[
 M(v,v,w,w)=2d^2-6\sum_h p_h^2,
\]
only the two \(v,w\) pairings and the block of size four survive inclusion–exclusion. Thus \(\sum p_h^2=d^2/3\) and \(n\cdot n=4d^2/3\ne0\). The vectors \({\bf1},v,w,n\) form a basis: the first and fourth are nonisotropic and orthogonal to the other three, and \(v,w\) form a nondegenerate isotropic pair.

Compute the squared norm of \(e_h-{\bf1}/4\) in this basis. Its coefficients along \(v,w,n\) are \(w_h/d,v_h/d,n_h/(n\cdot n)\), respectively. Hence
\[
 \frac34=\frac{2p_h}{d}+\frac{(4p_h-d)^2}{4d^2/3},
 \qquad 16p_h(3p_h-d)=0.
\]
Since \(\sum p_h=d\ne0\), three coordinates of \(p\) equal \(d/3\) and the remaining coordinate is zero. The vector \(n\) is therefore proportional, after reordering, to \((-3,1,1,1)\). The simultaneous orthogonality of \(v,w\) to \({\bf1},n\) forces their first coordinate to be zero. The two isotropic lines in the remaining centered triple can be normalized to
\[
 v=(0,1,\omega,\omega^2),\qquad w=(0,1,\omega^2,\omega),\qquad
 \omega^2+\omega+1=0.
\]
Replace \(n\) by the proportional vector \((-3,1,1,1)\).
Now \(v^2=w,\ w^2=v\). Translating the pair differences in rows 1,2 and 3,4 in the triple identities gives \(z_1,z_2\in v^\perp=\operatorname{span}(v,n)\) and \(z_3,z_4\in w^\perp=\operatorname{span}(w,n)\), taking orthogonals in \(H\). Write their respective \(v\) or \(w\) amplitudes as \(a_1,a_2,b_3,b_4\), and their \(n\)-amplitudes as \(c_i\). Comparing the coefficients of the two independent pair differences in \(D_{13}=D_{24}\) gives \(a_1+a_2=b_3+b_4=0\), because \(v\cdot w=3\).

The \(v,w\) amplitudes therefore contribute opposite signs to \(D_{13},D_{14}\), and equal signs within either complementary pair. The three complementary-pair equalities imply
\[
 c_1c_2=c_3c_4,\quad c_1c_3=c_2c_4,\quad c_1c_4=c_2c_3.
\]
For each index \(i\), its incident sum gives
\[
 (n\cdot n)c_i\sum_{j\ne i}c_j=-15S^2/4.
\]
No \(c_i\) can be the zero form. In the fraction field of the polynomial ring on \(E\), the three complementary products imply \(c_i^2=c_1^2\) for every \(i\), so \(c_i=\pm c_1\). The sum of three signs is nonzero. The incident sum then gives \(c_1^2\) proportional to \(S^2\) by a nonzero scalar. Thus all \(c_i\) vanish on \(\ker S\). There only the two parameters in \(av,-av,bw,-bw\) remain, contradicting \(\dim\ker S=3\).

Every case for a four-dimensional projection has been excluded. This proves the bound for the stated class of 4×5 level spaces.
