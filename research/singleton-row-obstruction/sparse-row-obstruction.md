# Single sparse row normals on the 4 by 5 permanent level

Let \(P(A)=\sum_{\sigma:[4]\hookrightarrow[5]}\prod_{i=1}^4 A_{i,\sigma(i)}\), and let \(J\) be the all-ones matrix. Assume \(L\) is a seven-dimensional complex linear space and \(P(J+X)=120\) for every \(X\in L\).

**Theorem.** Suppose projection onto each pair of rows is injective, all four row projections have dimension four, and exactly one row normal has a zero coordinate. Then this sparse row normal has support of size at most two.

The theorem leaves open one- and two-coordinate supports and cases with multiple sparse normals or a smaller row projection. Pair injectivity means that no nonzero element of \(L\) is supported on at most two rows.

## Finite configuration and Gram obstruction

Write \(u\) for the size of the sparse support \(S\) and \(T\) for its complement. We exclude \(u=3,4\). Normalize each row normal to have coordinate sum one. Its sum is nonzero, since otherwise the translated row image would contain zero. Call the first three normals high. Their pairwise phase constraints and the nonsingular polarized quadratic form are proved in the [full-row argument](full-row-obstruction.md). The [sparse/high classification](sparse-high-pair.md) supplies the other three pair constraints.

Using the first high row as a reference, express the physical normals as \(v_i/s_i\) where \(v_{ij}=E_{ij}x_j\) and \(s_i=\sum_jv_{ij}\). Every \(x_j,s_i\) is nonzero. The high phases \(E_{ij}\) are fourth roots of unity. Normalize by row and column rephasings so the first high row consists entirely of ones, and every row has phase one in a chosen active column. The sparse phases, on comparison with the first high normal, are \(\pm1\) on \(S\) and zero on \(T\). Comparison with each other high normal makes all the high phases on \(S\) signs as well. Thus an active column has three binary relative signs, and a missing column has two arbitrary fourth roots relative to the high base.

Enumerate these column multisets, quotienting by permutations of the three high rows, rephasing, and permutations within \(S,T\). For a high pair with three phase values the two orders of its signed groups are tested. For a sparse/high pair with two values on the support, test each way of defining \(B,C\) as its two sign classes. For a common ratio on the support, enumerate every pair of disjoint nonempty ordered subsets \(P,Q\subset T\).

Each pair contributes a homogeneous linear constraint on \(L\), and the three-group high pairs and all sparse/high pairs also have quadratic equations on the \(x_j\). Here are the two sparse/high equations, with sparse row \(i\) and high row \(k\):
\[
\begin{array}{ll}
s_k\sum_{C}v_{ij}+s_i\sum_Bv_{kj}=0,&
s_k e_i\otimes v_i|_C+s_i e_k\otimes v_k|_B,\\
s_k\sum_P v_{kj}+s_i\sum_Qv_{kj}-s_i s_k=0,&
s_k e_i\otimes v_k|_P+s_i e_k\otimes v_k|_Q .
\end{array}
\]
The second covector in each entry is the corresponding homogeneous tangent constraint; the parentheses in \(v|_C\) mean restriction with extension by zero. In the common-ratio case the phase ratio on \(S\) is one by our normalization. The physical normal ratio there is \(s_k/s_i\), giving the second formula directly.

In coordinates \(Z_{ij}=x_jX_{ij}/s_i\), the four row normals and six pair covectors give a ten-row matrix \(M\) with entries in \(\{0,\pm1,\pm\mathrm i\}\) depending only on relative phases and groups. The assumed pair projections of \(L\) have dimension seven. A pair of row projections of \(\ker M\) contains such an image and is itself subject to two row normals and one independent pair relation, hence has dimension seven. Thus \(\operatorname{rank}M-\operatorname{rank}(M|_{\rm other\ two})=3\) for every row pair. The verifier computes the ranks at both split embeddings over \(1{,}000{,}000{,}009\). A Gaussian minor has absolute value at most \(10^5\) by Hadamard's inequality. Vanishing at both embeddings therefore proves exact vanishing. The test leaves 713 orientations for support four and 1,407 for support three.

In physical coordinates, append the total-sum covector to the ten constraints, giving \(F\). Write
\[
 K=(3I_4-\mathbf1\mathbf1^t)\otimes(4I_5-\mathbf1\mathbf1^t).
\]
This is 12 times the inverse of the polarized quadratic. The [isotropic dimension argument](full-row-obstruction.md) gives \(\operatorname{rank}(F K F^t)\le6\) at any admissible weights.

## Finite aggregate weights

Combine columns whose phases agree in every row and whose memberships in \(P,Q\) agree for every common-ratio pair. The source enumerations have four or five distinct groups in the retained finite cases that reach the Gram test. The conics and row sums depend only on aggregate masses. Require every singleton mass, each row sum, and both \(s_i\pm s_k\) for a two-group high pair to be nonzero. A repeated group's aggregate is allowed to vanish.

With \(n\) aggregate masses and at least \(n-1\) homogeneous conics, the verifier calculates a degree-\(n+1\) Macaulay kernel. For each individual case it uses the [exact contraction and multiplication-matrix argument](full-row-obstruction.md); the count of equations is simply a way to route cases. Empty open support excludes 635 orientations for support four and 1,359 for support three. Six orientations at each support size require the Gram test.

In a doubled column, use masses proportional to \(w+t,w-t\) and double every singleton mass. The Gram is unchanged by swapping the two identical columns, so it is a pencil in \(t^2\). With operator block size \(b\), its \(t^2\) coefficient has rank at most \(4b\) by factorization through the four column-difference row coordinates. When both columns are missing from the sparse normal and no common-ratio \(P\) contains either one, no sparse-row slot of any constraint has a varying derivative. Only the three high rows occur. The restriction of the row metric to them has rank two, hence the sharper bound \(2b\). Interpolation according to the corresponding bound yields a full-degree projected determinant and coprime projected determinants at a split prime. The [specialization argument](full-row-obstruction.md) rules out every complex split parameter, including any with non-real coordinates.

## The rational curves

The other cases have five distinct aggregates and three conics. All three high pairs are sign pairs, so every entry of \(E\) is a sign or zero. Set the total of the sparse row's active masses to one. For any two-group sparse/high pair take \(y_i\) as the signed high total on \(S\), \(t_i\) its signed high total on \(T\), and \(h_i\in\{1,-1\}\) as the phase ratio on \(B\). The [pair calculation](sparse-high-pair.md) gives
\[
    z_i=h_i y_i-1,\qquad z_i^2+h_i t_i z_i=2.                    \tag{1}
\]
In particular its two roots are nonzero and have product \(-2\).

**Support four.** Both sparse/high sign classes occur for each of the high rows. With only one missing coordinate of weight \(t\), put \(e_i=E_{i,4}\). For \(v_i=e_i h_i z_i\), (1) reads \(v_i^2+t v_i=2\). Choose one root \(v\) as a parameter; the other is \(-2/v\), and \(t=2/v-v\). Each high total on the active columns is \(y_i=h_i+e_i v_i\). The active \(4\times4\) sign matrix is invertible for every one of these 72 orientations, as checked by its integer determinant and adjugate. Thus all masses are rational functions of a single nonzero finite \(v\). Choosing the first row's root to be \(v\) leaves four assignments. Among the 288 branches, 180 lose a required nonzero factor identically and 108 are excluded by the univariate Gram calculation below.

**Support three.** In all 42 curve orientations the \(4\times3\) active sign matrix has rank three. Thirty have one common-ratio sparse/high pair and twelve have none.

With one common-ratio pair, its two missing coordinates form singleton \(P,Q\). Let their signed masses in this high row be \(t,q\). Its conic becomes \(t(t+q)=1\), so \(t\ne0\) and \(q=t^{-1}-t\). In the other two high rows the signed missing total is, up to a row sign, either \(t+q=1/t\) or \(t-q=2t-1/t\). The two roots of \(z^2+(2t-1/t)z=2\) are \(1/t,-2t\). For the other type take \(v\) as a root of \(v^2+v/t=2\), giving \(t=v/(2-v^2)\) and the second root \(-2/v\). The denominator is nonzero at any finite nonzero \(t\). If this type is absent, use \(t\) itself. Enumerating the relative root choices recovers all three high active totals. The rank-three active matrix then recovers the active masses.

Without a common-ratio pair, write \(p,q\) for the two missing masses and \(T_+=p+q,\ T_-=p-q\). On the two missing columns the high rows have signs, so every \(t_i\) equals, up to sign, one of these two totals. Every one of the twelve orientations uses one type twice and the other type once. The active sign matrix has a unique relation among its four rows, and its coefficient on the singleton-type high row is nonzero. Both facts are verified from the sign matrix. For the repeated type choose a root \(v\) of \(v^2+T v=2\); its other root is \(-2/v\). Their assignments fix both active high totals. The linear relation, together with sparse total one, then determines the remaining high total and its root \(w\). This root must be nonzero. The two signed missing totals are \(2/v-v\) and \(2/w-w\), so \(p,q\) and all active masses are rational in \(v\). The verifier substitutes each parametrization back into all three conics as identities of rational functions. Over the 42 orientations it checks 114 branches. Fifty-five lose a required factor identically; 59 require the univariate Gram test.

For the **univariate Gram test**, clear a common denominator of the five mass functions and remove any common polynomial factor of all numerators. All denominators used in the derivation are nonzero at a candidate. After this choice the five weights are integer polynomials of some degree at most \(m\). Project \(F K F^t\) to seven constraints, using \(n_0,n_1,n_2\) combinations separately from covectors homogeneous of degrees zero, one and two in the weights. The determinant polynomial in the parameter has degree at most \(2m(n_1+2n_2)\). Integer determinants at consecutive integer arguments and Newton interpolation recover it exactly. The verifier removes exactly dividing factors of the necessary nonzero polynomials and takes primitive gcds over \(\mathbb Q\). A constant final gcd excludes every complex value of the finite parameter. This uses exact integer identities without root approximation.

The finite and rational cases account for every retained orientation in both support sizes. This proves the theorem. No claim is made here on the other classes of seven-planes.
