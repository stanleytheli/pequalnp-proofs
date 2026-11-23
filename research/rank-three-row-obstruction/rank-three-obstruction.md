# Eliminating a rank-three row when all rank-four normals have full support

Let \(P\) be the sum of products over the 120 injections from four rows into five columns, and let \(J\) be the all-ones matrix. Suppose a seven-dimensional linear space \(L\subseteq\mathbb C^{4\times5}\) satisfies \(P(J+X)=120\) for all \(X\in L\).

**Theorem.** At least one of the following holds.

1. A nonzero matrix in \(L\) is supported on at most two rows.
2. A four-dimensional row projection of \(L\) has a normal covector with a zero coordinate.

The theorem leaves the existence of a seven-plane in either class open. The [full-row result](full-row-obstruction.md) proves the assertion when every row projection has dimension four. Below, suppose both conclusions fail. Every two-row projection is injective. Every single-row image has rank at most four, since a surjective image permits a zero translated row. Pair injectivity then makes every rank at least three and permits at most one rank-three row. It suffices to eliminate the case of exactly one rank-three row.

## Coordinates and constraints

Call the three rank-four rows high and the remaining row low. The [low-row reduction](row-reduction.md) shows, up to row and column permutations, that the low-row tangent is given by
\[
   x_0 X_{30}=0,\qquad \sum_{j=1}^{u-1}x_j X_{3j}=0,
   \qquad x_0=\sum_{j=1}^{u-1}x_j,\qquad u\in\{2,3\}.
\]
Here the weights \(x_j\) are coordinates of a chosen reference high-row normal, all nonzero. The active columns are \(0,\ldots,u-1\). All three high normals are proportional there. From the pair classification in the full-row proof, write the high normals \(v_i/s_i\) with \(v_{ij}=E_{ij}x_j\), \(s_i=\sum_jv_{ij}\), and fourth roots \(E_{ij}\). Normalize the active columns and the reference row to ones. The remaining columns of \(E\) have the form \((1,\mathrm i^a,\mathrm i^b)^t\). Enumerate their multisets, quotient by the six permutations of the high rows followed by column rephasing to restore the first row, and choose either orientation at each three-group pair. Every normalized pair has either phases \(1,-1\) or exactly three distinct phases. This gives the following oriented counts, where \(h\) is the number of three-group pairs.

| Active columns \(u\) | \(h=0\) | \(h=2\) | \(h=3\) |
|---:|---:|---:|---:|
| 2 | 3 | 68 | 224 |
| 3 | 1 | 8 | 16 |

Let \(K=(3I_4-\mathbf1\mathbf1^t)\otimes(4I_5-\mathbf1\mathbf1^t)\). This is 12 times the inverse of the polarized quadratic permanent form. Let \(F\) have nine rows. Three are the high-row normals, two are the displayed weighted low tangent constraints, three are the pair constraints between the high rows, and one is total sum zero. The high-pair covectors, on the physical coordinates and after clearing nonzero denominators, are
\[
 -s_k e_i\otimes v_k+s_i e_k\otimes v_i
 \quad\text{or}\quad
 s_k e_i\otimes(v_i|_B)+s_i e_k\otimes(v_k|_C),
\]
respectively for the two- and oriented three-group cases. Each three-group pair also satisfies the necessary conic of the full-row proof. Since \(L\subseteq\ker F\) is isotropic and has dimension seven, \(\operatorname{rank}(F K F^t)\le6\). This holds even if the nine constraints are dependent.

Combine the active columns into the mass \(\eta=2x_0\). Their phases agree in every pair, so all pair conics and row sums depend only on this mass and on the free masses. Each coordinate of that aggregate list is nonzero. Each \(s_i\) and, for every two-group pair, both \(s_i\pm s_k\) are nonzero as well.

## Finite aggregate cases

In the 248 cases with \(h\ge (6-u)-1\), use \(n=6-u\) aggregate variables and degree \(d=n+1\). Construct all degree-\(d\) monomial multiples of the oriented pair conics. The exact Macaulay kernels, contractions, common left-eigenvector test for multiplication matrices, and restriction to the row space of the product of required nonzero factors are justified in the [full-row proof](full-row-obstruction.md). These routines are included verbatim in the shared verifier. Fifty-two cases have empty open support under these tests. The remaining 196 are excluded by projected Gram determinants.

For \(u=2\), actual masses are proportional to \((\eta,\eta,2x_2,2x_3,2x_4)\). For \(u=3\), they are proportional to \((2\eta,\eta+t,\eta-t,4x_3,4x_4)\), for some scalar \(t\). All high-row sums are independent of \(t\). Interchanging the two split columns fixes every constraint and the metric, hence the Gram is a pencil in \(t^2\). Its coefficient factors through the four row coordinates on the column difference. With multiplication matrices of size \(b\), every projected block determinant has degree at most \(4b\) in \(t^2\). The finite-field verifier finds a determinant attaining that bound and a constant gcd of projected determinants. This excludes every complex split by the projective specialization argument of the full-row proof. No diagonalizability or commutativity of the multiplication matrices is required.

## Two three-group pairs with four aggregate coordinates

This accounts for the 68 cases with \(u=h=2\). There is an exceptional high row, joined to the other two by the three-group pairs. Reorient the pair descriptions so it is the lower row, interchanging the two signed groups when the pair is reversed. In that row's weighted coordinates the two parity blocks have totals \(A,B\). The exceptional row sum is \(A+B\ne0\). Each pair has center total \(U\in\{A,B\}\), opposite total \(T\), signed difference \(y\), and \(\gamma=\pm\mathrm i\). Its conic gives
\[
  2y=(1-\gamma)T+v,\qquad
  v^2=(4-2\gamma)T^2-4(1-\gamma)U^2.
\]

For 48 orientations the map from the four aggregate coordinates to \((A,B,y_1,y_2)\) is invertible. The verifier checks its adjugate and enumerates relative signs for repeated radical types. Twenty resulting branches lose a necessary nonzero factor identically. On the chart \(A=t,B=1-2t\), the projected Gram determinant norms over all radical signs have degree at most \(2(n_1+2n_2)2^k\), where \(n_1,n_2\) count the chosen degree-one and degree-two covectors, and \(k\) counts distinct radical types. The verifier includes one projection attaining its degree bound in every successful family. Thus it also tests the omitted projective parameter. Sixteen branches give coprime norms modulo 65521. For 32 branches the common reduced factor is exactly \(t-1\), where \(A+B=0\). At this parameter the square roots are Gaussian integers \(\pm(1+\gamma)\). The verifier checks a vanishing factor of every norm directly over the Gaussian integers. Dividing each by \(t-1\) gives coprime reductions and hence no admissible characteristic-zero parameter. All counts in this paragraph are branch counts after choices of relative radical signs.

On each of the 20 remaining orientations the coordinate map is singular. The verifier checks there are precisely three distinct aggregate phase columns, with one repeated. Combine the two like columns and retain their free scalar split. The repeated class total may vanish, so its coordinate is removed from the required nonzero forms. The three aggregate variables satisfy two conics. Seven orientations have no surviving open point by the finite-dual test. For 13 others the split is eliminated as follows.

Use the two unweighted covectors for the two fixed low coordinates. If the repeated class consists of two free columns, set their masses to \(w+t,w-t\), multiplying the singleton masses by two. The block Gram is even in \(t\). The derivative of the constraint array is supported in the column-difference direction on the three high rows. The high-row restriction of \(3I_4-\mathbf1\mathbf1^t\) is the rank-two matrix \(3I_3-\mathbf1\mathbf1^t\). The coefficient of \(t^2\) thus has rank at most \(2b\), so each determinant has degree at most \(4b\) in \(t\). If a free column repeats the active class, take the three corresponding masses to be \(t,t,w-2t\); the other masses are unchanged. All derivatives are supported on the one column vector \((1,1,-2)\) and the three high rows. Each of the two factors in the Gram product has a derivative factoring through at most \(3b\) coordinates. By Cauchy–Binet, the determinant of a projected Gram has degree at most \(6b\). More explicitly, factor the block Gram as the product of the array of left constraint blocks, the fixed scalar metric, and the corresponding right array, retaining the order of matrix multiplication within blocks. Each outside factor has minors of degree at most \(3b\), since higher coefficients require more independent derivative columns or rows. Both degree bounds hold over characteristic zero. A full-degree determinant and coprime projected determinants modulo a split prime finish each case.

## Four all-sign orientations

The remaining phase multisets of free columns, encoded as \(4a+b\), are
\[
 (u;f)=(2;0,2,8),\ (2;2,2,8),\ (2;2,8,10),\ (3;2,8).
\]
There are no conics for these profiles. Work with four homogeneous variables \((t,a,b,c)\), with physical masses \((t,t,a,b,c)\) for \(u=2\) and \((t,a,t-a,b,c)\) for \(u=3\). Use unweighted constraints for each individual fixed low coordinate and the weighted second low covector for \(u=3\). The nine rows of \(F\) have degrees \((1,1,1,0,0,2,2,2,0)\) in the first case and \((1,1,1,0,1,2,2,2,0)\) in the second. Compute the homogeneous \(7\times7\) minors of \(F K F^t\) whose degree is at most sixteen. Every such polynomial vanishes at a valid point.

For a minor of degree \(D\), dehomogenize at \(t=1\) and evaluate at integer points \((a,b,c)=(25,59,97)+(i,j,k)\) with \(i+j+k\le D\). The point sets are unisolvent for total degree at most \(D\), as follows from the triangular basis of products of falling factorials. Ordinary forward differences in the three variables recover all coefficients exactly. Homogenization recovers the original minors. At the evaluation points the \(9\times9\) Gram is invertible over the rationals. Jacobi's complementary-minor identity evaluates all the minors from the complementary \(2\times2\) minors of its adjugate divided by its determinant. Their signs do not affect vanishing. The verifier removes constant contents and repeatedly divides by any exactly dividing linear factor among the weights, the three row sums, and the six required sums or differences of a sign pair. All such factors are nonzero at any candidate point.

Take monomial multiples of the divided minors at degree 14. There are 680 monomial coordinates. The verifier embeds lists of row numbers selected from these multiples, regenerates every selected integer row from scratch, and recovers the full rational nullspace of the selected submatrix. Independent reduced rows at a prime give the rank lower bound. Exact annihilation and independent recovered rational null vectors give the matching upper bound. The four initial dual-space dimensions are 15, 47, 26 and 39, respectively.

Throughout the final test, a current row space \(E\) must contain the monomial evaluation \(v_{14}(x)\) at any potential point. For a required nonzero linear form \(\ell\), let \(U=C_\ell(E)\) be its degree-thirteen contraction. At a valid point \(C_\ell v_{14}(x)=\ell(x)v_{13}(x)\), so \(v_{13}(x)\in U\). Therefore \(C_{x_j}v_{14}(x)\in U\) for every coordinate \(j\). Every exact functional killing \(U\) pulls back along any such contraction to a functional killing the desired evaluation. The verifier chooses some of these functionals using finite-field pivots, checks they annihilate \(U\) over the integers, and intersects \(E\) with their exact kernels. In each case the dimension reaches zero. A nonzero homogeneous point has nonzero degree-fourteen evaluation, giving a contradiction.

The finite cases, the mixed curves and the four sign orientations exhaust all 320 possibilities. This completes the theorem.
