# The support-two normal is disjoint from the low active columns

Let a seven-dimensional complex linear space preserve the value of the rectangular 4 by 5 permanent after translation by the all-ones matrix, and project injectively onto each pair of rows. Suppose the four row ranks are 4,4,4,3. Let two rank-four normals have full support and let the third have support \(D\) of size two. Present the rank-three affine row as \(Ua=U\mathbf1\), where \(U\) has rank two, and call a column active if its column in \(U\) is nonzero. This set is invariant under changes of the two defining covectors.

**Theorem.** Both coordinates of \(D\) lie outside the rank-three row's active columns.

The [mixed-row two-column argument](https://github.com/stanleytheli/pequalnp-proofs/blob/b84251b1c4c1701c56b3d1601cce6f0725bcf67e/research/mixed-row-obstruction/mixed-row-obstruction.md) splits the active columns into nonempty classes \(A,B\) on which the restrictions of the first full normal prescribe equal nonzero totals. In particular the physical base weights satisfy \(\sum_Ax_j=\sum_Bx_j\ne0\). On a cross pair, the low row can be supported on the two chosen coordinates with both entries nonzero. Its projection with the sparse row is Cartesian. If the sparse row normal were nonzero on exactly one coordinate of the pair, varying the other sparse row coordinate would vary the two-row permanent factor; its product with the remaining permanent is a nonzero constant polynomial on the affine line. This is impossible. Thus \(D\) contains all active columns, or none.

If \(D\) contains all active columns, its size two makes \(A,B\) singletons. Label these coordinates 0 and 1. The two full phases and the sparse phase can each be normalized to agree on these indices. Hence the sparse signed row total is \(2x_0=2x_1\) and we may set \(x_0=x_1=1/2\). There are three unconstrained nonzero missing weights, denoted \(w_2,w_3,w_4\).

## The two missing-coordinate conics

Both sparse/full pairs have a common ratio on \(D\). The [classification of a sparse/full pair](https://github.com/stanleytheli/pequalnp-proofs/tree/4ba51579c0716b65d49ec02fa68e51c3e3d92e72/research/support-two-row-obstruction) gives ordered disjoint nonempty subsets \(P,Q\) of the three missing coordinates. Write \(T\) for the full row's signed total over all missing indices and use \(P,Q,R\) also for its signed masses on \(P,Q\) and their complement. The conic is
\[
        (1+T)P+Q-(1+T)=0,\qquad PT=1+R .
\]
The verifier recomputes all full/sparse phases, pair groups and the necessary ranks of their eight homogeneous tangent constraints. This leaves 1,834 orientations with the proposed containing support. In 1,554 of these the full/full pair has three relative phase values and supplies the third conic, besides the two displayed above. The established finite [mixed-row Macaulay and Gram computation](https://github.com/stanleytheli/pequalnp-proofs/blob/b84251b1c4c1701c56b3d1601cce6f0725bcf67e/research/mixed-row-obstruction/mixed-row-obstruction.md) excludes 16 by the empty open locus and 1,538 by the Gram rank condition. The remaining 280 have only two full/full ratio values, and all phases are real signs.

Set \(t=T\) for the first common-ratio row. Its two linear identities on the three missing weights are their signed sum \(t\) and \(tP-R=1\). When the complement \(R\) contains a coordinate, use one coordinate in \(Q\) and one in \(R\) as pivots; their determinant is a nonzero sign. Otherwise use one in \(P\) and one in \(Q\), with determinant a nonzero sign times \(t\). In the latter case \(t\ne0\) follows from \(tP=1\). Calling the free weight \(v\), obtain
\[
       w_j=C_j(t)+L_j(t)v .
\]
The second conic becomes \(g_0(t)+g_1(t)v+g_2(t)v^2=0\) after clearing a common denominator. Retain the original coefficients and every root of their common content or leading coefficient. These exceptional values are treated separately below. For 160 orientations the generic second equation is linear in \(v\), 46 have a rationally split quadratic, 66 have an unsplit quadratic and eight have generic degree zero.

## Generic norms and exceptional fibres

Away from the exceptional parameter values a linear branch or split quadratic gives rational \(v\). In the unsplit case set \(b=g_2v\), which satisfies the monic equation \(b^2+g_1b+g_0g_2=0\). After clearing denominators all five homogeneous weights are polynomials in \(t\) with coefficients in this rank-at-most-two algebra. These transformations preserve every point where the original chosen pivot and the leading coefficient are nonzero.

Take the same nine physical covectors as in the mixed-row argument: three rank-four row normals, two singleton low block covectors, three rank-four pair relations, and the total-sum covector. The scalar Gram relative to \(K=(3I_4-\mathbf1\mathbf1^t)\otimes(4I_5-\mathbf1\mathbf1^t)\) must have rank at most six. A seven-row projected determinant therefore vanishes on the candidate sheet. Its norm through the monic extension is an integer polynomial in \(t\); for a rational branch the norm is the determinant itself. If a required mass or row total is identically zero on a branch, that branch has no admissible point.

The program computes the projected norm by exact signed-radix reconstruction using the [published coefficient bound](https://github.com/stanleytheli/pequalnp-proofs/blob/4ba51579c0716b65d49ec02fa68e51c3e3d92e72/research/support-two-row-obstruction/support-two-obstruction.md). Here a projection uses \(n_1,n_2\) combinations of the five degree-one and three degree-two covectors, and optionally the sole degree-zero covector. The absolute coefficients are at most seven. If each weight has modulus at most \(W\ge1\) on the unit parameter circle on both sheets, the projected coordinate bounds \(77,77W,77\cdot5W^2\) apply. The entrywise metric bound six and the 20 physical coordinates give the uniform single-sheet determinant bound
\[
  7!(20^2\cdot6\cdot77^2)^7\,5^{2n_2}W^{2(n_1+2n_2)}.
\]
Its power by the number of sheets bounds coefficients of the norm by Cauchy's formula. Successive projected norms and primitive gcds produce a finite set of parameter roots on every generic chart. Unite these roots with \(t=0\) and the exceptional content and leading roots. The full row total excludes \(t=-1\).

At each resulting factor, return to the original three coefficients. When the specialized second equation has degree zero with nonzero constant, it is inconsistent. In degrees one and two, companion matrices give operators for \(t,v\), including both possible roots. Exact inverses are checked in the corresponding polynomial quotient. With the two active weights fixed at \(1/2\), restrict these operators to the required nonzero physical weights, row totals, and the two-ratio full-pair sums, then prove the necessary seven-row Gram is nonsingular by a split-prime minor whenever the open locus is nonempty.

If all three specialized coefficients vanish then \(v\) remains free. For these vertical components the parameter factor is checked to be linear or monic quadratic. Substitute its exact class for \(t\) in \(C_j,L_j\), then run the polynomial norm argument with \(v\) as free parameter. Any remaining finite parameter pair is tested with the tensor product of its two companion matrices. All 30 vertical components are excluded.

Across the 280 orientations there are 94 instances with no surviving parameter fibre, 96 inconsistent fibre cases, 60 empty open-locus cases, 32 Gram exclusions, and 30 vertical exclusions. A single orientation can contribute several fibre cases. This completes the exclusion of a containing support and proves disjointness. The seven-plane problem for disjoint supports remains open.
