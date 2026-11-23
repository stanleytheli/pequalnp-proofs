# A two-coordinate row normal on the complex 4 by 5 permanent level

Let \(P\) be the rectangular permanent on four rows and five columns, and let \(J\) be the all-ones matrix. Suppose \(P(J+X)=120\) on a seven-dimensional complex linear space \(L\), every pair of row projections is injective on \(L\), and all four row projections have rank four. If three row normals have full support, the fourth cannot be supported on exactly two coordinates. Combined with the [size-three/four obstruction](sparse-row-obstruction.md) and the [full-support obstruction](full-row-obstruction.md), the only remaining case with at least three full-support normals has a fourth normal supported on one coordinate. These hypotheses are essential to the scope of this result.

Use the [sparse/high pair classification](sparse-high-pair.md) and the notation of the [size-three/four calculation](sparse-row-obstruction.md). Enumerate the same phase configurations with the two active columns \(S=\{0,1\}\), using all admissible ordered pairs \(P,Q\) for each common-ratio pair. There are 667,352 orientations. The exact pair-projection test retains 97,472. Distinct high-row phase orientations with the same low pair groups are included. The program aggregates columns only when both phases and group memberships agree.

Of the retained orientations, 96,752 have at least \(n-1\) weight conics in \(n\) aggregate coordinates. The finite dual-space method and split-column pencils are described in the [preceding case](sparse-row-obstruction.md). Its degree threshold routes the cases to a checker; it is not used as a geometric dimension assertion. Two of the routed orientations require the additional split-independent calculation below. The remaining 720 have five aggregate coordinates, two common-ratio sparse/high pairs, one two-group sparse/high pair, and only sign pairs among the three full normals.

## Three conics in four affine variables

Normalize the sparse row total to one. Write \(x_2,x_3,x_4\) for the three missing weights, \(e_{kj}=\pm1\) for the corresponding high phases, and choose a high row \(k\) with common ratio on the active columns. Its unnormalized active total equals one. For the chosen nonempty disjoint missing groups \(P,Q\), let \(R=T\setminus(P\cup Q)\) and let \(p,q,r\) denote their signed totals. The affine conic for this pair is
\[
                     p(p+q+r)=1+r.                              \tag{1}
\]
Indeed the relevant high row total is \(1+p+q+r\); multiply the affine normalization from the sparse/high classification by its nonzero denominator.

Set \(t=p+q+r\). For fixed \(t\), the total equation and \(tp-r=1\) are linear in the three missing coordinates. If \(R\ne\varnothing\), choosing one coordinate from each of \(Q,R\) as pivots gives a nonzero constant determinant. If \(R\) is empty, choose pivots in \(P,Q\), with determinant a unit times \(t\). The case \(t=0\) then contradicts (1). In both cases the missing weights are \(C_j(t)+L_j(t)v\) for a free coordinate \(v\). The second common-ratio conic is
\[
                 g_2(t)v^2+g_1(t)v+g_0(t)=0.                    \tag{2}
\]
The two possible choices of first common-ratio row are equivalent. The verifier chooses a presentation with smaller degree in \(v\) or an exactly split quadratic when possible.

For the remaining high row, let \(y\) be the signed total of its two active positions, let \(s(t,v)\) be its signed missing total, and let \(h=\pm1\) be the sparse/high phase ratio on its first sign group. Its conic is
\[
              z=hy-1,\qquad z^2+hs(t,v)z=2.                     \tag{3}
\]
The two active coordinates can now be recovered linearly. If the sparse phase at the second position is \(d=\pm1\), their weights are \((1+y)/2\) and \(d(1-y)/2\).

## Integral norms and finite parameter values

Clear the denominators of (2) and record the common polynomial content of its coefficients before dividing it out. Away from its roots and the zeros of the leading coefficient, a linear or rationally split equation supplies explicit rational functions for \(v\). Otherwise, replace \(v\) by the integral coordinate \(b=g_2v\), giving
\[
                 b^2+g_1 b+g_2g_0=0 .
\]
Here \(g_i\) are the polynomial coefficients after removing common content. Clear a common denominator \(D(t)\) of all missing weights in the basis \(1,b\). Replacing \(z\) by \(c=Dz\) turns (3) into a monic quadratic
\[
                 c^2+(A(t)+B(t)b)c-2D(t)^2=0.
\]
The known denominator zeros are among \(t=0\) and the leading-coefficient zeros just retained. When a quadratic with polynomial coefficients splits rationally, the verifier certifies the polynomial square and checks both root choices. All five physical weights, up to common scaling, now have integer-polynomial coefficients in the basis \(1,b,c,bc\), omitting unused generators.

For an integer seven-row projection \(U\) compute the exact determinant of \(U F K F^t U^t\) over this algebra and take the successive monic quadratic norms. The norm of \(x+y b\) for \(b^2+G b+H=0\) is \(x^2-Gxy+Hy^2\), with the same formula for the other extension. The resulting polynomial lies in \(\mathbb Z[t]\), including when specialized roots coincide. A valid solution makes every projected determinant zero on its sheet and hence every norm zero.

The verifier recovers the integer polynomials from a single packed evaluation with a rigorous coefficient bound. On \(|t|=1\) the modulus of a polynomial is bounded by the sum of its absolute coefficients. A root of a monic quadratic \(X^2+GX+H\) has modulus at most \(1+\max(|G|,|H|)\). Apply this successively to bound every sheet of \(b,c\), then bound every physical weight in modulus by \(W\ge1\). The integer inverse metric has entries of modulus at most six. In each of the seven projected rows the coefficients have modulus at most 77 times, respectively, \(1,W,5W^2\) for degrees zero, one and two. If the projection uses \(n_1,n_2\) rows of positive degrees one and two, its determinant has modulus at most
\[
          7!\,(20^2\,6\,77^2)^7\,5^{2n_2}\,W^{2(n_1+2n_2)}.
\]
Raise this bound to the number of sheets for the norm. Cauchy's coefficient inequality bounds the magnitude of every individual integer coefficient by the same number. For a power of two \(B\) greater than twice this bound, evaluation at \(B\) followed by balanced base-\(B\) expansion therefore recovers every signed coefficient exactly. The method operates on arbitrary-precision integers.

A chart with an identically zero required factor is empty. Otherwise the program obtains a nonzero norm and takes square-free gcds of further projected norms. Rational polynomial gcds are reconstructed with modular degree upper bounds and verified by exact division into both arguments. The union of the resulting root sets, \(t=0\), the common-content roots and the leading-coefficient roots contains the parameter at every valid point. If (2) has degree zero after removing its content it contributes no generic branch. The procedure obtains such a finite set in all 720 orientations.

## Exceptional fibers

At the roots of each square-free parameter polynomial \(f(t)\), work in \(\mathbb Q[t]/f\). Split \(f\) by exact gcds with the three **original** coefficients in (2), before the removal of common content. On each resulting factor, the specialized degree in \(v\) is known. An invertible constant equation is inconsistent. In the linear and quadratic cases, form the corresponding companion multiplication matrices, retaining (3) as a further monic quadratic. All denominators inverted in a quotient have certified inverses by the Euclidean algorithm. The argument also permits reducible \(f\); every complex evaluation of the defining polynomials supplies a common left eigenvector on the associated monomial basis.

Clear scalar denominators in the coordinate matrices. Restrict to the open set by the product of all necessary nonzero forms, using the checked image and multiplication identities of the [finite dual-space proof](full-row-obstruction.md). The verifier either proves that this product is nilpotent or exhibits an invertible projected seven-row block Gram at a prime. Either outcome excludes all admissible common evaluations. The sparse-row sum normalization rules out \(t=-1\) because the first common-ratio high row would have sum zero.

In 60 orientations an exceptional factor makes every coefficient of (2) zero. Here \(v\) is free and must be checked separately. The factors are \(t-1\), \(t^2-t-1\), \(t^2+t-1\), or \(t^2-2\). Treat \(t\) as a constant algebraic generator on that factor and use \(v\) as the univariate parameter. The missing masses are affine in \(v\), equation (3) is monic after clearing constant denominators, and the same exact norm procedure applies. Each of these 60 component checks has constant gcd of projected norms or an identically zero required factor. The verifier matches the exceptional components directly as it encounters them.

## The two split-independent cases

Each of the two remaining finite-route cases has three common-ratio sparse/high pairs and one repeated pair of active phase columns. Let \(t\) be the signed missing total of a first common-ratio pair. Use its section as in (1). The other two conics are both quadratic in \(v\), but their difference is linear. Its constant and linear coefficients are coprime in \(\mathbb Q[t]\), which the verifier checks. Hence every solution is given by an explicit rational \(v(t)\) on the section chart. Substitution is checked in both original conics.

The two active weights have known total and an arbitrary antisymmetric split. The seven following tangent covectors are independent of that split as vectors. Use the total sum, the three common-ratio pair covectors on missing positions, and the three corrected high/high pair covectors. For each high pair, add \(s_k F_i-s_i F_k\) to its sign-pair covector, where \(F_i\) is the row-\(i\) normal covector. The sign phases agree on both active positions, so the corrected vector has zero entries there. Every one of these seven covectors is invariant under interchanging the two active columns. The same holds after applying \(K\). Pairing any of these covectors with any of the eleven original constraints is therefore independent of the antisymmetric split, because varying a constraint gives opposite entries on those columns in each row. All seven-by-seven minors of this seven-by-eleven matrix must vanish at a solution. The verifier computes the minors as polynomials in \(t\) at the equal split by integer Newton interpolation, removes exactly dividing factors known to be nonzero, and obtains a constant gcd in both cases.

These checks exhaust the support-two configurations and establish the theorem.
