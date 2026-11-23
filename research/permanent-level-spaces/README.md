# Linear spaces in levels of the translated permanent

These results concern the project’s geometric-complexity question L-gct-086. For the all-ones matrix J, the general question asks whether every complex linear L with per(J+T)=per(J) has dimension at most Cn. The results below establish bounds and classifications under specified hypotheses and narrow two finite searches.

| Hypothesis | Conclusion | Reproduction |
|---|---|---|
| Regular abelian action on m rows, q≤m columns, and q at most a prime power pᵃ dividing m | Dimension at most m−1. Includes square matrices for all abelian p-groups | PrimePowerPermanent.lean and prime-power-shifts.md |
| Regular abelian row action annihilated by e | Dimension at most (m−1)(e−1) | BoundedExponentPermanent.lean and bounded-exponent.md |
| Doubly transitive action on m rows, q≤m | Every nonzero invariant level space is the whole centered subspace in one column. Its dimension is m−1 | DoubleTransitivePermanent.lean and double-transitive.md |
| Independent regular abelian row action and transitive column action on a square matrix | The level space is zero | TwoSidedPermanent.lean and bounded-exponent.md |
| Rank-one family of matrices whose row factors are all n-th roots of unity and whose column factor vanishes in one fixed coordinate | This (n−1)-dimensional family is inclusion-maximal among all level spaces, for every n≥2 | MaximalRootFamily.lean |
| A 4×5 space contains a whole centered column | Dimension at most six, attained | centered-column-bound.md |
| A 5×5 space contains a whole centered row or column | Dimension at most seven | centered-row-bound.md. FiveByFiveGram.lean checks the projected cofactor and Gram-rank obstruction |
| Matrices of the form Tᵢⱼ=uᵢ+vⱼ inside a 4×5 level space | At most one independent such direction, attained | additive-pencil-proof.md, additive_plane_certificate.py and review_pencil_extension.py |
| Additive directions in a 5×5 space | At most two independent directions | square-additive-moments.md |
| Seven-dimensional 4×5 space satisfying all positive-degree conditions through degree three | Its permanent is 120−24abcd. Every actual level subspace in this family has dimension at most six | FourByFiveNearWitness.lean |

The general additive-direction argument for square and adjacent rectangular sizes is in additive-directions.md. A quantitative bound for arbitrary rectangles with at least four rows is in rectangular-additive-moments.md. The five-by-five and four-by-five dimension bounds stated in the manuscripts include paper arguments. The sharp additive four-by-five bound also uses an exact finite-field calculation. The independent quadratic-extension check verifies the two exceptional nonzero parameters.

## Reproduce

The Lean files are standalone over official Mathlib and were checked with Lean 4.36.0. Check them individually in a matching Mathlib workspace, for example with lake env lean DoubleTransitivePermanent.lean. Each file includes its necessary definitions; several share helper names. Their main theorem audits report only propext, Classical.choice and Quot.sound. The finite-field checks use Python's standard library.

    python3 additive_plane_certificate.py
    python3 review_pencil_extension.py

The permanent expansion and the column-product and transversal bounds in the formal files adapt project developments from brilliant-hq/pequalnp-proofs, including the Minc expansion and checked L-gct-171 and L-gct-175. The algebraic results here do not depend on a proposed resolution of P versus NP.

## Further classifications

RankOneLevels.lean proves that a square level space consisting entirely of matrices of rank at most one has dimension at most n−1. In the equality case, up to transpose there are exactly two families, described in rank-one-classification.md.

The line with additive entries ωⁱ+cωʲ, where ω is a primitive n-th root and cⁿ=−1, is inclusion-maximal inside the additive part of the square level for every n≥2. The proof is in maximal-additive-root-line.md. The auxiliary check_root_line.py independently computes its decisive coefficients from the original permanent in sizes 3 through 11. A separate finite-interpolation argument in moment-line.md excludes higher-dimensional additive spaces whose low row moments vanish. For the 5×5 additive two-plane search this rules out an identically zero row Gram form.

The 4×5 finite search has another obstruction. A space containing a nonzero variation constant down each column has dimension at most six. The proof in pure-column-shift-proof.md combines a complex vector-bundle argument with an exact finite-field certificate. The independent reviewer recalculated the derivatives from the 120 summands of the rectangular permanent and checked all 40 geometric candidates.

    python3 pure_column_shift_certificate.py
    python3 review_pure_shift.py
    python3 check_root_line.py

## Frobenius rank over the complex numbers

FrobeniusPermanent.lean bounds the rank of the ordinary bilinear Frobenius pairing on any translated rectangular permanent level space by m+n−2. If the space is closed under conjugation, its dimension has the same bound. The five-by-five specializations use the desk's permanent expression directly. The proof and its relation to the project's real result L-gct-158 are in frobenius-rank.md.

OrderedField.lean also proves the dimension bound over any coefficient field that embeds in an ordered field, including a number field with a real embedding different from the chosen embedding into the complex numbers. Compile FrobeniusPermanent.lean to a local .olean first, then include that directory on LEAN_PATH.
