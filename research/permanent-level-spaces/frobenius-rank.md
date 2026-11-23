# Frobenius rank on a translated permanent level

Let L be a complex linear space of m by n matrices, with 2≤n≤m. Suppose the rectangular permanent of the all-ones matrix plus X takes its value at the all-ones matrix for every X in L. Transposing gives the other shape convention. For the ordinary complex *bilinear* pairing

    B(X,Y) = Σᵢⱼ Xᵢⱼ Yᵢⱼ,

the rank of its restriction to L is at most m+n−2. In a 5 by 5 level space of dimension nine, a nonzero matrix with zero row and column sums must therefore pair to zero with the entire space. More generally the dimension of the subspace of such centered matrices is at least dim(L)−m−n+2.

The argument uses the first two coefficients of the permanent. The linear term shows every X in L has total entry sum zero. The polarized quadratic term shows that the sum of Xᵢⱼ Yₖₗ over i≠k and j≠l is zero. For Y with all margins zero, the excluded-row, excluded-column sum of entries of Y at (i,j) is Yᵢⱼ. Thus B(X,Y)=0 for every X in L. Send Y to all row sums except the first and all column sums except the first. The kernel consists of centered matrices, and lies in the radical of B on L. Rank-nullity gives the stated rank bound.

If L is closed under entrywise complex conjugation, a centered Y also pairs to zero with its own conjugate. The sum of the squared absolute values is zero, so Y=0 and dim(L)≤m+n−2. In size 5 by 5 this proves the requested bound eight under conjugation stability.

The project's earlier L-gct-158 already gives the real dimension bound by using the first two coefficients and the margin map. The statements here retain the radical inclusion over the complex numbers, where a nonzero matrix can have zero bilinear square. The Lean file uses the project's Minc expansion for the level-to-polarization step and checks the 5 by 5 injection-indexed formulation directly.

The standalone FrobeniusPermanent.lean was checked with Lean and Mathlib 4.36.0. The theorem audits for translated_rectangle, five_by_five, rectangular_gram and five_gram report only propext, Classical.choice and Quot.sound.

## Coefficient fields

Let K admit a field embedding into an ordered field R and also a possibly different embedding into ℂ. If U is a K-linear space of matrices whose entrywise complex image belongs to L, then dim_K(U)≤m+n−2. In particular a complex nine-dimensional five-by-five level space could have no basis over any orderable coefficient field. This includes number fields with a real place even when the chosen complex embedding is nonreal.

Indeed, a vector of U with zero margins maps to a vector in the radical over ℂ. Its bilinear square is zero. The equation is a sum of squares with coefficients in K. Transporting it to R forces every coordinate to vanish. Thus the margin map over K is injective. For the assertion about a complex basis, its vectors are also independent over the coefficient field. Conversely, a hypothetical nine-plane yields an explicit obstruction over its field of definition: a nonzero K-matrix Y with zero margins and ΣYᵢⱼ²=0. Dividing by any nonzero entry yields −1 as a sum of at most 24 squares in K.

OrderedField.lean imports FrobeniusPermanent.lean and proves ordered_coefficients and five_ordered_coefficients with the same three standard axioms. It makes the field embeddings explicit.
