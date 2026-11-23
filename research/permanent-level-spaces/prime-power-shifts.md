# Constant permanent on spaces with row or column translation symmetry

Let a finite abelian group G of order q act regularly on the q columns of an r by q complex matrix. Assume r ≤ q, and let L be a linear space invariant under these translations. If the translated rectangular permanent (the sum over injections of the row indices into distinct columns) is constant on J + L, then dim L ≤ q−1 whenever r ≤ pᵃ for some prime power pᵃ dividing q. In particular this gives the bound for square matrices for every finite abelian p-group in its regular action. Transposition gives the corresponding row statement for square matrices.

The argument extends the project's proposed prime-order cyclic case, L-gct-211. The nonvanishing used here agrees, for cyclic groups of prime-power order, with Hugh Thomas's theorem on the monomial support of the generic circulant determinant. The argument below works directly with characters and does not require cyclicity. [Thomas, 2004](https://arxiv.org/abs/math/0301048)

## The injective character sum

For d ≤ r, let χ₁,…,χ_d be characters of G. Define I as the sum of χ₁(g₁)⋯χ_d(g_d) over ordered tuples of distinct elements of G. A simultaneous translation shows that I vanishes if the product character is nontrivial. If the product character is trivial, inclusion-exclusion over set partitions writes I as a sum of integers. Only partitions on which the product of the characters on each block is trivial contribute. Such a partition with m blocks of sizes b₁,…,b_m contributes

    (−1)^(d−m) q^m ∏ (b_i−1)!.

One can obtain this formula by multiplying out the alternating sum over permutations of d labels, imposing equality on every cycle. At a tuple with repeated elements the signs cancel in its nontrivial stabilizer. A tuple of distinct elements contributes only the identity permutation.

Take a = v_p(q), with d ≤ pᵃ and a ≥ 1. The one-block partition contributes ±q(d−1)!. Its p-adic valuation is strictly smaller than that of every other contributing partition. For positive b,c with b+c ≤ d, Legendre's formula gives

    v_p((b+c−1)!) − v_p((b−1)!) − v_p((c−1)!) ≤ a−1.

Each floor difference is zero or one. Terms with pʲ > b+c−1 vanish and b+c−1 < pᵃ. Merging m blocks to one uses m−1 such inequalities, whereas the extra q factors supply a(m−1) powers of p. The valuation gap is at least m−1. The one-block term therefore survives, so I is nonzero.

## Application to level spaces

Decompose L into character spaces for the column translations. A matrix in one character space has the form u(i)χ(g), for a vector u on the r rows. Polarize the constant-permanent identity in d such directions. Up to the nonzero factor (q−d)!/(q−r)!, the multilinear coefficient is the product of the injective character sum and the sum of ∏u_h(i_h) over distinct row indices. It vanishes. Whenever the product character is trivial, the preceding argument forces the row factor to vanish.

Now consider the simpler polynomial Σ_g ∏_i(1+X_ig). In the same d directions its multilinear coefficient is the same row factor times the unrestricted sum of the product character on G. For a nontrivial product character the unrestricted sum is zero. For a trivial one the row factor is zero. All positive-degree coefficients vanish on L, by multilinearity and the character-space decomposition. At X = 0 the polynomial has value q.

On V = L + ℂJ, homogenizing gives Σ_g ∏_i Y_ig = q λ(Y)^r, where λ(X+cJ) = c. Here r ≥ 1, so J is outside L and λ extends to the ambient space. The project's checked column-product bound L-gct-175 gives dim V ≤ q. The case r = 0 is immediate.

For q divisible by different primes the size restriction on r can matter: corresponding cyclic determinant coefficients can vanish for some zero-weight multisets outside the prime-power range. [Colarte, Mezzetti, Miró-Roig and Salat, 2019](https://arxiv.org/abs/1806.05905)
