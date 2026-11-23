# Extremal linear spaces of rank-one matrices

Let L be a complex linear space of n×n matrices of rank at most one, where n≥2. Assume per(J+T)=n! throughout L. Then dim L≤n−1. Up to transposition, every space of dimension n−1 is one of the following.

* All centered vectors in one row.
* All matrices u vᵀ, where u is a nonzero scalar times the n distinct n-th roots of unity in some order, and v is arbitrary subject to vanishing in one fixed coordinate.

Both families attain dimension n−1. The second family is also maximal among all translated permanent level spaces, even when higher ranks are admitted, as proved separately in MaximalRootFamily.lean.

## Proof

A nonzero linear space of rank-at-most-one matrices has a common left factor or a common right factor. Indeed the sum of two rank-one matrices with independent left factors and independent right factors has a nonzero two-by-two minor. Fix a nonzero member. All space members must thus share its left or right factor. The union of two proper linear subspaces cannot contain a vector space unless one already contains it. Transpose if necessary and write L as all u vᵀ, with fixed nonzero u and v in a subspace V of column factors.

The degree-k coefficient of per(J+t u vᵀ) is a positive constant times eₖ(u)eₖ(v). If s is the support size of v, then eₛ(v) is the product of its nonzero entries. Thus every positive support size appearing in V is an index k for which eₖ(u)=0.

Over the complex numbers, a d-dimensional vector space of column vectors realizes at least d different positive support sizes. To see this, use d independent coordinate projections, and successively allow one more of them to be nonzero. The union of possible supports strictly increases at each step. In each resulting subspace a single vector realizes that union, since a finite union of proper hyperplanes cannot cover a complex vector space. At the support size of u its own elementary function is nonzero. This proves dim V≤n−1, and more generally bounds the dimension of each common-factor family by the number of zero elementary functions of u.

A hyperplane in n coordinates realizes every intermediate support size 2≤k<n. If its defining linear equation has at most one nonzero coefficient, take k coordinates outside that coefficient. Otherwise choose k coordinates containing two nonzero coefficients. On those coordinates the same equation permits every coordinate separately to be nonzero. The finite-union argument gives a solution nonzero at all k simultaneously. The formal file gives a separate proof using the support-size bound and a codimension-one section.

When dim V=n−1, the support of u therefore has either one element or n. For a one-coordinate u, the degree-one condition gives Σvᵢ=0 for every v, determining V. For a full-support u, the top coefficient gives ∏vᵢ=0 on V, so V is one of the coordinate hyperplanes. Such a hyperplane realizes every positive support size below n, hence e₁(u),…,eₙ₋₁(u) all vanish. The monic polynomial whose n roots are the entries of u is therefore Xⁿ+c with c≠0. Its roots are distinct and form the stated scaled root family.

RankOneLevels.lean checks the upper bound and classification with the ordinary matrix rank and permanent. The checked conclusion records the elementary-function vanishing characterizing the root profile. Its main theorem is RankOneLevels.square_rank_one_classification. The rectangular, fixed-profile dimension bound is RankOneLevels.spectral_dimension.
