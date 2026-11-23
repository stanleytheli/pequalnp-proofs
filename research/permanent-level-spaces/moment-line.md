# Zero low-order row moments force a single additive direction

Let J be the all-ones square matrix of size n≥2, and let W be a complex linear space of additive matrices Tᵢⱼ=uᵢ+vⱼ on which per(J+T)=n!. Use the unique centered row and column offsets, so both coordinate sums are zero. Suppose the elementary symmetric functions eₖ(u) vanish throughout W for 1≤k≤⌊n/2⌋. Then dim W≤1.

In particular a two-dimensional additive subspace of a 5×5 permanent level space must have a nonzero row Gram form. The same conclusion holds for 4×4. In these two sizes the additional hypothesis on u is simply that Σuᵢ²=0 throughout W.

## The joint moments

The degree-k component of the normalized square permanent on additive offsets is a sum over a+b=k of numerical multiples of eₐ(u)eᵦ(v). Both pure terms have coefficient one. To see this, select the rows and columns contributing the row and column offsets in a permutation, then count the permutations completing each choice. The pure row and column formulas follow directly from the product ∏(1+uᵢ) and its column counterpart.

Put h=⌊n/2⌋. By hypothesis both the degree-k identity and eₖ(u)=0 give eₖ(v)=0 for k≤h, since every mixed term includes a positive row degree ≤h. At all remaining k≤n, each mixed summand still contains a row or column degree between 1 and h. Thus eₖ(u)+eₖ(v)=0 for every positive k≤n. Newton's identities now give pₖ(u)+pₖ(v)=0 for all these k, where pₖ is the sum of k-th powers. Indeed the low-order power sums vanish separately, and a product of two elementary or power sums both of degree greater than h has degree greater than n.

Regard the 2n coordinate evaluations on W as points of the dual vector space W*. For each k≤n the sum of their k-th powers at every w∈W vanishes. Polarization therefore shows that the sum of a polynomial over the 2n evaluation points equals 2n times its value at the origin for every polynomial of total degree at most n. Collect coincident points, and subtract 2n at the origin. If W is nonzero, every resulting coefficient is nonzero. Each nonzero point has positive integer multiplicity, and the coefficient at zero is the negative of the number of nonzero coordinate evaluations counted with multiplicity. This gives a relation supported on at most 2n+1 distinct points, including zero.

## A finite interpolation bound

Suppose a set of at most 2d+1 distinct points in a complex affine space supports a relation with all coefficients nonzero that annihilates every polynomial of degree at most d. Then the points are collinear.

Fix a point p. Partition the other points by their lines through p. If each class has size at most d, pad the list to 2d entries with individual dummy entries and order entries from each class consecutively. Pair positions i and i+d for 1≤i≤d. No pair contains two actual points from the same class. The affine span of each remaining pair or singleton avoids p, so there is an affine linear form vanishing on that pair or singleton and nonzero at p. Ignore entirely empty pairs. The product of these at most d forms vanishes at every other point and is nonzero at p, contradicting the relation. Hence a line through each p contains at least d+2 members of the set. Two distinct lines of this size would have a union of at least 2d+3 points. They must all be the same line.

Apply this fact with d=n. All coordinate evaluations lie on a single line through zero. They span W*, since they separate the vectors in W. Therefore dim W≤1.
