# Sharp tensor-tree width under numerical approximation

Consider the same subcubic graph obtained by replacing each edge of the expander-overlay core by a long path. Write g for the number of base edges. There are Θ(m²) of them for Hamiltonian order m, and the number of physical vertices is Θ(gL) when the path length is L. Write Q for the canonical multilinear polynomial of the indicator of an independent set, and E=1−Q for edge detection. A binary tensor tree has one physical index of dimension two per vertex, arbitrary real internal tensors and one output. Its cost here is its largest bond dimension, minimized over all trees. With real inputs p, evaluate the vertex leaf on (1−p,p). An assertion on the cube means uniformly on all of [0,1]ᴺ, including its Boolean corners.

For any fixed 0<ε<1/2, the optimal maximum bond dimensions are as follows. Constants in the exponents can depend on ε and the expansion bound, and are independent of the subdivision length.

| Required accuracy on the cube | Q, the probability of no edge | E, the probability of an edge |
|---|---|---|
| Exact | 2^Θ(g) | 2^Θ(g) |
| Absolute error ≤ε | 2^Θ(√g) | 2^Θ(√g) |
| Relative error ≤ε times the target | 2^Θ(g) | 2^Θ(√g) |

The upper bounds are for signed real tensor entries. The approximate upper bound is an existence and randomized sampling construction. It holds already for a tensor train, the special case of a tree which reads its inputs in sequence. The estimates concern errors in values of the represented functions. The Boolean inputs alone suffice for all the lower bounds.

## Lower bounds from a matching

Every binary tree has an edge dividing its N leaves into parts of sizes between N/3 and 2N/3 (take a centroid, then its largest branch). The graph-cut proof in the companion note supplies an induced crossing matching of k=Ω(g) edges. Fix all other bits to zero. The table of Q on the remaining bits is DISJₖ(A,B)=[A∩B=∅]. A tree of maximum bond D has matrix rank at most D across this edge, including after the restriction.

For multiplicative approximation to Q, index the columns by complements of subsets B'. The forced-zero pattern permits a nonzero entry only when A⊆B', and every diagonal value is positive. Ordering the subsets by a linear extension of inclusion produces a triangular matrix with a nonzero diagonal. Its rank is exactly 2ᵏ. The same proof works with merely exact zero versus nonzero support, over any field, for the Boolean values of Q.

For fixed additive error ε the real approximate rank of DISJₖ is at least 2^Ωε(√k). One can see the precise reduction from Sherstov's pattern-matrix theorem. Let t=⌊k/4⌋. Alice has two Boolean bits in each of t blocks. For each bit reserve two matching coordinates and put that bit and its complement there on Alice's side. Bob selects one coordinate in each block to choose one of its two bits and an arbitrary polarity. Intersecting the selected coordinates occurs exactly when the OR of the t chosen, optionally flipped bits is true. This embeds the (2t,t)-pattern matrix of signed OR in the signed version of DISJₖ, up to a sign. An additive ε approximation to a 0/1 table yields a sign-table approximation with error 2ε and rank at most one larger. Apply Theorem 1.4 with any fixed accuracy parameter strictly between 2ε and 1. The approximate degree of OR at that accuracy is Ω(√t). Complementing a 0/1 target costs a rank-one matrix, so the same bound holds for E. [Sherstov, The Pattern Matrix Method, Theorem 1.4](https://doi.org/10.1137/080733644) [Paturi, On the degree of polynomials that approximate symmetric Boolean functions](https://doi.org/10.1145/129712.129758)

## A matching upper bound that does not grow with path length

For a Boolean physical input, write bᵢ for the indicator that physical path i contains some edge with both ends occupied, including its two end edges. The vectors b share root bits. Their OR is nevertheless exactly E. When g≥2 and w=Σbᵢ, take

    P(b) = 1 − T_d((g+1−2w)/(g−1)) / T_d((g+1)/(g−1)).

Here T_d is the Chebyshev polynomial. P(0)=0. For 1≤w≤g, the inner argument is in [−1,1]. The denominator is cosh(d·arcosh(1+2/(g−1))). Taking d=Oε(√g) makes the maximum error at positive weights at most ε/2. The case g=1 uses P(b)=b.

Reduce bᵢ² to bᵢ, which preserves all Boolean values and cannot increase the sum of absolute coefficients. The affine argument inside T_d has coefficient mass at most 7, including its constant. The recurrence T_{j+1}=2xT_j−T_{j−1} now bounds the coefficient mass of T_d of this argument by 15ᵈ. The denominator exceeds one. Hence P has total mass W≤1+15ᵈ, degree at most d and constant coefficient exactly zero.

Draw a nonconstant monomial with probability proportional to its absolute coefficient. Give its evaluation the value W times the sign of its coefficient. Its mean is P(b) for every b and its magnitude is at most W. The average of O(W²(g+1)/ε²) independent draws has sampling error at most ε/2 simultaneously on all 2ᵍ bit strings with positive probability, by Hoeffding's inequality and a union bound. Each sampled monomial vanishes on b=0. Sampling bounded features according to coefficient mass is classical. [Bruck and Smolensky](https://doi.org/10.1137/0221003) [Sherstov on approximate inclusion–exclusion](https://web.cs.ucla.edu/~sherstov/pdf/incl-excl.pdf)

The resulting signed sum therefore approximates E *relatively* on every Boolean input, with at most 2^Oε(√g) terms of degree at most d.

Use the same variable order for every term. Read all root bits, then process the interior bits one path at a time in path order. To evaluate a term retain the bits of the endpoints of its selected paths, at most 2d of them. The first path bit is its retained left endpoint. Scanning the interior needs a previous-bit flag and an occupied-edge-seen flag. Test the last pair against the stored right endpoint and accumulate the AND over the selected paths. All other paths can be ignored. The path position is fixed by the tensor-train layer. These machines have at most a constant times 2²ᵈ states each. A direct sum of the machines, with their signed coefficients at the output, has bond at most 2^Oε(√g). Subtracting this approximant from 1 gives an additive approximation of Q with the same asymptotic bond.

Finally apply the two Bernoulli weights at every individual physical leaf. This averages the Boolean approximation over independently selected *vertices*, preserving dependencies of different path flags through their common endpoints. If A approximates E relatively on the Boolean cube, then |𝔼[A]−𝔼[E]|≤𝔼[|A−E|]≤ε𝔼[E] on the entire continuous cube. Additive errors transfer by the same argument. The exact construction in the companion note supplies the relative upper bound for Q.

The induced-matching obstruction and the Chebyshev, sampling and pattern-matrix ingredients have prior uses. The conclusions here concern this particular read-two family together with its arithmetic specialization, including the differing behavior of complementary events under relative accuracy. Priority for that combination has not been established.
