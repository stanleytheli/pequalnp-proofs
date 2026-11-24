# How much repeated use a corner-counting projection would need

Grochow's Open Question 5.2 asks whether a polynomial-size monotone permanent projection could count the Hamiltonian-cycle polynomial or the nonbipartite perfect-matching polynomial exactly on all Boolean inputs. The question allows a monomial to repeat an input variable: x and x^a agree on Boolean inputs for every positive a. The following bounds quantify how severely some repetitions would have to occur in such a projection. They leave the general corner question open. [Grochow, Open Question 5.2](https://toc.cs.uchicago.edu/articles/v013a018/v013a018.pdf)

Let F be a homogeneous multilinear polynomial of degree h with positive coefficients on its monomials. A monotone affine substitution into a k×k permanent gives a polynomial P with nonnegative coefficients. Assume P and F agree on the whole Boolean cube. Replacing every positive exponent in P by one gives a multilinear polynomial with exactly the same corner values. Uniqueness of interpolation implies that this reduced polynomial is F. Consequently every positive labeled perfect matching of the source uses exactly h distinct variables forming the support of some F-monomial, and every support in F occurs. A labeled matching chooses one nonzero term per matched matrix entry; nonnegative constants count as choices of degree zero.

For a support S of F define e(S) to be the smallest, over its source realizations, of the total number of variable occurrences minus h. Write R=max_S e(S). For n target variables the following bound holds for an absolute constant C:

    xc(Newt(F)) ≤ [C(1+k²(n+1))]^{2R+O(1)}.

Here xc counts linear inequalities in an extended formulation. For a simple projection (one variable or constant per entry) replace k²(n+1) by k²+1. Thus if F is either the m-city Hamiltonian or the m-vertex nonbipartite perfect-matching polynomial and k is polynomial in m, some target monomial forces Ω(m/log m) repeated occurrences in **every** source realization of that monomial.

## A union of small extended formulations

Use a bipartite multigraph with one labeled copy of each source edge for every term of its entry. There are L≤k²(n+1) such copies. The convex hull of its perfect matchings is given by nonnegativity and row/column sums equal to one, hence has O(L+k) inequalities and equations.

Consider all ordered pairs of subcollections (D,K) of labeled edges such that |D|≤R and |K|≤|D|. The letters designate occurrences to delete from the exponent vector and keeper occurrences. Require the union D∪K to be a matching, containing distinct labeled edges, and all its labels to be variables. For every variable occurring on D require exactly one occurrence of the same label on K, and no other labels on K. The empty pair is allowed. Enforce all these edges in the matching, a coordinate face of its polytope. On this face count the variable occurrences excluding D. Each matching still uses every one of its original h distinct variables: if a deleted occurrence had variable i, a forced keeper with variable i remains. Therefore this count is ≥h for every matching. Equality to h exposes another face, if nonempty. On that subface the exponents outside D are exactly the zero/one indicators of the support. Linear projection by summing these remaining labels hence maps this face into Newt(F).

Conversely for every support choose a source matching attaining e(S)≤R. For each repeated label mark one occurrence as keeper and put its remaining occurrences into D. These pins yield one of the enumerated pairs. The matching lies in its equality face and yields exactly the desired vertex of Newt(F). Thus the convex hull of the union of the projected faces is Newt(F). There are at most (L+1)^{2R+O(1)} pairs and each face has an O(L+k)-size formulation. The convex hull of a finite union of bounded nonempty polytopes can be expressed by one block of variables per polytope: multiply its defining right-hand sides by an auxiliary λ≥0, require Σλ=1, and add the scaled image vectors. At λ=0 the bounded polytope's trivial recession cone forces a zero block. This proves the bound. Constants can be ignored in the exponent projection. An overall positive scalar also has no effect on the argument.

## One interior test and a quantitative consequence

There is a simpler criterion for exactness. At any strictly interior y∈(0,1)^n, replacing each positive exponent in a monomial of P by one weakly increases its value, and strictly increases it if a variable repeats. Since all coefficients are nonnegative, equality P(y)=F(y) at just one such y, in addition to exact Boolean corner counting, forces P to equal F as a formal polynomial. Grochow's exponential lower bounds then apply directly. A merely finite or positive value at y carries no such conclusion.

For each h-element support S of F take the input x=ρ 1_S for 0<ρ<1. No other h-element support is contained in S, so only the realizations of S survive. Their total coefficient equals the coefficient of S in F, by the corner argument. Therefore

    P(ρ 1_S)/F(ρ 1_S) ≤ ρ^{e(S)}.

In a hypothetical polynomial-order Boolean-corner counting projection for either target above, for every fixed ρ∈(0,1) some single tour or perfect matching would exhibit a deficit by a factor exp(Ω(m/log m)). This is a conditional obstruction to extrapolating a Boolean-corner construction to a fixed non-Boolean layer. It does not assume unknown Boolean complexity-class separations.
