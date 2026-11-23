# A maximal additive line on every square permanent level

For n≥2, let ω be a primitive n-th root of unity and choose c with cⁿ=−1. The line spanned by the additive matrix Dᵢⱼ=ωⁱ+cωʲ is inclusion-maximal among complex linear spaces of additive matrices Tᵢⱼ=uᵢ+vⱼ on which per(J+T)=n!, where J is the all-ones matrix and i,j range from zero to n−1. In particular D has no independent additive extension in any square size. All row and column offsets in the proof are centered. Their uniqueness on a level space follows from the linear coefficient, which forces the total entry sum to vanish.

## The normalized permanent

For additive offsets u,v, the normalized permanent of J+T is

    Σ_{i+j≤n} C(i,j) eᵢ(u)eⱼ(v),    C(i,j) = (n−i)!(n−j)!/[n!(n−i−j)!].

Indeed, fixing the i rows contributing a row offset and the j columns contributing a column offset means the permutation must avoid mapping one of those rows into one of those columns. Counting such permutations and dividing by n! gives C(i,j). For the proposed direction the elementary functions of both root lists vanish in degrees 1 through n−1, and the two terms in degree n cancel. Thus its line belongs to the level.

Suppose x,y are the centered row and column offsets of another direction in a linear level space containing D. In degree k, take the coefficient linear in that direction and of degree k−1 in D, for 2≤k≤n. Every term using both row and column offsets has a positive-degree undifferentiated elementary function below degree n and vanishes. Differentiating eₖ at a list of n-th roots gives (−1)ᵏ⁻¹Σᵢωⁱ⁽ᵏ⁻¹⁾xᵢ. The corresponding column derivative has the extra factor cᵏ⁻¹. Hence the Fourier coefficients of x and y satisfy yₜ=cᵗxₜ for 1≤t<n: at k−1=n−t the equation reads xₜ+cⁿ⁻ᵗyₜ=0. Constant Fourier coefficients vanish by centering.

Write X(z)=Σₜxₜzᵗ. Consequently the two lists are X(ωⁱ) and X(cωⁱ). After subtracting a multiple of D assume that the highest nonzero frequency t of X is at least two. We derive a contradiction.

## Isolating its highest frequency

Use λ for the coefficient of D and μ for that of the putative second direction. The rows are the samples of λz+μX(z) on zⁿ=1, and the columns are its samples on zⁿ=−1. Assign weight 1 to a λ term and weight s to a μ term of frequency s. Invariance under z↦ωz makes each monomial within a row elementary function have weight divisible by n. A column elementary function has the corresponding row coefficient multiplied by c raised to that weight. At total weight n the two pure elementary terms cancel. Every mixed row/column term of positive degrees has total weight at least 2n.

Choose b=⌊2n/t⌋ and a=2n−tb. Then a,b≥0, b>0, and a+b≤n. To check the last inequality write n=th+r, 0≤r<t. If 2r≥t then a+b=2r−t+2h+1≤n. If 2r<t then a+b=2r+2h≤n, since r≤h(t−2). The coefficient of λᵃμᵇ has maximum weight 2n. Only terms using the highest frequency t for every μ can contribute at that weight. Thus it suffices to show that this coefficient is nonzero for X(z)=zᵗ, after which the original coefficient is multiplied by xₜᵇ.

For nonnegative i,j with i+j>0 set H(i,j)=n·binom(i+j,j)/(i+j). In the formal logarithm of the row product ∏(1+λωᵏ+μωᵗᵏ), the coefficient of λⁱμʲ is (−1)ⁱ⁺ʲ⁻¹H(i,j) when n divides i+tj, and zero otherwise. This is the power series for log(1+z) and the finite root sum. At weight 2n only a single logarithmic term of weight 2n or a product of two terms of weight n is possible. Taking the exponential and inserting the constants C in the normalized permanent gives the following expression for the desired coefficient, up to the common sign (−1)ᵃ⁺ᵇ:

    −2H(a,b) + Σ (1−C(i+j,i′+j′)) H(i,j) H(i′,j′).

The sum is over ordered decompositions (a,b)=(i,j)+(i′,j′) with i+tj=i′+tj′=n. The two pure elementary terms contribute −2H(a,b) and the same sum with coefficient 1. The mixed terms contribute the negative C multiple because the column factor has weight n and cⁿ=−1.

If 2r≥t then b=2h+1, while in each half of weight n we would have j≤h. The sum is empty and the coefficient is nonzero. If 2r<t, the only decomposition is (i,j)=(i′,j′)=(r,h). Put l=r+h. Since also a=2r, b=2h, positivity of the expression reduces to

    (n/l) [1−binom(n−l,l)/binom(n,l)] > binom(2l,2h)/binom(l,h)².       (1)

When r=0 the right side is 1. Here l=h≥2 because t<n. A uniformly random l-subset hits a fixed l-subset with probability strictly greater than the chance l/n of containing one fixed member. This proves (1).

## The comparison when r>0

Let X be the size of the intersection of a uniform l-subset with a fixed l-subset of an n-set. Its first moment is l²/n and its second factorial moment is l²(l−1)²/[n(n−1)]. Cauchy–Schwarz gives

    (n/l) Pr(X>0) > l(n−1)/[n−1+(l−1)²].

The inequality is strict because l≥2 and n≥2l, and positive intersection sizes of both one and two occur. The lower bound increases with n. Write p=hr. Since t≥2r+1 in this case, n≥2p+l.

On the right of (1), Vandermonde's identity gives a central term 1 and twice the sum of the successive terms to one side. The first term is x=p/[(h+1)(r+1)]. Each later successive ratio is at most y=(h−1)(r−1)/[(h+2)(r+2)]. Consequently the right side is at most

    1+2x/(1−y) = 1 + 2p(p+2l+4)/[3(l+1)(p+l+1)].

This upper bound is at most l(2p+l−1)/[2p+l(l−1)], the previous lower bound evaluated at n=2p+l. After clearing positive factors this is equivalent to

    −2p²+(2l²−3l−11)p+(l−1)(l²+2l+3) ≥ 0.

For l≥4 use p≤l²/4 and (3/2)l²−3l−11≥1. At l=2 we have p=1 and equality. At l=3 we have p=2 and a strict inequality. This completes (1), excludes the highest nonzero frequency t≥2, and proves the asserted maximality.
