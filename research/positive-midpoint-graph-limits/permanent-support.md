# The bipartite graph size for perfect-matching support has exponent 3/2

Let b(m) be the minimum number of vertices in a bipartite graph whose no-edge probability, after cube-preserving real affine input substitutions and a positive rescaling at each stage, has finite Boolean limits with positive support exactly on m×m matrices admitting a perfect matching. Assume the scaled no-edge probability is bounded at the cube midpoint. Arbitrary input locality, affine slopes of either sign and unbounded positive rescalings are allowed. Then

    log₂ b(m) = 3m/2 + O(log m).

The upper bound already holds for ordinary probabilities with unit output scale. The lower bound uses the fact that the clauses in the midpoint theorem have a *shared vertex dictionary*. Counting all clauses alone gives a smaller exponent.

## Every maximal Hall obstruction requires its exact rectangle

For r between 1 and m put s=m−r+1. Choose row set S of size r and column set T of size s. The matrix that is zero exactly on S×T fails Hall's condition, since only r−1 columns can meet S. Adding any one missing edge restores a perfect matching. Use the new edge, match the remaining r−1 rows of S bijectively to the r−1 columns outside T, and match the m−r rows outside S to the s−1 unused columns of T. Thus each bit in S×T is individually critical.

The midpoint theorem describes positive support by clauses, each a disjunction of at most two members of a fixed dictionary of N individual vertex clauses (one member suffices for a singleton). Discard tautologies and identically true clauses. At each maximal Hall obstruction some clause is false. Every positive literal in it must belong to S×T since all cells outside are true. Conversely, changing any one rectangle cell to true must make this clause true. It must contain that cell as a positive literal. This deduction allows arbitrary negative literals. Consequently S×T is the union of the *positive* cell sets of one or two dictionary members. The empty positive set is permitted.

Replace each nonempty cell set by its bounding rectangle, the product of its row projection and column projection. In a witnessing pair both bounding rectangles lie inside S×T and together cover it. Either one is the entire rectangle, or their row projections are both S, or their column projections are both T. Indeed if the first missed a row and the second missed a column, their intersection cell would be uncovered. Interchanging the boxes gives the other constraint. A witness involving an empty positive set must have one full box and can be charged to its full box alone.

## Count shared dictionary members

Write A=binom(m,r), B=binom(m,s). For each fixed S let n_S be the number of dictionary members with precisely this row span. Row-oriented pairs and single full boxes can witness at most min(B,n_S²+n_S) rectangles with these rows. For n_S≥1 this is at most 2√B n_S, while n_S=0 contributes zero. Summing over S gives at most 2√B N row-oriented rectangles. Likewise all column-oriented witnesses cover at most 2√A N. All AB rectangles are witnessed, so

    N ≥ AB / (2√A+2√B).

At r near m/2 both A and B are Θ(2^m/√m), giving at least a constant multiple of 2^{3m/2}/m^{3/4}. Summation across all r within √m of m/2 sharpens the polynomial factor. In each of those layers A,B remain Θ(2^m/√m), while each nonempty dictionary member has a fixed row span and column span, so it is counted on each orientation at most once over all layers. The same argument gives b(m)=Ω(2^{3m/2}/m^{1/4}). The exponent assertion only requires one layer.

## An ordinary graph attaining the exponent

Split the m columns into C₁ and C₂ of sizes ⌊m/2⌋ and ⌈m/2⌉. On side i of a bipartite graph create one vertex (S,U) for each nonempty row set S and each subset U of C_i. Its absence probability is the average of the matrix entries indexed by S×U, with value zero for empty U. Join vertices across the sides when they have the same S and |U₁|+|U₂|=m−|S|+1. At a Boolean input a vertex is forced present precisely when every entry in its indexing set is zero. No-edge probability is positive precisely when these forced-present vertices are independent, since all other vertices can be simultaneously absent with positive probability. A conflicting edge therefore means exactly that the zero entries contain one of the Hall rectangles S×(U₁∪U₂). Hall's theorem proves the matching predicate. The graph uses (2^m−1)(2^{⌊m/2⌋}+2^{⌈m/2⌉}) vertices.

The same maximal matrices require a violated clause of width rs. In a model with locality d at each graph vertex, every clause has width at most 2d. Thus even without any graph order bound, d≥ceil(floor((m+1)²/4)/2). The construction is for Boolean support and imposes no numerical values on accepting matrices. The positive permanent construction in the companion line-graph note uses triangles, which changes the restrictions on simultaneous forced selections.
