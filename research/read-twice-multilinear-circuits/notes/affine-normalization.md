# Exact affine specialization on long bipartite subdivisions

Let E be the two-spin interaction with E(1,1)=0 and all other entries 1. For a graph H, the polynomial

    Q_H(p) = ∑_{spins σ} ∏_v p_v^{σ_v}(1−p_v)^{1−σ_v} ∏_{ab∈E(H)} E(σ_a,σ_b)

is multilinear and agrees on the Boolean cube with the indicator that the selected vertices form an independent set. Thus 1−Q_H is the canonical multilinear extension of the graph edge-detection predicate. All identities here are formal polynomial identities in every characteristic. Probabilities are indeterminates and can be specialized to field elements.

## A path with adjustable end factors

The endpoint spins are external. We sum only the nine internal spins of a length-ten path. First use activities z, so an unoccupied internal vertex has weight 1 and an occupied one weight z. A normalized Bernoulli parameter p=z/(1+z) multiplies this local sum by the same nonzero scalar 1/(1+z) for both possible spins.

Work over the rational function extension F(t,u) of any field F. Define F₀=1, F₁=1+t, Fⱼ=Fⱼ₋₁+tFⱼ₋₂. Fⱼ is the independent-set partition function of a j-vertex path with constant activity t. Each has constant coefficient 1. Put B=F₆, C=F₅, and A=t⁶/C. Assign activity t to six consecutive middle vertices (positions 2 through 7) and −B/C to position 8. When the adjacent vertices at positions 1 and 9 have states 00, 01, 10, 11, the partition functions of this middle segment are respectively 0, B, A, C. Indeed 00 gives F₆−BF₅/C=0; 10 gives F₅−BF₄/C=A by F₅²−F₆F₄=t⁶. This Cassini identity follows from the recurrence (or direct expansion). Positions 01 and 11 give F₆ and F₅.

Let the outer left and right multipliers be r,s. Assign positions 1 and 9 the activities

    a=(1−r−s)B/(rC),           b=(1−r−s)A/(sC).

Summing these two spins gives the boundary matrix

    [[aA+bB+abC, aA], [bB, 0]] = D [[1,s],[r,0]],
    D=(1−r−s)AB/(rsC).

Use (r,s)=(u,u) on ordinary edges, and (u,1) on an edge leading to a designated leaf (row index at its owner). Every activity in the path is defined and differs from −1. For −B/C this follows from B−C=tF₄. For (u,u), the numerators of 1+a and 1+b after clearing uC have nonzero constant terms B and A as polynomials in u. For (u,1), a=−B/C and b=−uA/C. In each case D≠0 (also in characteristic two). The normalized path signature is therefore κ[[1,s],[r,0]], with κ=D/∏_{i=1}^9(1+zᵢ)≠0. No limiting operation is needed.

## Exact transfer of a weighted graph

Start with a finite loopless weighted graph G in which every root has positive degree. Roots carry constant activities c_v, and some additionally carry matrix variables x_j multiplying that activity when selected. Attach a separate leaf to each occurrence of a variable at its root, before subdividing. Let d_v be the degree of the root in this enlarged base graph. Substitute a ten-edge path for *every* base edge, including each new leaf edge. Give each root the fixed Bernoulli parameter

    p_v = c_v/(u^{d_v}+c_v).

Give each designated leaf for x_j the affine input 1−x_j. Using the path signatures above, summing the leaf spin contributes κ if its owner is absent and κ·u·x_j if its owner is present. An ordinary path contributes κ times its hard-core constraint and a factor u for each occupied endpoint. All paths together contribute u^{d_v} per occupied root. The ratio of its occupied to unoccupied weight is therefore c_v times all its designated data variables. It follows that

    Q_H(specialized inputs) = (∏_e κ_e)(∏_v (1−p_v)) Z_G(c_v·∏_{j at v}x_j),

where Z_G is the multivariate independent-set partition function. The scalar in parentheses is nonzero and independent of the matrix entries. This is an ordinary affine substitution over F(t,u) with an output rescaling. Each variable input is a single complement. The original field embeds in F(t,u); hence arithmetic circuits for Q_H over F also transfer. Substituting constants independent of the Laurent approximation variable preserves regular coefficients and constant terms, giving the same implication for border complexity.

The form also covers a designated leaf already present in the base graph: omit that leaf and its edge when specifying G, retain its owner's degree in the enlarged base, and then apply exactly the same construction. A root whose only original neighbor is its designated leaf still has positive enlarged degree, which is enough for the denominator argument.

## Application to Hamiltonian-cycle witnesses

Use a parsimonious Boolean witness for a directed Hamiltonian cycle with its rotation anchored at a specified vertex, and clause flags of activity −1 in the independent-set encoding. Variable triangles ensure each component contains a cycle. Splitting each high-degree graph vertex into a chain of copies and joining neighboring copies by length-three equality paths of internal activity −1 preserves the partition function up to a fixed sign; the local equality matrix is diag(−1,1). Allocate distinct incident edges to the copies and keep each data leaf unique. These operations produce a subcubic loopless base of size polynomial in the matrix order with only activities 0,1,−1 besides the data leaves. See the accompanying explicit seed construction and verification. The exact affine path substitution then sends the canonical independent-set multilinear extension to a nonzero scalar times the Hamiltonian-cycle polynomial.

The final unsigned graph H is bipartite, subcubic, and has girth at least 30. In each ten-edge path its odd internal positions lie on one common bipartition side B and have degree two. All original vertices and all even internal positions lie on side A. The explicit star formula centred on A reads each A variable once and each B variable twice, and can be built in linear time. Every base component contains a cycle, so taking all original vertices minimizes the even-path endpoint charge (selecting a whole component costs its vertex count, omitting it costs its edge count). The established subdivision theorem gives exact unrestricted De Morgan size |E(H)|+|A|−1, attained by this same read-twice monotone formula.

This yields a sparse read-twice family with linear-size optimal Boolean formulas whose canonical multilinear extensions require superpolynomial-size arithmetic circuits, including border circuits over every field, on the strength of the released Hamiltonian-cycle bound. With the O(m² log m) seed for order m, the number of graph variables is O(m² log m), and affine-input and output overhead is O(m²). The superpolynomial bound in graph order retains the exp(Ω((log N)^{4/3})) form. Hrubeš previously proved VNP-hardness of multilinearizing monotone 2-CNFs over every field. The additional restrictions and the explicit exact normalized-path construction are the focus here. [Hrubeš, 2015](https://eccc.weizmann.ac.il/report/2015/067/) [Anthropic, formal theorem](https://github.com/anthropics/formal-math/blob/11b6c7e3c927df2658f513b6b68ea7f8929c62c5/vp-vnp/Statement.lean)
