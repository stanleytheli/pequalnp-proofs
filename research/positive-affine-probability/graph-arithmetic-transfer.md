# A Hamiltonian polynomial in the independent sets of long even subdivisions

Let G be a graph with a separate indeterminate z_v at each vertex and write I_G(z)=Σ_S∏_{v∈S} z_v, where S runs over independent sets. For n≥2 we construct an explicit bipartite graph H_n of maximum degree three and girth at least 30. Its multivariate independence polynomial has the directed Hamiltonian-cycle polynomial HC_n as a projection over every field. H_n has O(n² log n) vertices and edges. Each n×n matrix variable is used as a vertex activity; all other activities are integers in {0,1,−1}.

Our Boolean edge predicate accepts the vertex sets containing an edge. On the same graph an optimal unrestricted fan-in-two De Morgan circuit is a monotone formula reading each variable at most twice. Its exact size follows from the long-subdivision theorem and is available from two vertex and edge counts. The canonical multilinear extension of this Boolean function, however, inherits a superpolynomial lower bound for both exact and approximating arithmetic circuits. Arithmetic here means formal polynomial equality over a field. Monotone 2-CNFs with hard multilinear extensions were studied by Hrubeš. The restrictions here include bipartiteness, degree, growing girth if desired, and efficient construction of an optimal read-two Boolean formula. [Hrubeš, *On hardness of multilinearization, and VNP-completeness in characteristics two*](https://users.math.cas.cz/~hrubes/PDFs/Mult.pdf)

## A unique certificate per Hamiltonian cycle

Set b=ceil(log₂ n) and introduce n² Boolean indicators e_ij for directed edges and b bits r_i for each vertex. Require exactly one outgoing edge per vertex. A prefix OR of the outgoing indicators, the exclusion of a new indicator whenever its prefix is already true, and a final unit clause implement this with O(n²) clauses and unique prefix bits. Fix r_0=0. Define d on b-bit strings to increment modulo 2^b except that d(n−1)=0. Compute d(r_i) in binary once for each i. For each i,j, require e_ij⇒r_j=d(r_i) bit by bit. Use both implication directions for each introduced AND or XOR gate. All auxiliary bits are then uniquely determined by the indicator and rank bits. The complete formula has O(n² b) variables, literal occurrences and clauses, each of width at most three.

The cyclic points of d are precisely 0,…,n−1, in one cycle. Any value from n up to 2^b−1 increments to zero and never returns to that range. Each component of a finite functional digraph contains a directed cycle. The length of every such cycle would be divisible by n, because applying d along it returns to the starting rank. Thus a valid n-vertex digraph consists of one Hamiltonian cycle. Conversely each directed Hamiltonian cycle determines exactly one anchored rank assignment, the forward distance from vertex zero, and one assignment for all introduced gate bits. Weight each satisfying choice by the product of x_ij over its selected edges. Summing gives HC_n, with no factor representing a choice of starting vertex.

## A literal graph with signed vertex activities

Introduce one true and one false literal vertex for each bit. Join the pair to forbid selecting both. A private vertex of activity −1 joined to both enforces the selection of at least one under summation, since its two possible states sum to zero if neither literal is selected. Give the true vertex for e_ij activity x_ij. Set all other literal activities to 1. For each clause, introduce another vertex of activity −1 adjacent to the literal vertices satisfying it. If a clause is unsatisfied its flag contributes zero; if it is satisfied its flag must be absent, contributing one. Different flags have no common edges. The resulting independent-set sum is therefore exactly the weighted satisfying-assignment sum, as an integer polynomial. This cancellation also works in characteristic two. Every vertex is incident to an edge, and every component contains a triangle formed by a variable, its complement and its private flag.

If the seed has an odd number of edges, append one activity-zero leaf adjacent to an existing literal. This preserves the polynomial and makes the edge count even. Write v and m for its final vertex and edge counts.

## Degree reduction and uniform even subdivision

For a hard-core edge let E have rows (1,1) and (1,0), indexed by absence and presence. A private internal vertex of weight −1 contributes D=diag(1,−1). A path with k private weighted vertices has endpoint interaction (ED)^k E. Direct multiplication gives

    (ED)^3 = −I,        (ED)^2 E = diag(−1,1).

Replace a vertex of degree d≥1 by d copies, each assigned one incident edge. Link consecutive copies with length-three paths having two private vertices of weight −1. The second identity forces all copies to take the same spin. Assign the original activity to the first copy, all ordinary copy activities to 1, and give the second copy activity −1 if d is even. For each uniform spin the local weight is then (−1)^(d−1) times the original one. No variable is negated or squared in this construction.

Write K for the resulting subcubic graph, with V=6m−2v vertices and M=7m−3v edges. Indeed there are 2m copies and D₀=2m−v equality links, each of which has two private vertices and three edges. Replacing every vertex with a tree preserves the number of components and their cycle ranks. Thus all components of K contain a cycle. All physical inputs are nonisolated.

Replace each edge of K by its own path of length L, where L≥10 and L≡4 (mod 6); every new interior activity is −1. Since L−1≡3 (mod 6), the path contributes −E on its endpoints. The combined overall factor from splitting and subdivision is (−1)^(D₀+M)=(−1)^(m+4D₀)=1. The resulting simple graph H has V+(L−1)M vertices, LM edges, maximum degree at most three, and girth at least 3L. Even path lengths give a bipartition in which all vertices inherited from K lie on one side. This proves the claimed projection. For L=10 the vertex and edge counts are 69m−29v and 70m−30v, respectively.

## Boolean gate count and the polynomial lower bound

Let A contain all vertices inherited from K and every even-position private vertex on each path. This is one color class of H. A minimum cover has size |A|=V+(L/2−1)M: for an even-base-edge component the parity quotient selects either the whole component, costing its number of vertices, or none, costing its number of edges. Each component of K is connected and contains a cycle, so selecting it costs at most as much as omitting it. The long-subdivision circuit theorem gives the exact Boolean count

    C_Bool(H)=V+(3L/2−1)M−1.

The star formula centered on A attains this count. Each center occurs once; every opposite-color vertex is a private odd-position path vertex of degree two and occurs exactly twice. For L=10 the answer is V+14M−1. [Long-subdivision theorem and parity quotient](https://github.com/stanleytheli/pequalnp-proofs/tree/a31fcb5bd01e0bd1ba8e58c7c7db40195392c5fa/research/long-subdivision-circuits)

Anthropic's public formal statement asserts that for some absolute c>0 and sufficiently large n depending on the characteristic, the arithmetic circuit size and border size of HC_n over every field exceed n^(c(log₂ n)^(1/3)). Our ordinary-variable and constant projection preserves the arithmetic circuit gate count. A circuit over Laurent series that approximates I_H likewise specializes to an approximating circuit for HC_n, since all substitutions are regular constants or variables. Thus both lower bounds transfer. As N=|V(H)| is polynomial in n, they also have the form exp(Ω((log N)^(4/3))). We use the stated upstream theorem as a black box. [Pinned Anthropic statement](https://github.com/anthropics/formal-math/blob/11b6c7e3c927df2658f513b6b68ea7f8929c62c5/vp-vnp/Statement.lean)

For any fixed 0<α<1, one may take L polynomial in M with L≡4 mod 6 and L≥(2M)^q, choosing q/(q+1)≥α. Because V≤2M, we get N≤(L+1)M≤L^(1+1/q), hence girth(H)≥N^α. The polynomial growth of N in n, with α fixed, preserves the superpolynomial lower bound.

## A division-free circuit reduction for multilinear extensions

Let f_H be the canonical multilinear extension of the Boolean edge predicate and R=1−f_H. Then

    I_H(y)=∏_i (1+y_i) R(y_1/(1+y_1),…,y_N/(1+y_N)).

This follows termwise from R(x)=Σ_(S independent) ∏_(i∈S) x_i ∏_(i∉S) (1−x_i). It works in every characteristic. If f_H has an s-gate arithmetic circuit, substitute y_i t for y_i and evaluate the displayed right side in F[y][t]/(t^(N+1)). Each 1+t y_i is a unit, its inverse is a truncated geometric progression, and every addition and multiplication is implemented by operations on N+1 coefficients. Computing all input series and the outside product, then simulating the circuit, costs O((s+N)N²) scalar arithmetic gates. Evaluate the resulting coefficient list at t=1 by summation. The target I_H(ty) has degree at most N in t, so truncation loses no term. With constants in F((ε)) and coefficients regular in ε at the circuit output, the same construction yields an approximating circuit: each coefficient of the transformed output is a finite F-linear combination of coefficients of the original output, agrees modulo ε with I_H and has no negative powers. This handles an approximating polynomial of arbitrarily high formal degree.

Thus the lower bound also holds, up to a polynomial factor, for f_H and its border size. A general circuit agreeing with f_H on Boolean inputs exists with O(|E|) gates: 1−∏_(uv∈E)(1−x_u x_v), with individual degrees at most three. The lower bound concerns the canonical multilinear polynomial itself.

## Reproduction

The original Python constructor hamiltonian_seed.py emits the full graph and the projected integer or variable label at every vertex. Its probability-leaf mode creates a private leaf attached to each true edge indicator and sets that indicator's own activity to one. In this mode a Bernoulli leaf of probability 1−x_ij supplies a factor x_ij when the indicator is true and integrates to one otherwise.

The independent verifier check_contraction.py receives only the emitted graph, its labels and test values. It contracts degree-one and degree-two vertices and equality constraints as general binary factors, then uses exact variable elimination over a prime field. It checks the result against the Hamiltonian-cycle sum enumerated directly from permutations. It uses only the Python standard library.
