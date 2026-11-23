# Hamiltonian cycles on prescribed-margin, prescribed-diagonal matrices

For an \(n\times n\) matrix \(A\), let \(H_n(A)\) be the sum of \(\prod_i A_{i,\pi(i)}\) over all permutations consisting of one cycle of length \(n\). Fix any field \(K\), including characteristic two, any diagonal \(d\in K^n\), and any row and column sums \(a,b\in K^n\) with the same total. We study \(H_n\) as a polynomial in affine coordinates on the common fibre. The reduction also works for a circuit receiving the full matrix entries and evaluated on this fibre as a polynomial identity.

**Theorem.** For every \(n=m+4\) with \(m\ge2\), a size-\(S\) ordinary or border arithmetic circuit for this restriction gives one of the same kind for the unrestricted \(H_m\) of size \(O(S+\mathrm{poly}(m))\). Consequently the upstream Hamiltonian cycle lower bound transfers to all these slices, over every field. The exponent \(\Omega((\log n)^{1/3})\) and characteristic-dependent threshold are inherited from [the published theorem](https://github.com/anthropics/formal-math/blob/11b6c7e3c927df2658f513b6b68ea7f8929c62c5/vp-vnp/Statement.lean).

**Proof.** Name five distinct vertices \(v_0,\ldots,v_4\). Reserve the row set \(R=\{v_0,v_1,v_2,v_3\}\) and the column set \(C=\{v_1,v_2,v_3,v_4\}\). Write \(T\) for the remaining \(n-5\) vertices and use a single new symbol \(*\). On the complement block \(R^c\times C^c\) place a generic \(m\times m\) matrix \(X\) indexed by \(T\cup\{*\}\), interpreting row \(v_4\) and column \(v_0\) as \(*\). For each \(i\in T\), replace \(X_{ii}\) by \(d_i\). This leaves \(H_m(X)\) unchanged since \(m\ge2\).

Put the remaining diagonal values in their prescribed places and assign zero to unspecified entries initially. For each row outside \(R\), correct its row sum by changing the entry in column \(v_1\). For each column outside \(C\), correct its sum by changing the entry in row \(v_1\). These two disjoint edge sets lie outside the complement block and avoid the diagonal. The only remaining deficits are at the four reserved rows and four reserved columns. Their totals on the two sides agree. Their available pairs form \(K_{4,4}\) minus the three diagonal edges at \(v_1,v_2,v_3\). This graph is connected because row \(v_0\) joins every reserved column and column \(v_4\) joins every reserved row. Fix a spanning tree, leave every other edge zero except for the assigned diagonals, and process its leaves. At each leaf put its deficit on its sole surviving edge and subtract that amount from its neighbour's deficit. The final deficit is zero by equality of the two totals. This construction gives an affine completion \(Y(X)\) using only addition, subtraction and constants, including in characteristic two.

Define \(D\) to have value \(+1\) on the directed path

\[
v_0\longrightarrow v_1\longrightarrow v_2\longrightarrow v_3\longrightarrow v_4
\]

and value \(-1\) on the four edges

\[
v_0\longrightarrow v_4,\qquad v_1\longrightarrow v_3,\qquad
v_3\longrightarrow v_2,\qquad v_2\longrightarrow v_1.
\]

All other entries are zero. Its two sets of edges are disjoint and use each reserved row and column once. The marker has zero margins and zero diagonal, so \(Y(X)+wD\) lies in the prescribed fibre. Its Hamiltonian cycle polynomial has degree at most four in \(w\).

To contribute to degree four, a Hamiltonian cycle must use a perfect matching of the marker support from \(R\) to \(C\). In the order displayed for those sets, the positive matching is the identity permutation of four positions. The negative matching sends positions \((0,1,2,3)\) to \((3,2,0,1)\). Their relative permutation is a four-cycle. Their union is consequently one alternating eight-cycle with precisely two perfect matchings. The negative matching contains the directed three-cycle \(v_1\to v_3\to v_2\to v_1\), which cannot belong to a single cycle spanning all \(n\) vertices. The positive matching supplies the displayed path with coefficient one. Contracting it to \(*\) gives a bijection with the Hamiltonian cycles on \(T\cup\{*\}\). Its complementary edge weights are the entries of \(X\), apart from unused loops. Hence

\[
 [w^4]H_n(Y(X)+wD)=H_m(X).
\]

Simulate a circuit on the pencil over \(K[w]/(w^5)\) and select the degree-four coefficient. Every gate requires a bounded number of base gates, independent of \(m\). Completion and affine reparametrization use polynomial size. For a border circuit perform exactly this simulation over \(K((\varepsilon))\). All coefficients of its output are regular, and coefficient selection commutes with reduction modulo \(\varepsilon\). This verifies the asserted gate and border bounds in every characteristic. ∎

The diagonal choice \(d=0\) and all margins equal to one gives the directed, loopless doubly stochastic affine slice. Over the reals its relative interior contains the matrix having off-diagonal entries \(1/(n-1)\). Exact agreement on the open subset of strictly positive off-diagonal matrices implies polynomial agreement on the fibre.

## Symmetric prescribed-margin and prescribed-diagonal inputs

**Theorem.** The same asymptotic lower bound holds on symmetric matrices with any prescribed row sums and any prescribed diagonal over fields of characteristic other than two. In characteristic two, \(H_N\) on a symmetric matrix is identically zero for \(N\ge3\), since every cycle pairs with its distinct reverse with equal weight.

**Proof.** First represent \(H_m(X)\) by an undirected Hamiltonian path between two fixed ordered endpoints. For each original vertex \(i\) form three vertices \(a_i,c_i,b_i\) joined by unit edges \(a_i c_i,c_i b_i\). Give every edge \(b_i a_j\) with \(i\ne j\) weight \(X_{ij}\). Remove \(c_0\), and take \(b_0,a_0\) as the initial and final endpoints. All internal \(c_i\) have degree two. A path beginning at \(b_0\) enters some \(a_j\), must traverse its gadget in the order \(a_j,c_j,b_j\), and continues this way until its final move into \(a_0\). Conversely every directed Hamiltonian cycle rooted at zero lifts uniquely to such an oriented path. Thus the weighted sum of paths is \(H_m(X)\). Without changing this sum we may subdivide a unit internal edge of a gadget for \(i\ne0\) once or twice. This supplies any desired core order \(3m-1+e\) with \(e\in\{0,1,2\}\).

Add seven reserved vertices \(\beta,l_1,l_2,l_3,r_1,r_2,r_3\). Form a symmetric marker \(D\) from two four-cycles \(\beta,l_1,l_2,l_3,\beta\) and \(\beta,r_1,r_2,r_3,\beta\), putting weights \((+1,-1,+1,-1)\) around each. It has zero diagonal and row sums zero. The two groups of three are disconnected in its support after deleting \(\beta\). A Hamiltonian path through the support therefore traverses one group, then \(\beta\), then the other group. Its two ends belong to \(\{l_1,l_3\}\) and \(\{r_1,r_3\}\), respectively. In particular \(\beta\) is always internal. For ends \(l_1,r_1\) the path through the marker is unique up to reversal. Its weight is one, since each three-edge subpath has weight one.

In a base symmetric matrix \(Y\), use the weighted gadget graph as the core, and assign every diagonal entry the prescribed value. Join \(l_1\) to \(b_0\) and \(r_1\) to \(a_0\) with unit weight. Place whatever residual each core row requires on its single edge to \(\beta\), and put all other core-to-reserved off-diagonal entries at zero. Complete the remaining seven reserved row deficits using just off-diagonal pairs within their clique. Send the deficit at each of four vertices to a designated vertex in a remaining triangle, then solve that triangle by the half-sum formula \(x_{ij}=(h_i+h_j-h_k)/2\). The resulting matrix and its pencil \(Y+wD\) are symmetric with the required margins and diagonal.

A Hamiltonian cycle on the full vertex set uses at most six marker edges. Its marker edges form a cycle-free graph of maximum degree two on the seven reserved vertices, since any cycle among only these vertices would be a separate cycle in the permutation. Six such edges necessarily form a single path covering all seven. Every internal marker vertex already has both cycle neighbours. An unmarked edge between the two ends would close a cycle before visiting the core. Both ends must therefore use external edges. The only eligible endpoints with such edges are the designated two, each with its single specified unit edge. The remainder is exactly a core path from \(b_0\) to \(a_0\). Summing the two global orientations gives

\[
 [w^6]H_N(Y+wD)=2H_m(X),\qquad N=3m+6+e.
\]

Every \(N\ge12\) has this form with \(m\ge2\). Degree-six coefficient extraction uses constant-factor gate simulation and commutes with reduction modulo the border parameter exactly as above. Dividing by two proves the theorem. ∎

Over the reals, row sums one and diagonal entries one-half give a strictly positive definite matrix in the fibre with all off-diagonal entries equal to \(1/(2(N-1))\). Positive definiteness and strict entrywise positivity persist on a relative open neighbourhood. Polynomial identity on that neighbourhood implies identity on the full fibre. Thus the same exact lower bound applies with the additional positive-definite and entrywise-positive promise.
