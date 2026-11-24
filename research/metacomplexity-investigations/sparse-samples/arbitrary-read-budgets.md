# Exact gate counts and feasibility for every read budget

Let \(H=(V,E)\) be any finite simple graph with no triangle or cycle of length four and \(m=|E|>0\). Fix nonnegative individual read budgets \(r_v\) for its vertex variables. Its Boolean function accepts precisely those vertex sets containing an edge. A read is an input occurrence in a binary monotone AND/OR formula. A binary gate costs one and the formula is a tree. Put
\[
   R=\{v:d(v)>r_v\},\qquad O=V\setminus R.
\]

**Theorem.** A formula respecting all budgets exists if and only if
\[
                |E(H[S])|\le\sum_{v\in S}(r_v-1)
                \qquad\text{for every }S\subseteq R.             \tag{1}
\]
Whenever feasible, the exact minimum gate count is
\[
                   m+|V|-1-\alpha(H[O]).                         \tag{2}
\]
The right-hand side of (1) uses integer subtraction, so a zero read budget on a nonisolated vertex fails its singleton test. The earlier graph-formula project formalized Hall feasibility, its density form, and regular readability for whole-function formulas. The additional optimization formula (2) and the sparse sample below identify the minimum gate count for every feasible individual budget. The bundled Lean module `CappedMinimum.lean` proves both the whole-function lower bound and attainment.

Both conclusions hold unchanged if the formula is only required to fit the following finite sample. Each edge \(e=ab\) gives a positive row \(\{a,b\}\) and a negative row \(I_e=(N(a)\cup N(b))\setminus\{a,b\}\). Include also a negative singleton \(\{u\}\) for each vertex \(u\) having a degree-one neighbor. Duplicate negative examples may be merged. For maximum degree \(\Delta\), each negative has size at most \(\max(1,2\Delta-2)\) and each coordinate occurs in at most \(\Delta^2+1\) rows. Graphs of minimum degree at least two need no singleton supplement.

**Pointwise replacement.** The set \(I_e\) is independent. An edge between two of its points would give a triangle or a four-cycle with \(e\). Run the monotone formula protocol on the pairs of positive and negative rows as in the [sparse-sample proof](sparse-formula-consistency.md). Assign each edge to the endpoint selected at \((e,I_e)\). If \(v\) has degree \(d\) and owns \(a\) edges, its \(d\)-by-\(d\) incidence submatrix has ones off the diagonal and exactly \(a\) diagonal ones. This forces at least
\[
                             d-a+\mathbf1[a>0]
\]
occurrences of \(v\) when \(d\ge2\). For \(d=1\) the expression is one regardless of ownership. The positive row of its unique edge, compared with the negative singleton on the other endpoint, forces the variable to occur. For \(d=0\) the expression is zero. Make one star per used owner, taking the OR over all stars. Its occurrences are exactly the displayed expression, and its size is \(m+\#\{v:a_v>0\}-1\). Thus every sample-consistent formula gives a full-function formula dominated separately in every read count. In the other direction each ownership assignment supplies such a star formula. For the row bounds, \(v\) appears in \(d(v)\) positives, at most \(\sum_{u\sim v}(d(u)-1)\) edge-indexed negatives and at most one extra singleton.

**Feasibility.** A vertex in \(O\) needs no minimum number of owned edges. A vertex in \(R\) needs at least \(L_v=d(v)-r_v+1\) owned edges. The incidence bipartite graph can assign distinct edge slots to these demands precisely if \(\sum_{v\in S}L_v\) is at most the number of edges incident to \(S\), for every \(S\subseteq R\). This is Hall's theorem applied to \(L_v\) copies of each vertex. The strongest demand for a given support takes all its copies. The incident supply is \(\sum_{v\in S}d(v)-|E(H[S])|\), giving (1). Every edge not allocated to a demand can be oriented arbitrarily. A bipartite matching or integral maximum flow finds a feasible assignment, or detects infeasibility, in polynomial time. Orientation feasibility is classical; the pointwise formula replacement identifies why it answers these read-budget questions. [Hakimi, *On the degrees of the vertices of a directed graph*](https://doi.org/10.1016/0016-0032(65)90340-6).

**Optimization.** The unused owners of any permitted assignment are independent and all belong to \(O\). Thus at most \(\alpha(H[O])\) are unused. Conversely choose any maximum independent set \(I\) in \(H[O]\), starting with any feasible assignment from the preceding paragraph. Reassign every edge owned by \(I\) to its other endpoint, necessarily outside \(I\). Only vertices with zero lower demand can lose edges, and every demand elsewhere is preserved. This attains the largest possible number of unused owners, proving (2). Isolated vertices add one both to \(|V|\) and to the independence number and have no effect on the gate count.

**Uniform readability.** Define \(p(J)=\lceil\max_{\varnothing\ne S\subseteq V(J)} |E(J[S])|/|S|\rceil\), with value zero on an empty graph. This is the pseudoarboricity of \(J\). Read cap \(k\ge1\) is feasible exactly if
\[
                         p(H[\{v:d(v)>k\}])\le k-1.
\]
In particular the minimum possible maximum read is either \(p(H)\) or \(p(H)+1\), and one density test distinguishes the two. The larger cap is always feasible by the displayed criterion. To see that a cap below \(p(H)\) is impossible, choose a vertex set with more than \(k\) induced edges per vertex and repeatedly delete any vertex of original degree at most \(k\). Each deletion preserves positive excess of the edge count over \(k\) times the vertex count. A nonempty remainder violates (1). For a \(d\)-regular graph in this class and \(d\ge2\), the uniform readability is exactly \(\lceil d/2\rceil+1\). A nonempty matching has readability one.

Given a gate allowance as well as read caps, first test (1). The remaining decision question is solely an independent-set threshold on the induced graph \(H[O]\). Changing a positive cap below degree can change feasibility; once feasibility holds, the precise value of any such cap has no effect on the optimal gate count.
