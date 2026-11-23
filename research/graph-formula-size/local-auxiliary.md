# One shared signal in a circuit for projective-plane incidence

The order-three plane has 26 inputs, 52 incidences and minimum vertex-cover size 13. Its ordinary star circuit has 64 binary gates. Consider circuits of the following form. A private, arbitrary monotone binary circuit computes one signal h. For each chosen center z the output has a term x_z AND (OR of its listed raw neighbors and, optionally, h). Each term has its own OR tree, and the output is their OR. The root wire h may go to any number of terms. Its interior is private. This includes a two-sided choice of centers and arbitrary internal sharing in the circuit for h.

**If h depends on at most 14 raw inputs, every circuit of this form needs at least 64 gates.** This bound examines all Boolean functions possible for h under the stated monotonicity and support condition. Its certificate uses no sample of proposed circuits.

Write R for the essential input set of h and r for its size. A binary circuit computing h has at least r−1 gates, by counting input slots in a connected output cone. Constants can be removed. If h is unused, the ordinary star bound applies. Let T be the centers that use h and let D be the graph edges whose two-vertex assignment makes x_z AND h true for some z in T. Each such term must be safe on every independent set. The full set of term centers covers every edge. Distinct residual edges outside D require at least one raw neighbor occurrence each. If c is the number of centers and a is the cost of the private auxiliary, the total gate count is at least

    52 − |D| + |T| + c − 1 + a.

Repeated centers are harmless for the inequality: use the distinct centers to define T and lower-bound c by the size of the cover. The expression follows by adding the sizes of the OR trees, the center AND gates, the final OR tree and the private circuit. Thus any strict improvement requires |D|−|T|>a.

Let S be the raw singleton inputs on which h is true. Every center in T must be adjacent to every vertex of S, including the requirement that the two vertices be distinct. Otherwise the center gate would accept an independent set of at most two vertices.

- If S has at least two vertices, only one center is possible because the graph has no four-cycle. A single use of h can be unfolded only if it is a formula, but even an internally shared h gains nothing at that center: every other potentially covered neighbor w requires either w in S or both z and w in R. In either case w belongs to R, except when z is the singleton input, which safety rules out. Thus |D|≤r and |D|−1≤r−1≤a.
- If S consists of one vertex s, T is contained in N(s). At most |T| edges of D are incident to s. Every other covered edge has a second endpoint w in R different from s and requires its center z in R as well. The other endpoints cannot repeat across different centers, since that would make a four-cycle with s. Therefore |D|−|T|≤r−1≤a.
- If S is empty, D is contained in the graph induced by R. The vertices of T in R cover D. For any subgraph D of H=G[R], the quantity |E(D)|−τ(D) is at most |E(H)|−τ(H): adding one edge increases the cover number by at most one. Consequently |D|−|T|≤|E(H)|−τ(H).

For the last case, support.cpp enumerates all point and line subsets of the given plane. For each fixed set of selected lines it computes matching deficiency simultaneously for all point subsets, using the maximum of |U|−|N(U)| over subsets U of the selected points. Hall's theorem and König's theorem then give τ(H). Its output columns are r, the maximum of |E(H)|−τ(H)−(r−1), and point and line masks attaining that value. The maximum is nonpositive at every r from 1 through 14. The first positive value occurs at r=15, so this particular counting test stops there. Each pair of masks encodes local indices 0 through 12 on its respective side. Subsets with no points have no edges and cannot improve the maximum.

The calculation concerns the displayed form with a single shared signal and private star OR trees. Further internal wires shared between star computations, or additional nested signals, are separate circuit possibilities in the unrestricted project question.
