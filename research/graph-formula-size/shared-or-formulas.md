# Shared OR gates and independently computed auxiliary formulas

Let G be a finite simple graph without triangles or four-cycles, with a positive number m of edges and minimum vertex-cover size τ. Each of a collection of private binary monotone formulas computes a signal h_i from the raw vertex variables. These private formulas have disjoint gate sets. An arbitrary circuit of binary OR gates uses the raw variables and the h_i as its inputs. For each selected center z one signal B_z from that OR circuit is conjoined with x_z. Their OR is the final result. If this circuit computes the edge function of G, it uses at least m+τ−1 gates. The usual star circuit attains the bound.

Both the center set and the shared OR circuit are arbitrary. In particular a shared OR may combine several different auxiliary outputs before reaching several centers. The theorem concerns reuse outside the private auxiliary formulas; internal reuse of nonlinear subcomputations is a separate possibility.

## Assigning positive edges

Merge terms having the same center by ORing their neighbor signals. This takes one fewer gate overall per merge. Remove dead terms, constant gates and unused auxiliaries. Let c be the number of remaining centers. If there is only one center its root OR uses zero gates. The general number of final AND and combining OR gates is at least 2c−1.

Let S_i be the singleton inputs at which h_i is true. No used auxiliary can be true on the empty input, because a center singleton would then be accepted. View the OR circuit abstractly in its inputs, and replace each h_i by the OR of the x_s for s∈S_i, with the empty sum false. This replacement gives each center a Boolean sum supported on a set R_z of raw variables. It is its exact singleton support. Every s∈R_z is a genuine neighbor of z: the term's acceptance of {z,s} and rejection of {z} prove this.

There are at most Σ_z |R_z| edges of G of the form zs with s∈R_z. Assign each other edge to a successful term z, then to one auxiliary h_i in that term's OR supplying a true value on the edge. Such an auxiliary exists because success by a raw variable would have put its other endpoint in R_z. Let D_i denote the resulting disjoint sets of assigned edges. They satisfy

  m ≤ Σ_z |R_z| + Σ_i |D_i|.

For one auxiliary suppress the index and write h,S,D,T for its formula, lit singletons, assigned edges, and set of centers reached by its OR output. The set T covers D. The signal h is true on every D-edge and false on every independent set containing a member of T. An assigned edge has no noncenter endpoint in S, since every member of S belongs to the receiving center's R_z.

We claim that the private gate count a satisfies

  a ≥ |D| + max(|S|−1,0).

For empty D this follows from essentiality of the lit singletons. If |S|≥2, every element of S is a neighbor of every member of T. Four-cycle freeness gives |T|=1. Its only center is absent from S and each assigned edge contributes a distinct new essential variable outside S, by comparing that edge with the center singleton. Therefore h has at least |D|+|S| distinct variable leaves. If S={s}, all consuming centers belong to N(s). Every assigned edge zw with z∈T has its essential variable w outside T∪{s}. Such w cannot repeat across two different centers because of the potential four-cycle with s; the centers are mutually nonadjacent because G has no triangles. Including the essential s gives at least |D|+1 variable leaves.

## The zero-singleton case

Let S=∅ and D nonempty. Then both endpoints of each D-edge are essential variables. For an edge f={p,q} in D, its proper neighborhood I_f consists of neighbors of either endpoint, excluding p and q. Use the full graph G for these neighborhoods. They are independent by the short-cycle assumptions. Call f good when I_f contains a member of T. Then h(I_f)=false. Run the deterministic formula protocol on positive D-edges against these negative inputs. Orient each good diagonal row/column pair (e,I_e) toward the returned endpoint. For a vertex v, put d_v and k_v for its good-edge degree and indegree. Restrict to the incident good rows and columns. Every off-diagonal entry has unique permissible label v and the selected k_v diagonals also have label v. The rectangle rank calculation in formula-exact.md gives at least d_v−k_v leaf occurrences of v. It gives one extra if k_v>0. When d_v=1, k_v=0, the one needed occurrence follows from essentiality.

A bad edge with exactly one endpoint in T has a private pendant endpoint u outside T: every other D-edge at u would have a different center at its far end, making the original edge good. These pendant endpoints are all distinct and absent from good edges. Bad edges joining two centers form a matching B. If two such bad edges met, the additional center would lie in a proper neighborhood, making the other edge good.

Consider a vertex v on a matching edge e∈B. Enlarge its local positive rows to the good incident edges together with e. Use also the negative input N_D(v). This is independent in G by triangle freeness and contains v's other endpoint in e, which belongs to T. Therefore h is false on this extra input. Every local positive edge has unique witness v against it, so its whole column in the v-labelled cell matrix is the all-ones vector. For every good edge j incident to v and oriented away, its column on this enlarged row set is all ones minus the jth coordinate vector: this holds on the extra row e as well, because its far endpoint is included in I_j. The corresponding d_v−k_v coordinate vectors and the all-ones vector are independent; their extra e-coordinate gives the last independent direction. Each occurrence of v contributes an indicator rectangle of rank at most one. This proves at least d_v−k_v+1 leaves for EVERY endpoint of B, regardless of the orientation at its good incident edges.

Summing the d_v−k_v terms gives the number of good edges. If there are p bad pendant edges and b=|B|>0, the distinct additional vertex labels just proved give

  leaves(h) ≥ |good|+p+2b ≥ |D|+1.

If b=0 and a good edge exists, one of its endpoints owns its diagonal and receives an extra leaf; all p pendant endpoints are still distinct and outside the good graph. If every edge is a bad pendant, the p distinct outside endpoints require separate occurrences and at least one center is essential as well. This proves a≥|D| in all zero-singleton cases.

## Counting the joint OR circuit

Let q denote the number of original inner OR gates. Substituting the singleton-sum formulas costs at most Σ_i max(|S_i|−1,0) additional OR gates; empty singleton supports can be set to zero and their gates simplified. This produces every sum on R_z. In an OR-only realization, a wire with at least two distinct raw labels can feed at most one distinct center: any two centers share at most one neighbor. For each center with |R_z|≥2, at least |R_z|−1 gates with at least two raw labels are needed. This follows by retaining the cone of its output, treating widths zero and one as constants or corresponding variables, and counting input slots in the resulting connected binary graph. These counted gates are disjoint between centers. Thus

  q+Σ_i max(|S_i|−1,0) ≥ Σ_z |R_z|−c.

Combining the edge assignment, the private formula bounds, and the 2c−1 final gates gives a total of at least m+c−1. The centers cover every edge, so c≥τ. For the order-three projective plane this class needs exactly 64 gates.
