# Two layers of AND gates with shared OR circuits

Let G be a finite simple graph with no triangle or four-cycle, maximum degree at most four, m ≥ 1 edges, and minimum vertex-cover size τ. Consider binary monotone circuits organized as follows.

- The internal AND gates compute signals of the form h = (OR A) AND (OR B), where A and B are sets of raw vertex variables represented by OR circuits.
- A second AND layer has one term x_z AND Q_z per selected center z. Each Q_z is computed by OR gates from raw variables and the internal signals.
- The output is the disjunction of these terms.

The OR circuits can share gates arbitrarily, including a raw OR gate used both in an internal operand and in a final query. A used internal AND has no internal AND ancestor. Both layers can involve vertices from either side of the graph.

**Theorem.** The minimum size for the full edge predicate in this class is m + τ − 1. This gives 64 gates for the order-three projective-plane incidence graph and 27 for the Heawood graph.

The star construction attains the stated size. For the lower bound, eliminate constants and unused signals. Merge terms having the same center by disjoining their queries. Each merge reduces the total gate count. Let c be the number of distinct centers, q the number of inner OR gates, and k the number of internal AND gates. The final c ANDs and their output disjunction require at least 2c − 1 more gates. The centers cover all genuine edges, so c ≥ τ. It will suffice to prove q + k ≥ m − c.

## OR queries with erroneous memberships

Suppose a binary OR circuit produces the sums on sets S_z of variables. Let R_z be a subset of S_z with at most four elements. Suppose distinct R_z intersect in at most one element. Write d_z = |R_z| and r_z = |S_z minus R_z|. The circuit contains at least the sum over z of max(0, d_z − 1 − r_z) gates.

Outputs with r_z ≥ 3 have no positive requirement. For r_z = 2 only d_z = 4 matters. Reserve its output gate as one unit. It contains four raw labels of R_z. The full support of any other output with at most two errors contains at most three labels of R_z. Thus this gate cannot belong to any of the other cones under consideration. Here and below the support of an OR gate is the full set of raw labels in its cone.

For each remaining cone, where r_z = 0 or 1, set raw labels outside R_z to false and bypass every OR for which one operand already has the full projected output support. Every surviving gate strictly grows both input supports. It produces a set of at least two labels. If such a physical gate is used in two projected cones z,w, its full raw support lies in the intersection of S_z and S_w. Two labels in each projection and at most one common label force three labels in the full support. Each projection contains two of these three and omits its own single error. In particular an error-free cone never shares a surviving gate. A gate of full width three has a child of width at least two. At least one of the three possible pair projections is already present in that child and cannot use this gate after bypassing. A particular pair can occur in at most one R_z. Hence at most two cones use the physical gate, each to combine two singletons into a pair. Charge such a gate half to each cone. Charge a gate used by only one cone wholly to that cone.

In a single normalized cone let e be the number of its half-charged gates and g the number of other gates. Delete dead paths after the bypasses. Each half-charged gate now has singleton inputs, so taking these e pair outputs as new distinct sources leaves a connected binary cone with g gates and at least e sources. If l raw singleton sources remain, then d_z ≤ l + 2e, and g ≥ l + e − 1. Thus its charged cost is at least

    max(d_z − e − 1, e − 1) + e/2.

An error-free cone receives at least d_z − 1, because e = 0. For a single error and d_z ≤ 4 the display is at least d_z − 2. For e = 0,1,2 this follows directly. For e ≥ 3 the second argument gives at least 7/2. The nonnegative charges also cover a zero lower bound. This proves the query estimate.

## Saving gates when internal signals are set to false

In an OR circuit, mark r distinct input signals for replacement by false. Assume each has a path to a designated output, and all fixed structural zero inputs have already been removed. Let b be the number of designated outputs with empty support after substitution. Then at least r − b OR gates can be removed by constant propagation.

Indeed, let Z be the number of gates whose both operands have become zero, and M the number whose exactly one operand has become zero. Each of the r + Z zero signals either has an outgoing operand slot in one of these gates or is a designated zero output. There are at most 2Z + M such operand slots and b designated zero outputs. Consequently r ≤ Z + M + b, and all Z + M gates can be removed. If some physically unused gates are present, trim before applying the argument. The same argument considers only the part reachable from a deleted input. Its gates have no path into another internal AND in our two-layer model.

## Replacing an individual internal signal

View a final query first as a formal OR of its raw variables and internal signals. A center consumes h when a formal OR path from h reaches its query. If it consumes h, every assignment containing z on which h is true must contain a genuine graph edge. This uses full correctness, including independent inputs of size three and independent color classes.

The replacements below yield one ordinary raw OR circuit. Some internal signals are replaced by raw wires, others by false. We also put raw neighbor groups at named centers. This may introduce additional centers. An error is a raw label in a query that is not a neighbor of its center. We preserve each true two-vertex input, allowing a different center to cover it.

Remove an empty operand or absorb a singleton operand that belongs to the other operand. These give zero or a raw variable. In the remaining singleton case write h = x_a AND (OR B) with a outside B.

- If B has two or more vertices outside N(a), replace h globally by x_a. Every consuming center z outside N(a) must be adjacent to every such stray vertex. Indeed z cannot equal a, and the input containing a, z and the stray vertex lights h and the final center. The only possible edge is between z and the stray vertex. Two stray vertices have at most one common neighbor, so this replacement introduces at most one error across all centers.
- If B has at most one vertex outside N(a), set h to false and put the raw group B at center a. Every genuine edge input lost by the substitution contains a and a vertex of B. The new group covers all such edges and has at most one error.

Now suppose both operands have at least two labels. Put I = A intersect B. Every label of I is a genuine neighbor of every consuming center, by the singleton test for h. If a consuming center z lies in A, then B is entirely in N(z), and conversely if z lies in B then A is entirely in N(z). No consuming center lies in I.

When I is empty, set h to false. A successful two-vertex input at center z must have z in one operand and its other endpoint in the opposite operand. At most one center lies in A, since two such centers would share all of B as neighbors. At most one lies in B for the same reason. At each of these at most two centers put its opposite raw operand as a group. Each group has zero errors.

When I has just one label, use that raw label in place of h. At most one extra opposite-operand group is needed. If both a center z in A and a center w in B existed, z and w would be adjacent and would both be neighbors of the common label in I, forming a triangle. The replacement and extra group have zero errors.

Finally assume |I| ≥ 2. There is exactly one consuming center z, since every consumer is adjacent to all of I and two distinct centers cannot have two common neighbors. Put A_bad = A minus N(z) and B_bad = B minus N(z). Every vertex a in A_bad is adjacent to every vertex b in B_bad. Indeed, the input containing z, a and b lights h and its final term, and z is adjacent to neither a nor b. The two bad sets therefore form the sides of a complete bipartite subgraph. Four-cycle freeness implies that at least one bad set has at most one element. Replace h globally by the corresponding whole raw operand. It covers every pair previously supplied by h at its unique center and introduces at most one erroneous membership. This argument works even if z belongs to an operand.

## Combining the counts

Let r count internal signals set to false, and let K count the raw groups added in the replacements. Let E be an upper bound obtained by summing the possible erroneous memberships introduced by the replacements and groups, one charge for each indicated error. The cases give

    K + E ≤ k + r.

A globally replaced signal costs at most one group or one error. A deleted signal costs at most two groups without errors or one group with at most one error. Raw replacements are made in the existing OR network. All added groups use existing raw wires.

Let b of the c original queries become empty after the global replacements. The OR network can now use at most q − r + b gates, by the preceding slot count. Discard the empty queries. Append the K new groups, merging all groups for a given center into a single query. If n centers that had no surviving query become nonempty (including revived original centers), the merges use at most K − n additional OR gates. The final number of nonempty queries is c − b + n.

For each resulting query let R_z be its genuine neighbors present in its raw support. Every graph edge is represented at least once, so the sum of d_z is at least m. Distinct centers have at most one common neighbor; all d_z are at most four, and all error counts sum to at most E. The query estimate therefore gives

    q − r + b + K − n ≥ m − (c − b + n) − E.

This simplifies to q + K + E − r ≥ m − c. Since K + E − r ≤ k, the desired bound follows.
