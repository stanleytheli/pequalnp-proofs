# Fixed-sample formula minimization realizes monotone NP/poly

For each input length fix one list of accurately labeled examples, one target function and one gate threshold. The external instance is a bit string \(x\). Its \(i\)-th bit specifies whether a designated coordinate of the formula can occur three times instead of two. All other read caps are fixed constants in \(\{2,3\}\). The answer is yes if a consistent monotone binary formula meets the gate threshold and those caps. In the construction each bit controls a different coordinate exactly once.

For polynomial-size fixed data and polynomial gate thresholds, the Boolean function families obtained in this way are exactly the monotone languages in \(\mathrm{NP/poly}\). Here “monotone” describes the language on permission bits; the Boolean verifier for the language can use negation. The result continues to hold when each positive example has weight two, each negative has weight two or three, each coordinate occurs in at most six examples, and a read-two star formula for the full target is always available. It also holds when the cost being thresholded is gates plus twice the number of sample errors.

## Representing one language

The answer is monotone, since extra read permissions preserve any witnessing formula. Guessing a formula and checking its size, individual read counts, and all the listed examples is an NP computation with the fixed length-dependent data as advice. The penalty objective has the same upper bound.

For the converse, fix a polynomial-size Boolean verifier \(V_n\) for a monotone language. Monotonicity implies
\[
 x\in L \quad\Longleftrightarrow\quad
 \exists\, y,w \quad (y\le x\ \text{coordinatewise})\ \land\ V_n(y,w)=1.
\]
Keep \(y,w\) as ordinary Boolean variables. Introduce the verifier's gate values as further variables and enforce its local truth tables and accepting output with a fixed polynomial-size CNF of width at most three, using fan-in-two AND/OR/NOT gates. Repeat ordinary literals to pad short clauses to three positions. For each external bit add an additional three-position constraint \((\neg y_i,\neg y_i,d_i)\). The position \(d_i\) is an unconditional alternative available precisely when \(x_i=1\). Selecting some true or available position from every such constraint requires \(y_i\le x_i\). Every original position belongs to a fixed clause independently of \(x\).

Build a simple subcubic graph as follows. Ensure that every variable appearing in the CNF has at least two occurrences by adding fixed tautologies, such as \((v,\neg v,v)\), where necessary. For a variable with \(d\) ordinary literal occurrences, form an alternating cycle
\[
  T_1,F_1,T_2,F_2,\ldots,T_d,F_d
\]
of length \(2d\). Its independent sets have size at most \(d\), and equality forces one of the two alternating selections, encoding that variable's truth value. Create a triangle of three distinct records for every clause, one vertex per position even if two literals are repeated. Connect each ordinary position for occurrence \(j\) to the cycle vertex corresponding to its *falsifying* assignment: \(F_j\) for a positive literal and \(T_j\) for a negative one. The optional positions \(d_i\) receive no conflict edges. All degrees are two or three. For each degree-two vertex attach one new private vertex and connect those new vertices in a cycle. Fixed harmless tautologies ensure there are at least three new vertices. This makes a simple cubic graph \(B\). Its size is linear in the number of verifier clauses and external bits.

Let \(U(x)\) contain every original cycle vertex, every ordinary triangle position, and exactly the optional positions whose external bit is one. The padding vertices stay outside \(U(x)\). Put \(D=\sum_v d_v+\#\{\text{clauses}\}\). The induced graph \(B[U(x)]\) has independent-set size at most \(D\) by the cycle and triangle bounds. Equality requires an alternating choice in every variable cycle and an available, nonconflicting position from every triangle, and therefore witnesses \(x\in L\). A satisfying assignment gives equality by choosing precisely those records.

Apply the sparse sample construction to this one cubic graph. If \(m_B\) and \(n_B\) are its edge and vertex counts, its fixed threshold is \(4m_B+n_B-1-D\). The exact size identity from the companion note makes its budget query equal to \(L(x)\). The same identity for penalized errors gives the robust version. The data and threshold do not depend on \(x\). If one allows a bit and its complement as separate external flags, this also represents arbitrary languages in \(\mathrm{NP/poly}\) on that dual-rail domain. For the latter assertion use the monotone predicate that some certificate and some permitted assignment to all dual rails satisfy the verifier.

## One uniform family for clause deletion

A fully explicit family fixes all \(M=8\binom{n}{3}\) signed clauses on triples of distinct variables, for \(n\ge3\). An input bit says that its potential clause \(C=(\ell_1,\ell_2,\ell_3)\) is **absent**. For each potential clause use a fresh variable \(z_C\) and the two triangles
\[
 (\ell_1,\ell_2,z_C),\qquad (\neg z_C,\ell_3,d_C).
\]
The second triangle's last optional vertex is enabled by that absence bit. If the bit is zero, selecting a true literal in both triangles is equivalent, after choosing \(z_C\), to satisfying \(C\). If the bit is one, choosing \(z_C\) true and the optional vertex satisfies both constraints. Thus the decision function on switches is precisely satisfiability of the present 3-CNF. Ordinary 3-SAT can be restricted to distinct-variable width-three clauses in polynomial time by eliminating tautologies and replacing short clauses with their standard two- or four-clause paddings.

The variable cycles use \(10M\) vertices for \(5M\) ordinary occurrences, the triangles use \(6M\) vertices, and exactly \(6M\) additional vertices fill unused degree-two ports. The resulting cubic base has \(22M\) vertices and \(33M\) edges. Its sample has \(88M\) input coordinates and \(198M\) labeled examples. Exactly \(M\) permissions vary; the threshold is the fixed number \(147M-1\) of formula gates. Preprocessing these samples into polynomial-size general Boolean circuits for their permission predicates would imply \(\mathrm{NP}\subseteq\mathrm{P/poly}\).

## An unconditional querying lower bound

There is a separate fixed sample whose switch predicate is precisely \(k\)-CLIQUE on a graph with \(N\) vertices, with one switch for every possible edge \(uv\). Use ordinary guessed variables \(y_v\) specifying a vertex subset. A fixed width-three CNF enforces that at least \(k\) of the \(y_v\) are true. For example compute the threshold by the dynamic programming recurrence \(c_{i,j}=c_{i-1,j}\lor(y_i\land c_{i-1,j-1})\) and assert \(c_{N,k}\), using local gate consistency constraints. This costs \(O(Nk)\) clauses. For every unordered pair add the triangle \((\neg y_u,\neg y_v,d_{uv})\) whose optional position is present exactly when the edge is present. A subset of size at least \(k\) passes these checks precisely when it is a clique. The total cubic graph size, sample length measured in examples, and number of formula coordinates are all \(\Theta(N^2)\). The construction has only one variable permission per external bit and requires no input-dependent labels.

Known monotone circuit lower bounds for CLIQUE therefore hold for every monotone AND/OR circuit evaluating these fixed-sample permission queries, even after preprocessing each sample into an arbitrary length-specific circuit. For example take \(k=\lfloor N^{1/4}\rfloor\). The bound \(N^{\Omega(k)}\) gives \(2^{\Omega(Q^{1/8}\log Q)}\) gates for \(Q=\Theta(N^2)\) labeled examples. Improved clique approximation lower bounds also give \(2^{\widetilde{\Omega}(Q^{1/4})}\) at an appropriate choice of \(k\). These are lower bounds for monotone preprocessing outputs, not unconditional bounds for general Boolean query algorithms. [Cavalar, Kumar and Rossman](https://doi.org/10.1007/s00453-022-01000-3) [Hardness of Clique Approximation for Monotone Circuits, CCC 2025](https://doi.org/10.4230/LIPIcs.CCC.2025.4).
