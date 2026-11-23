# Exact positive cases of the one-NOT refund bound

Let the inputs be indexed by a finite set, and let the circuit compute the OR of each of the sets \(S_1,\ldots,S_m\) of a linear family. Distinct sets in the family share at most one input. Suppose the only NOT negates a monotone wire \(h\). Let \(Y\) be a minimum-cardinality input set where \(h\) is true and put \(k=|Y|\). Here a set means the Boolean assignment with exactly its elements present. Write \(N\) for the circuit size. The physical circuit may have arbitrary fan-out. All other gates have at most two inputs and are ANDs or ORs.

L997 asks for the sum of full sizes of rows disjoint from \(Y\) and truncated sizes \(\min(k,|S_i|)\) of all meeting rows to be at most \(N+m+R\). A gate contributes to \(R\) when its singleton support is one of the full rows and its support on the assignments \(Y\cup\{p\}\), for \(p\notin Y\), is a full row disjoint from \(Y\). Every disjoint row with at least two points contributes a distinct refunded output gate.

## Selecting a full row

Let \(P\) be a set of inputs. Write \(a_i=\min(k,|S_i|)\) and \(b_i=|S_i\cap P|\). If \(h(P\setminus S_i)=0\) whenever \(b_i>a_i\), then
\[
 N\;\ge\;k+\sum_i(\max(a_i,b_i)-1)_+ .
\]
This is `rowwise_first997`. In particular, for \(k\ge1\), select **any one** row \(S_j\) and take \(P=S_j\). A distinct row has \(b_i\le1\), and the selected row has \(h(P\setminus S_j)=h(\varnothing)=0\). Thus its full charge \((|S_j|-1)_+\) and the ordinary truncated charges of all other rows coexist. See `full_one_row997`.

To prove this, pin the NOT output to true, giving a monotone circuit \(C_1\). A whole-domain gate assigned to row \(S_i\) has its singleton support contained in that row and of size at least two. The low-weight cut provides \((a_i-1)_+\) such gates. For the restricted count, intersect the singleton supports with \(P\). A gate assigned to \(S_i\) has at least two restricted support points, all in \(S_i\). A binary cut around the output supplies at least \((b_i-1)_+\) such gates when the output is false at \(P\setminus S_i\). Indeed the remaining cut frontier has at most one point per wire which is false on that assignment. Those wires must collectively distinguish each singleton in \(S_i\cap P\) from that assignment. We exclude the constant-true pin slot itself. A whole and a restricted charge can coexist at one gate for distinct rows only if its restricted support of size at least two belongs to both, contradicting linearity. The same reasoning separates two restricted charges. The \(k\) reserve positions comprise the NOT and at least \(k-1\) prefix gates with empty singleton support that are true at \(Y\).

## Deleting a transversal

Take \(P\) with \(h(P)=0\). If every disjoint row loses at most one point outside \(P\), then the exact L997 inequality holds by `thin_deletion997`. The first loss for each nontrivial disjoint row is paid by its own refunded output gate. Empty and singleton rows need no extra charge.

Alternatively suppose every disjoint row is contained in \(P\cup H\) for a common deletion set \(H\) with \(\binom{|H|}{2}\le k\). Then the exact L997 inequality holds by `small_transversal997`. A row with \(r\) points in \(H\) loses at most \(r\) units, and \(r\le1+\binom r2\). Different rows contain disjoint collections of pairs in \(H\). The sum of all charges left beyond the first refund is therefore at most \(\binom{|H|}{2}\), which the reserved positions pay. For instance one can take \(P\) to be the union of disjoint rows with a transversal of its \(h\)-minterms removed.

## Nested subcubes and local activation ranks

Assign each row a subcube \(P_i\), with all the \(P_i\) pairwise comparable by inclusion, and an integer \(k_i\). Suppose \(h(Z)=0\) for all \(Z\subseteq P_i\) disjoint from \(S_i\) with \(|Z|<k_i\). Then the checked `chain_first997` gives
\[
 N\ge k+\sum_i(\min(k_i,|S_i\cap P_i|)-1)_+.
\]
For each row, use the low-weight cut on the restricted singleton supports. Its outside witnesses now lie in \(P_i\setminus S_i\). When two assigned gates coincide, use the smaller of their two domains. Its at least two support points lie in both rows, contradicting linearity.

For an exact L997 consequence, let \(B\) be the union of the disjoint rows. Suppose every disjoint row \(S_i\) has \(h(Z)=0\) for \(Z\subseteq B\setminus S_i\) of size below \(|S_i|\). Take \((P_i,k_i)=(B,|S_i|)\) for disjoint rows and \((P_i,k_i)=(\mathrm{all},k)\) elsewhere. This proves the stronger inequality with \(k\) on the left and no refunds on the right; see `local_rank_exact997`. Thus failure requires an additional true input confined to the union of disjoint rows, avoiding some disjoint row, with fewer points than that row's size.

## A 400-gate threshold case for the plane of order seven

Work in \(\mathbb Z/57\mathbb Z\). The lines are the translates \(S_i=i+\{0,1,3,13,32,36,43,52\}\). Give line \(i\) the base \(O_i=i+\{5,14,20\}\). Each base avoids its own line. For every \(i,j\), either \(O_i\) avoids \(S_j\) or \(O_j\) avoids \(S_i\). Translation symmetry reduces this finite check to 57 offsets. If \(h(O_i)=1\) for every \(i\), pin the NOT output to false. Each output is globally sound for its line, and it is true on every \(O_i\cup\{p\}\) with \(p\in S_i\). The monotone private-gate lemma supplies seven gates per line. Its disjointness condition is exactly the cross-avoidance verified above. The 399 assigned physical positions omit the constant-false pin slot, giving \(N\ge400\). See `oriented400997` and `plane57_threshold_three997`.

## The remaining overlap

Taking private gates independently in the true and false pins can charge the same physical slot twice without earning a refund. Let \(h=a\land b\land c\), \(Y=\{a,b,c\}\), and form
\[
 w=((\neg h)\land(p\lor q))\lor(h\land(u\lor v)).
\]
Its singleton support \(\{p,q\}\) is a proper subset of \(\{a,p,q,r\}\). Its false-pin support above \(Y\) is \(\{u,v\}\), a proper subset of the disjoint row \(\{u,v,z\}\) for which the pinned gate is globally sound. Computing both requested outputs with ordinary OR trees produces a legal circuit satisfying the L997 inequality. The example demonstrates the overlap of two proposed charges. A general result must pay for this overlap or choose a different assignment of gates.
