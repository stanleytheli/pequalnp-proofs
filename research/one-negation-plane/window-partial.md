# Two certified counting approaches to L-meta-997

Write \(k=|y|\) and \(N\) for the physical gate count. Let \(D\) be the number of outputs whose set is disjoint from \(y\) and has at least two points. For a nonnegative integer \(u\), write \((u-v)_+=\max(0,u-v)\).

The L997 bound follows if either numerical condition holds:

\[
 \sum_{i:S_i\cap y=\varnothing} (|S_i|-k)_+\le k+D,
 \qquad\text{or}\qquad
 \sum_{i:S_i\cap y\ne\varnothing} (\min(k,|S_i|)-2)_+\le k+D.
\]

We give separate arguments for the two sufficient conditions. In particular they cover every family when \(k\le2\), every family with \(\max_i |S_i|\le k+1\), all-disjoint families, and all-meeting families. An empty disjoint output set contributes zero to the first sum.

If the circuit contains no NOT, the checked monotone private-gate argument (L988 with common empty bases) gives the full sum bound. Otherwise the unique NOT is at the stated index. Replace it by a constant-true gate to obtain the monotone circuit \(C_1\) and by a constant-false gate to obtain \(C_0\), preserving all gate positions. The actual NOT input \(h\) is monotone. The NOT is false on \(y\), hence \(h(y)=1\). It is true at all inputs of weight below \(k\), hence \(h\) vanishes there. If \(k=0\), monotonicity makes \(h\) constant one, so \(C_0\) computes every original output on every input and L988 applies. We henceforth take \(k\ge1\). These observations hold with the project's missing-reference default and variable arities. A NOT that fires false has a real, earlier, true input wire.

## Reserved gates before the NOT

At least \(k-1\) gates of the monotone prefix fire at \(y\) and fire at no singleton input. To see this, expand the wire for \(h\) backwards through every gate with those two properties. Process gates just once in reverse order. Each binary expansion increases the frontier size by at most one. If at most \(k-2\) gates were available, the final frontier would have at most \(k-1\) wires. For each frontier wire true at \(y\), select a singleton that fires it, possible for a raw input or for any true gate remaining outside the expanded class. An out-of-range wire is false. On the union of all selected singleton inputs, monotonicity fires every frontier wire that was true on \(y\), and thus fires \(h\). The union has size below \(k\), a contradiction. Choices may use points outside \(y\), which is why the first-weight hypothesis on all smaller inputs matters. These prefix gates and the NOT itself give \(k\) distinct physical positions.

Each of the \(D\) disjoint nontrivial output sets also contributes a distinct unit to the refund of L997. Its final output must be a gate since no input or missing wire computes a set OR of size at least two. On every singleton its support is its full set; on the heavy inputs \(y\cup\{p\}\), for \(p\notin y\), its support is again its full set. Distinct nontrivial sets in the linear family differ, so their output gates differ.

## Light window

In \(C_1\), give set \(S\) the gates false on the empty input whose singleton support is contained in \(S\) and has at least two points. Different sets have disjoint gate classes by the intersection hypothesis. Neither a reserved prefix gate nor the constant-true replacement can be in these classes.

For one output, expand all its assigned gates backwards once. Suppose the available gates plus one are fewer than \(\min(k,|S|)\), so the final frontier is smaller than both \(k\) and \(|S|\). Ignore wires true at the empty input, since they are always true. Of the remaining frontier wires, every one whose singleton support is contained in \(S\) sees at most one point. Pick \(p\in S\) outside all these singleton supports. Every other frontier wire has a singleton witness outside \(S\). Choose one such witness per wire and take their union \(Z\). It misses \(S\) and has size below \(k\), so \(C_1\) agrees with the original circuit there and its output is false. Yet \(C_1\)'s output is true at singleton \(p\), since replacing the NOT by true can only increase the original result. Every frontier wire true there is true on \(Z\), either because it is constant-true or because its chosen outside witness belongs to \(Z\). This forces the output true on \(Z\), a contradiction.

Summing now gives \(\sum_i\min(k,|S_i|)\le N-k+m\). The first sufficient condition spends at most the \(k\) reserved positions and the \(D\) refunds to change every disjoint-set term to its untruncated size.

## Heavy window

Every \(C_0\) output is globally sound for its set, since replacing the NOT by false can only decrease the original output. On all inputs containing \(y\), \(h\) remains true, so \(C_0\) agrees with the original circuit. For each \(S\) disjoint from \(y\), use the L988 private-gate argument with base \(y\) to obtain \(|S|-1\) gates. An assigned gate is globally sound for \(S\) and fires on at least two inputs of the form \(y\cup\{p\}\); soundness implies that each such point belongs to \(S\), so distinct disjoint-side output sets cannot share an assigned gate. The assigned gates are all false at \(y\). This excludes the reserved prefix gates, and the constant-false replacement has no firing points.

For each meeting output with \(\min(k,|S|)\ge2\), allocate its own final output gate. These gates are distinct. They are true at \(y\), exclude every heavy assigned gate, and differ from all reserved prefix gates because their actual singleton support is their whole nontrivial set. None is the NOT, since its value at \(y\) is false. Thus all disjoint outputs can pay their full sizes, and the meeting outputs can pay up to two apiece, using \(N-k+m\). The second sufficient condition pays the rest from the reserved positions and refunds.

## Remaining joint-counting problem

The two arguments do not establish that every low-support and heavy-support gate pair shares only at the refunded full-output boundaries. For example, let \(h=a\land b\land c\), let \(t=\neg h\), take \(y=\{a,b,c\}\), and form

\[
 w=(t\land(p\lor q))\lor(h\land(u\lor v)).
\]

Its light singleton support is \(\{p,q\}\), a proper subset of the meeting set \(\{a,p,q,r\}\). In the false pin it is globally sound for \(\{u,v,z\}\) and its heavy support is \(\{u,v\}\), another proper subset. Add ordinary OR trees for these two outputs to give a legal test circuit. Gate \(w\) belongs to both straightforward charged classes and supplies no full-on-both refund. This example pinpoints a failure of the direct disjointness argument. It satisfies the inequality because it has other gates to spare. Additional charging or a genuine violating circuit is still needed in families outside the two criteria.
