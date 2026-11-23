# The full refund inequality on at most eighteen input variables

The L997 inequality holds for every instance on at most eighteen input variables. This is a mathematical corollary of the Lean-checked counting results together with the following finite incidence argument and gate argument. The last gate argument has been independently reviewed as a mathematical proof. The package's Lean statements cover the gate-count ingredients and local-rank theorems.

## Necessary incidences for a counterexample

If the circuit has no NOT, the ordinary monotone private-gate theorem gives the conclusion. The two window bounds give it also for minimum firing weight \(k\le2\). Assume henceforth \(k\ge3\), and let \(v=n-k\) be the number of input variables outside the minimum witness \(Y\).

Call a disjoint row oversized when its size is at least \(k+2\). Let these \(t\) sizes be \(s_1\ge\cdots\ge s_t\). The light bound charges \((\min(k,|S_i|)-1)_+\) per row and reserves \(k\) further gates. It can charge the largest row its full \((s_1-1)\) instead, by `full_one_row997`. Each disjoint row of size at least two also provides a distinct refund unit. A disjoint row of size at most \(k+1\) has deficit at most this one refund, and empty and singleton rows have no deficit. Therefore any counterexample must have \(t\ge2\) and
\[
 \sum_{j=2}^{t}s_j\ge t(k+1)+1.
\]
Indeed the remaining excess after the largest row is charged is \(\sum_{j=2}^t(s_j-k)\); the reserves and the \(t\) refunds already pay \(k+t\).

Let \(I=\sum_j s_j\) and \(A=\max(t(k+1)+1,(t-1)(k+2))\). The preceding inequality gives \(I\ge A+\lceil A/(t-1)\rceil\). Put \(F(v,I)=(v-r)\binom d2+r\binom{d+1}2\), where \(I=dv+r\), \(0\le r<v\). This is the smallest sum of degree pairs on \(v\) points with total incidence \(I\), by transferring one unit from a degree exceeding another by at least two. Distinct rows meet in at most one point, so
\[
 F(v,I)\le\binom t2,\qquad t\binom{k+2}{2}\le\binom v2.
\]
For \(n\le18\) we have \(v\le15\), and \(k=3\) gives the least demanding inequalities. Thus \(t\le10\). Here are all possible row counts, with \(I_0=A+\lceil A/(t-1)\rceil\) at \(k=3\).

| \(t\) | 2 | 3 | 4 | 5 | 6 | 7 | 8 | 9 | 10 |
|---|---:|---:|---:|---:|---:|---:|---:|---:|---:|
| \(I_0\) | 18 | 20 | 23 | 27 | 30 | 35 | 40 | 45 | 50 |
| \(F(15,I_0)\) | 3 | 5 | 8 | 12 | 15 | 25 | 35 | 45 | 60 |
| \(\binom t2\) | 1 | 3 | 6 | 10 | 15 | 21 | 28 | 36 | 45 |

Only \(t=6\) survives, and its inequalities require \(v=15\), \(k=3\), and \(I=30\). Equality forces six rows of size five and every point in exactly two rows. Every pair of rows must meet. Consequently the outside variables are the 15 edges of \(K_6\) and the six row sets are its vertex stars. The supplementary Python verifier recomputes the incidence bounds for larger values of \(k\) as well.

## Excluding the six-star configuration

Let \(c_i=(\min(3,|S_i|)-1)_+\). In the true pin, let \(L_i\) be the whole-domain gates false at the empty assignment with a singleton support of size at least two contained in \(S_i\). They are pairwise disjoint, and \(|L_i|\ge c_i\). The three reserve slots are disjoint from them. Take exactly three of the reserve slots, including the pinned NOT. Let \(X\) be the other gates outside all \(L_i\). A row disjoint from \(Y\) and different from the six stars is a matching in \(K_6\) and thus has size at most three. Such a row of size two or three supplies an additional refund with no deficit. One such refund proves the result immediately by charging one star in full. Thus assume there are no such additional rows.

The six stars each have deficit two beyond the light count. Their six refunds and the three reserves leave a total deficit of three. A violation, by integrality, forces
\[
 |X| + \sum_i (|L_i|-c_i)\le 2.
\]
Empty outputs can only improve this inequality. Select any star \(S_j\). The checked `false_full_cut997` supplies four gates false at empty whose singleton supports meet \(S_j\) in at least two points. It applies because the pinned output is false at empty and true on each singleton in \(S_j\). The three reserve slots are excluded by their constant or empty singleton behavior. No \(L_i\) for \(i\ne j\) can supply one of the four gates. Therefore \(|X|+(|L_j|-c_j)\ge 2\) for **every** star. Along with the preceding total bound this forces every excess to vanish, \(|X|=2\), and both of these slots are false at empty and have at least two singleton-support points in each of the six stars.

Consider the first of the two slots in circuit order. Before it, every false-at-empty signal with at least two singleton-support points belongs to the private class of a unique row; the reserved prefix gates have empty singleton supports. Fix such an earlier private wire with support size \(r\). It requires at least \(r-1\) earlier-or-current private gates of its own row. To see this, expand its predecessors, processing each gate once in reverse circuit order. At a false-at-empty OR whose support lies in the row, both predecessors' singleton supports lie in the row. At an AND, a true-at-empty predecessor may be omitted since it is always true. Every other predecessor has support containing the AND output support, so whenever the latter has two or more points, every such predecessor must be private to the same row by linearity. Stop a branch once its wire has at most one singleton point. The resulting frontier covers the original \(r\) points and has size at most one plus the number of private gates expanded. This argument also allows missing inputs, duplicate reads and gates with fewer than two inputs.

No pre-\(X\) private wire can see three outside points. Indeed it would then need at least two of that row's private gates, its entire budget since \(c_i\le2\). If its support is a proper subset of its row, the row's final output is a third distinct private gate: the pin computes the correct singleton and empty values because \(k=3\). Even if the output precedes this wire, a size-three support made with at most two private gates uses only itself and, when needed, one size-two predecessor. Neither can be the distinct output with a strictly larger support. If the support is the entire row, a meeting row also has a point of \(Y\) and a star has five points. Both would need at least three private gates. A disjoint row of size three was excluded above.

A first \(X\) wire is false at empty. For an OR with that property both predecessors are false at empty. An AND can ignore any true-at-empty predecessor. Thus its singleton support contains at most four outside points. Each outside point belongs to exactly two stars, so these points supply at most eight incidences. The required two points in each of the six stars need twelve. This contradiction excludes the sole remaining incidence profile. ∎
