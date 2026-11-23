# Girth-five edge functions through eight essential inputs

For every simple graph with no triangle or four-cycle, with at least one edge and at most eight nonisolated vertices, its monotone binary circuit complexity is exactly |E|+τ−1. Here τ is the minimum vertex-cover size, and the Boolean function accepts a vertex set precisely when it contains an edge. Gates can have arbitrary fanout. This is a finite case of L-meta-608 and includes all such subcubic graphs in L-meta-602.

| Nonisolated vertices | Isomorphism classes | Labeled graphs |
|---:|---:|---:|
| 2 | 1 | 1 |
| 3 | 1 | 3 |
| 4 | 3 | 19 |
| 5 | 5 | 167 |
| 6 | 12 | 2,061 |
| 7 | 25 | 34,639 |
| 8 | 66 | 775,713 |
| Total | 113 | 812,603 |

The upper bound partitions the edges into stars around a minimum vertex cover. A center with d assigned edges needs d−1 OR gates on its neighbors and one AND gate with its own input. Combining the star outputs adds τ−1 OR gates. Each member of a minimum cover has an edge to a vertex outside the cover, so every star can be chosen nonempty.

## Reproduce the finite computation

    python3 reproduce.py
    python3 reproduce.py --search

The quick command builds and simulates every star-cover circuit on its full truth table. The longer command also compiles three C++17 programs. The first independently constructs all admissible labeled graphs by edge insertion, verifies the partition into relabeling orbits, and recomputes the minimum vertex covers from all subsets. The remaining programs exhaust the circuit search. No solver or network is needed.

The search tests all singleton and pair assignments. Every nonisolated input is essential even on these tests; a neighbor singleton and the corresponding edge pair demand different answers. A connected binary output cone on n inputs has at least n−1 gates. Expand gates depth first from the output, using a leaf whenever a previously completed wire is reused. First explore the child with more undiscovered reachable gates. It introduces at least as many gates as its sibling. Tied positive discovery counts imply that the two remaining cones were disjoint and had equal size, allowing the first child to have smaller truth-vector popcount. Two child leaves can be ordered by wire discovery age, with old wires before new inputs. Inputs are named by first occurrence; every labeling of every target is checked at the output. At every internal node try both gates and discard outputs whose test vectors equal an earlier wire. A smallest circuit matching those tests cannot have such a redundant gate or any unused gate.

Results on singleton and pair assignments are lower bounds for the full function. With no isolates the minimum circuit on the tests can be normalized to a live binary circuit. Nullary constants, unary copies, and out-of-range references evaluating to false can be propagated away from its nonconstant output. Isolated vertices can also be fixed false; constant propagation cannot increase size.

## The last eight-vertex case

For every class except mask 53643800, sizes up to eleven suffice to verify the lower bound. This last graph has edges 04, 05, 14, 16, 25, 27, 36, 37, 47, 56 and a minimum cover of four, giving a target of thirteen. The general search excluded all sizes through eleven for this graph. The separate program checks twelve gates. Setting any of inputs 0 through 3 false leaves a seven-vertex graph whose singleton-and-pair optimum is eleven. Deleting one of inputs 4 through 7 leaves a seven-vertex graph with optimum nine. These eight lower bounds follow from the preceding complete seven-vertex search. Consequently, in a putative twelve-gate realization each of the first four restrictions can eliminate at most one gate, and the other four at most three apiece.

A gate can be deleted on a restriction if its test vector agrees with a primary input, a preceding wire, or zero on that restriction. All marked gates can be removed together in topological order. While a candidate is generated, reject it if any one restriction removes four gates, or if at least five restrictions remove two or more. These rejection rules are invariant under input relabeling. The additional root test only uses inclusion of the left operand's singleton-and-pair vector: at the final AND it must contain a target vector, and at the final OR it must be contained in one. The twelve-gate run visited 7,333,379,473 completed programs over its 1,030 discovery trees. It found none matching the target on the tests. Combined with the explicit upper bound, the optimum is thirteen.

## General Lean results

PairSafe.lean proves the lower bound at all sizes under a hypothesis on the AND gates. Each AND must avoid accepting any singleton or nonedge pair. Arbitrary nesting and fanout are allowed. Its theorem is conditional608. It imports the project's accepted L-meta-575 from upstream pull request 652. AffineIncidence.lean proves that the unrestricted L-meta-608 conjecture implies a lower bound of q³+q²−1 on 2q² inputs for the incidence graphs of affine points and nonvertical lines over a finite field of size q. The file checks the edge count, absence of short cycles, and a perfect matching. The finite catalogue lower bounds use the external enumeration described above.
