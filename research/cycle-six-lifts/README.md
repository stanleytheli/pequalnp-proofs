# Six-cycle with two leaves at adjacent vertices

Desk problem L-meta-523 requests an 11-gate monotone circuit with a nested pair of AND gates and no admissible lift that reduces the number of such pairs. The graph has edges 01, 12, 23, 34, 45, 50, 06, 17. An exhaustive search found that every nested 11-gate circuit for this graph admits such a lift. There are 11-gate circuits for this graph.

## Reproduce

Use a C++17 compiler and Python 3. Run these commands in this directory.

    c++ -O3 -std=c++17 enumerate.cpp -o enumerate
    ./enumerate 7 11 0 10000
    python3 validate.py --complete

The last two arguments select a half-open interval of discovery-tree indices. The executable writes the candidates at size 11 to pair-candidates.txt. A copy from the original run is included. The Python checker independently evaluates every candidate, searches the legal lifts, simulates the transformed circuits, and counts comparable AND gates via a graph traversal.

## Completeness of the finite search

Test a circuit first on the 28 assignments with exactly two inputs set. Every circuit matching the target on just those tests uses all eight input variables. Otherwise, if it omitted variable i, take a neighbor j of i. Monotonicity and dependence only on the other variables force output true on the singleton j. There is a k distinct from i and j that is nonadjacent to j, so the nonedge test jk would then incorrectly return true. A connected binary output cone on eight essential variables needs at least seven gates by counting its edges.

Among the circuits matching the pair tests, take one of minimum size. Every gate belongs to its output cone. No gate can have the same pair truth vector as an earlier wire, since it could be deleted and its uses redirected. The output may always be placed last. The search found no pair matches through size ten. It follows that every 11-gate circuit computing the requested graph is already minimum for the pair tests. Discarding duplicate truth vectors and unused gates thus preserves every circuit of interest, including its nested-AND structure. Operands in the desk statement must be earlier wires and every gate has exactly two operands.

Explore the output cone depth first. First-time gates give internal nodes of a binary tree. Repeated gate references and input references give leaves. At each gate explore first the operand with the larger set of as-yet-undiscovered reachable gates. The first operand discovers all of its set. The second operand can only lose undiscovered gates. Thus the first subtree is at least as large as the second. If the resulting sizes are equal and positive, both original sets were equal in size and disjoint. In this case either order is possible, so the first operand can have the smaller popcount of its pair vector. Two child leaves can likewise be ordered by discovery age, with already discovered wires before fresh inputs. Two references to the same wire give a redundant gate. Fresh input names are assigned by first appearance. All permutations of the eight graph vertices are accounted for at the output. Popcount is invariant under simultaneous input relabeling.

The code generates all binary discovery trees meeting these conditions, tries both gate operators and every admissible reference at each node, and rejects gates with duplicate pair vectors. Lift eligibility, full-function correctness and the strict decrease in nesting are all invariant under permutations of inputs, commuting a gate's operands, and topological renumbering of gates. The output remains the last gate. A lift duplicates the kept input of an OR gate and appends an OR of the previous output and the lifted wire. Every gate that consumes a changed wire occurs after that wire in every topological ordering.

## Results

At size eleven the search completed 8,150,828,190 programs across 481 discovery-tree shapes. The counts are representations after the stated pruning. Some circuits can have multiple representations.

| Outcome | Representations |
|---|---:|
| Matched the 28 pair assignments | 1,174 |
| Failed on one or more of the remaining assignments | 76 |
| Correct on all 256 inputs, with no comparable pair of AND gates | 702 |
| Correct on all 256, with a comparable pair and a reducing lift | 396 |
| Correct on all 256, with a comparable pair and no reducing lift | 0 |

For each of the 396, Python explicitly checks both output truth tables, the lifted wire implication on every input, and the old and new numbers of comparable AND pairs. A separate run without the equal-child and leaf-order pruning also searches the less restricted set of discovery trees.

Control.lean is a separate kernel-checked positive example against the project's circuit semantics. It includes a proof equating the project's transitive-reachability set cardinality with a computable finite count. Its explicit 11-gate circuit has one comparable pair of AND gates, and the displayed lift reduces this count to zero. Both compute the same target on all 256 inputs. The exhaustive lower bound and classification above are external computations. The Lean file was checked using Lean 4.36.0 and project revision a285ace2301a31d8cdea9fd9e718bca202b4d06d.
