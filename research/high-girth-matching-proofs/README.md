# High-girth bipartite matching polynomials

This package derives arithmetic-circuit lower bounds for the perfect-matching polynomial of explicit sparse bipartite graphs. For dense dimension `m` and subdivision parameter `h`, the graph has maximum degree three, `2((h+2)m²−m)` vertices, and girth `4(2h+3)` for `m≥2`. Its polynomial specializes to the dense permanent by giving each graph edge the value of one input variable or the constant one. Over every fixed characteristic other than two, the exact and Laurent-approximate circuit lower bounds follow from the pinned upstream permanent theorem. A kernel-checked cubic completion gives logarithmic girth when supplied with cubic reservoirs of logarithmic girth. The sequence using sextet graphs can approach the coefficient `4/3` in front of `log₂ N`.

The strongest result is a mathematical proof for **the unmodified Biggs–Hoare sextet graphs themselves**. The explicit prime-field bipartite subfamily has girth greater than `(4/3)log₂N−2`. Its generic permanent has both circuit sizes at least `2^(Ω((log N)^(4/3)))`. The proof constructs a directed model of the complete permanent on `N^δ` indices, using protected binary trees and BFS in the complement of previous routes. See `sextet-routing.md` for the quantitative proof, independent prior work and primary references. The whole asymptotic sextet derivation has received two mathematical reviews. Its full Lean verification remains open. The checked components cover directed vertex splits, transfer of a split certificate to the edge polynomial, expansion after deleting vertices, an entire sequence of disjoint directed routes, and extraction of the required port data from full binary trees.

## Verified statements

| Local Lean declaration | Conclusion |
|---|---|
| `SparsePermanent.CoreMatching.equivOriginal` | Actual perfect matchings of the unsubdivided port graph are in bijection with permutations of the dense dimension. |
| `SparsePermanent.permanent_divideEdge` | Replacing one edge with a three-edge path preserves the specialized permanent over every commutative semiring. |
| `SparsePermanent.permanent_family` | After all designated joins receive all `h` subdivisions, the sparse permanent equals the dense permanent. |
| `SparsePermanent.degree_family`, `SparsePermanent.card_side` | Every neighbor set on either side has size at most three. The theorem gives the exact number of vertices on each side. |
| `SparsePermanent.count_operations`, `SparsePermanent.labels_family` | Each join is split exactly `h` times. The final matrix uses zero, one and original matrix entries. |
| `SparsePermanent.projects_to_perm` | The generic graph polynomial, with a different variable on each physical edge, has a zero/one/variable projection to the exact upstream dense permanent. |
| `SparsePermanent.Leaf.computes`, `SparsePermanent.Leaf.approximates` | Such projections preserve the exact same circuit-size parameter in both upstream models, including counting leaves as gates. |
| `SparsePermanent.exact_lower`, `SparsePermanent.approximate_lower` | Each local implication takes exactly the upstream theorem statement as its premise and returns the lower bound uniformly in `h`. |
| `SparsePermanent.family_girth_eq`, `SparsePermanent.family_egirth_eq` | Ordinary Mathlib simple-graph girth is exactly `4(2h+3)` for `m≥2`. |
| `SparsePermanent.order_girth_power` | For `h=m^q` and `m≥2`, the number of vertices satisfies `N^q ≤ girth^(q+5)`. |
| `SparsePermanent.exact_lower_order`, `SparsePermanent.approximate_lower_order` | For each fixed `q`, exact and approximate size exceed `2^(c_q(log₂N)^(4/3))` in every fixed characteristic other than two, for sufficiently large dense dimension. |
| `SparsePermanent.MatchExtension.family` (see `MatchExtension.lean`) | Each odd subdivision extends a physical perfect matching uniquely. |
| `SparsePermanent.Attach.complete`, `SparsePermanent.cubic_hard_family` | A balanced subcubic graph and a supplied cubic reservoir give a cubic graph preserving a common girth bound. Its generic permanent projects to the original generic permanent. For the selector family this transfers both exact and Laurent circuit budgets. |
| `SparsePermanent.Edges.family`, `SparsePermanent.Edges.deficit` | The subdivided graph has exactly `(2h+5)m²−4m` edges and `(h+1)m²+m` degree deficits on each side. |
| `SparsePermanent.RoutedModel.projects` | A directed model obtained by incoming and outgoing vertex splits, embedded with a fixed complementary matching, certifies the exact dense-permanent projection over every commutative semiring. |
| `SparsePermanent.DirectedGrowth.connect`, `.link`, `.pack`, `.Forest.port` | Expansion gives a bounded-length directed walk after vertex deletions. Binary trees supply private leaf groups, and each demand receives a disjoint support under explicit capacity bounds. |

`k` in the source represents dense matrix dimension `m=k+1`. The matrix permanent convention is `∑σ ∏i A(σi,i)`. The four lines defining `genericPermanent` give an independent variable to every permitted entry while defining the other entries as zero.

The authoritative replay ran in the isolated `lean-work` guest using Lean 4.36.0 and prebuilt Mathlib commit `fc4f59e577feb1a4956671bc04ac18aaaf8cd842`. The guest independently rebuilt the eleven base modules from fresh objects, then checked thirteen new geometry, scaling and padding modules against those freshly built objects. Seven further modules established the cubic construction and its weighted matching projection. An eighth linked these lemmas to the upstream exact and approximate circuit definitions. A further nine modules verified the exact edge count and directed routing components. All five Python checks also ran in the guest. The guest logs are in `verification/guest-*.log`. Printed proof dependencies were `propext`, `Classical.choice` and `Quot.sound`.

A preceding local development check also elaborated the adapted upstream definitions. The upstream proof was verified separately by its own comparator with Lean 4.33.1. To port its definitions to Lean 4.36.0 the local adapter changes two applications of `MvPolynomial.coeff` to method syntax. The bridging theorems take the upstream conclusions as assumptions. The combined proof chains have separate verification environments.

The mathematical note supplies the asymptotic reservoir choices and sharper dimension-to-order tradeoffs. The five Python computations check the concrete instances described below.

## Reproduce locally

Use an isolated Lean environment and the already-built Mathlib checkout at the commit above, with the matching Lean version selected by its `lean-toolchain`. When Mathlib is itself a dependency of a larger project, set `MATHLIB_DEPS_DIR` to that project’s `.lake/packages` directory. From this unpacked directory run the following commands. The shell driver compiles each source against that checkout and writes fresh `.olean` files to a newly created temporary directory. It does not install dependencies or invoke GitHub.

```sh
sh check-lean.sh /absolute/path/to/prebuilt/mathlib4
python3 checks/verify_graph.py
python3 checks/regular_complete.py
python3 checks/reservoir.py
python3 checks/sextet.py
python3 checks/sextet_routes.py
```

The first Python check enumerates 612 matchings across 20 graphs and compares every monomial multiplicity with the dense permutation sum. The second checks six complete switching constructions. The third checks nine reservoir constructions using three different cubic bipartite graphs, verifies actual girth by breadth-first search, and enumerates the monomials after zero-edge specialization. The fourth generates two unmodified Biggs–Hoare sextet graphs from projective-line transformations. The fifth finds physical permanent projections of dimensions five and seven and verifies all 120 and 5,040 surviving monomials. Both finite sextet experiments have been reproduced in the isolated guest. No Python package beyond the standard library is required. `verification/` contains the original development logs and the complete guest replay. `SHA256SUMS` covers all package files other than itself.

## Sources and scope

The source of the dense lower bound is Anthropic’s [pinned theorem statement](https://github.com/anthropics/formal-math/blob/11b6c7e3c927df2658f513b6b68ea7f8929c62c5/vp-vnp/Statement.lean). Its [independent comparator job](https://github.com/anthropics/formal-math/actions/runs/45272623486/job/138036167794) verified the upstream release. The full project source and the dependencies are external to this package. `upstream-review.md` records their pins and the verification chain.

Valiant’s 1979 Proposition 8 already gives weighted subcubic bipartite matching completeness and an odd-path embedding. The specific port gadget, regular graph switching and the sextet reservoir family also have classical precedents cited in the mathematical note. This package provides their weighted projection and the transferred exact and formal-approximation bounds. It does not establish Boolean `P ≠ NP`, and makes no claim of priority for the constructions.
