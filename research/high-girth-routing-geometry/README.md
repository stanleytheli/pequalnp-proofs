# High-girth routing for the permanent

This package contains 24 Lean modules and two independent numerical implementations. It extends the immutable 41-module sparse-permanent foundation, whose source files are reproduced unchanged in `foundation/HighGirthMatchingProofs/`. The original archive SHA-256 is `68e13887c9b7c1735b2e3c71399eea74de99219e4bae7b43cef99d09d76515ab`.

The main finite theorem, `SparsePermanent.Contract.tight_routes`, supplies directed binary port trees and simultaneous protected routes for **all ordered pairs** of selected centers in a cubic bipartite graph. Its hypotheses quantify girth, available vertex count and edge expansion. `SparsePermanent.DirectedGrowth.Packed.simplePaths` removes repetitions while retaining disjointness, and `SparsePermanent.DirectedGrowth.Forest.protected_ends` restricts contact with the short branching trees to the endpoints of the assigned private link.

The accompanying mathematical proof combines this with published sextet girth and group-diameter estimates. For the indicated Biggs–Hoare sextet subfamily, the generic edge permanent projects to a dense matrix permanent of dimension at least `n^(1/15)/(log n)^O(1)`, with `n` vertices on each side. Every substitution is zero, one or an individual matrix variable and the identity holds over every commutative semiring. The asymptotic sextet estimate and the application of the tree-to-split schedule to every member of that family are paper arguments. The finite geometric hypotheses, the simultaneous routing, the split identities and the certificate checker's soundness have kernel proofs. The primary references, assumptions, constructive schedule and quantitative exponents appear in [sextet-routing.md](sextet-routing.md).

| Lean declaration | Content |
| --- | --- |
| `SparsePermanent.OrbitCounting.expands` | Transitive finite group actions convert a graph-diameter bound to edge expansion. |
| `SparsePermanent.Contract.directed_expansion` and `.girth` | Expansion and absence of short cycles survive contraction of a chosen perfect matching with explicit quantitative losses. |
| `SparsePermanent.DirectedGrowth.pack_twoWays`, `.Forest.from_boxes` and `.Forest.tight_pairs` | Pack disjoint centers' two-way neighborhoods, build binary port branches, then route all ordered pairs. |
| `SparsePermanent.Contract.tight_routes` | Complete finite geometric assembly. The center budget is `m·2^(2R+4)`; the terminal reserve is `m²(M+1+18k)`. |
| `SparsePermanent.order_girth_sharp` | The sharp finite order–girth tradeoff for the selector subdivision construction. |
| `SparsePermanent.Butterfly.permanent` | A unit-loop vertex with a unique nonloop predecessor can be removed over every commutative semiring. Parallel alternatives add in the compressed matrix. |
| `SparsePermanent.SplitCertificate.replay_sound` and `.Fast.certify_sound` | Ordinary list-based and balanced-tree certificate verification for a sequence of physical vertex splits. |
| `SparsePermanent.RoutedModel.embed_matrix` | Extend a matrix on any embedded subset of the host's matched pairs, retaining a unit matching on the complementary pairs. |

The Python scripts generate the actual prime-field graphs from projective-line transformations. For dimension 10 on the 2,870-vertex sextet and dimension 20 on the 16,206-vertex sextet, they verify every final physical edge and weighted matrix entry with two methods. The first reverses safe eliminations before replaying the resulting 704 and 3,128 splits. The second builds the branch trees from the centers and directly subdivides the private links, locating each of the 100 and 400 formal variables at its designated exit. These larger concrete computations were checked by the supplied Python controls. They have a different verification status from the general Lean modules in this archive.

## Reproduction

Use Lean 4.36.0 with prebuilt Mathlib commit `fc4f59e577feb1a4956671bc04ac18aaaf8cd842`. As in the base package, if Mathlib is a dependency of a larger project, set `MATHLIB_DEPS_DIR` to that project's `.lake/packages`. All 24 additional Lean modules are original Mathlib-only work. Each passed an individual compiler check against its prerequisite objects. The bundled source hashes, observed object hashes, and full successful axiom transcripts are in `verification/`. Printed declarations use only `propext`, `Classical.choice` and `Quot.sound`. The nested foundation includes its separate staged guest transcripts and upstream license information.

```sh
sh check-lean.sh /absolute/path/to/prebuilt/mathlib4
python3 checks/verify-adaptive.py
python3 checks/construct_splits.py
```

The shell driver extracts the foundation, compiles it into a fresh temporary directory, then builds the additional modules in dependency order. The numerical controls use only Python's standard library. None of these commands installs software or accesses a network service.
