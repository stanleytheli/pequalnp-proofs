# Exact monotone circuit sizes for six-vertex edge functions

For each simple graph without isolated vertices on six vertices, the function accepts a set of vertices if that set contains an edge. The catalogue gives its minimum number of binary AND and OR gates. Wires can be reused. All 122 isomorphism classes are represented. Graph labels and programs are in catalogue.json.

| Minimum gates | Graphs |
|---:|---:|
| 5 | 7 |
| 6 | 10 |
| 7 | 24 |
| 8 | 25 |
| 9 | 33 |
| 10 | 15 |
| 11 | 7 |
| 12 | 0 |
| 13 | 1 |

The cycle C6 requires 8, the triangular prism 10, the five-rim wheel 11 and the complete graph K6 13. K3,3 requires 5. A graph mask uses the pairs (0,1), (0,2), …, (4,5) in lexicographic order, beginning at its least significant bit. The stored mask is the least of all its vertex relabelings. Gate triples give the operation (0 for OR, 1 for AND) and two wire indices. Wires 0 through 5 are primary inputs.

## Verify and reproduce

    python3 verify.py
    c++ -O3 -std=c++17 catalogue.cpp -o catalogue
    ./catalogue 5 10
    c++ -O3 -std=c++17 threshold.cpp -o threshold
    ./threshold 3 2 4 1 0 10000
    ./threshold 4 4 7 4 0 10000
    ./threshold 5 7 10 7 0 10000
    ./threshold 6 10 13 10 0 10000

The Python verifier constructs all labeled graphs with no isolates, checks that the isomorphism classes partition that set, and checks all 64 truth-table entries of every saved witness. The full-truth-table catalogue search exhausts sizes five through ten and discovers 114 of the 122 classes. The supplied witnesses for seven further graphs have size eleven, so this same exhaustive search proves their optimality. Rerunning the catalogue program through eleven also rediscovers these witnesses. The separate threshold search establishes the remaining class K6. The bounds in this catalogue are finite computational results outside Lean.

For the general catalogue, choose a smallest circuit computing the function. Every input is essential, since turning it on alongside one neighbor changes the answer from false to true. Every gate is reachable from the output; a connected binary cone with six inputs therefore needs at least five gates. No two wires in a minimum circuit have the same full truth vector. If they did, uses of the later wire could be redirected and its gate deleted. Constants and copying gates, if admitted, can first be eliminated without increasing size since the target is nonconstant.

Traverse backwards from the output. A first visit to a gate creates an internal node of an ordered binary discovery tree. An input or a reference to a previously completed gate creates a leaf. Visit first the child that initially reaches more undiscovered gates. It discovers all of these, whereas the other child can only lose new gates; the first thus introduces at least as many as the second. Equality of positive discovery counts implies that the original undiscovered cones were disjoint and equal in size. In that case the first child's truth vector may have the smaller population count. Two child leaves can be ordered by discovery age, with new inputs last. The program generates all such discovery trees, all legal references, both gate operations, and introduces inputs by first occurrence. Its terminal lookup checks the complete truth table against all input permutations. A second traversal with the equal-size-population and leaf-order restrictions removed gave the same minima through ten.

## Proving the remaining case

K6 computes the threshold-two function on six variables. It is fully determined among monotone functions by the false singletons and the true pairs. This allows the independent threshold search to use only those rows of the truth table. Replacing equal wires on these rows preserves correctness.

Let b be a proved lower bound for threshold two on m−1 variables. Setting any input i of an m-variable candidate to zero leaves precisely that smaller threshold function. Every gate whose restricted test vector agrees with an earlier wire or with zero can be removed, redirecting uses and propagating constants. These removals can be made together by processing the gates in topological order. If a prefix already contains more than k−b removable gates for a single restriction, that prefix cannot lead to a size-k circuit. The search computes this bound separately for every possible i. A difference between two test vectors disappears under i=0 exactly when every assignment where they differ contains i. An integer lookup table takes the intersection of those assignments to identify all such i at once.

Starting with the two-variable AND (one gate), the exhaustive searches give successive minima of 4, 7, 10 and 13 on three, four, five and six inputs. The size-12 run completed 15,824,537 programs after pruning and found no candidate. The size-13 construction in the catalogue was independently simulated on all 64 inputs. Every positive search size below the previous lower bound is also impossible by restriction.
