# Unrestricted De Morgan prefix search

The search uses full truth tables for the OR of graph edges. A smallest circuit for the nonconstant function on an isolate-free graph has a live output cone. Constant gates, semantically duplicate wires, repeated-input binary gates and irrelevant inputs can be eliminated. Missing or future wire references in the project model have value false and can be folded. A NOT reads its one effective input. The search represents it as a repeated descriptor with one actual reader slot.

## Fanout and a coordinate's sensitive pairs

For n essential inputs, k gates and u unary NOTs, the wiring has 2k−u edges. Count the final output as receiving an extra external reader. Every wire has positive fanout in the resulting cone, so the sum of fanout excesses is 2k−u+1−(n+k). Equivalently k−n+1 is u plus the sum of fanout excesses. Thus a prefix has already spent its number of NOTs, the excesses of its readers, and one extra for each already-read wire the suffix reads again.

For coordinate i, take every independent assignment x excluding i where adding i creates an edge. The suffix output differs on the pair (x,x∪{i}). Unless the suffix reads raw i directly, some gate at the prefix/suffix boundary must differ on the pair. This difference can point either way when negations are available. The search enumerates exactly which already-read gate wires the suffix may reread, allows every gate with no prior reader, and requires an extra raw-i reread if those gates fail to distinguish some pair. Untouched raw inputs add no prefix fanout cost. For an actual completion its exact gate-read pattern is enumerated with a weak lower bound on its raw rereads.

The machine word indexing checks full independent assignments with x_i equal to zero. For i<6, the row offset within its word can increase by 2^i without crossing a word boundary. For i≥6, flipping the coordinate xors the word index with 2^(i−6). The implementation intersects the unsigned XOR with the sensitive base rows.

## Restriction, constants and unused gates

The residual edge function on K, with optional extra OR literals attached by pinned one-vertices, has normalized lower bound at least the established bound for K. Setting each extra essential literal to zero saves a gate, also in the unrestricted circuit model. The remaining edge function is nonconstant.

Let p be the number of pinned original inputs and G the set of gates whose value is forced by constant propagation. The outgoing wires from these constants number p+|G|+∑fixed(fanout−1). Of those wires, ∑g∈G c(g) feed gates in G, where c(g) counts fixed operand slots with their actual arity. Every remaining wire feeds one distinct nonconstant boundary gate whose other input survives. Thus the number eliminated is p+∑fixed(fanout−1)+∑g∈G (2−c(g)). A unary NOT with fixed input has c(g)=1 and contributes one. A unary NOT with variable input survives as an ordinary gate. Constant propagation can safely remain syntactic in the presence of semantic complements.

After contracting boundaries and removing constants, every ordinary prefix gate used by the remaining output has a path to some prefix/suffix entrance. Include all zero-prefix-read gate tips and the exact chosen already-read gate entrances, then take their ancestor union in the restricted prefix. Ordinary gates outside this union contribute additional removals disjoint from the fixed/boundary charge. The replay in this directory marks live gates by a reverse pass instead of building ancestor bitmasks.

## Lexicographic cuts and scope

After choosing minimum size, take the least topological descriptor string over orderings and board automorphisms. An unblocked candidate can move earlier than any larger descriptor following the point its last input was defined. Such a move improves the descriptor at the earliest difference. An automorphism fixing every earlier unordered gate operand pair can likewise improve a candidate's pair, so both conditions hold together. Full truth-table comparison handles equivalence, constants and possible completion before canonical gate deletion. Reaching the depth cap without a proof returns unknown.

The seed parameter asserts the exact size m+τ−1 for every isolate-free induced graph through that order in the unrestricted gate model. No equality bound should be seeded from a solely monotone argument. The full graph must be isolate-free. For VERTICES at most 11 the input graph mask fits the 64-bit graph reader. The larger variant uses a wider graph mask and a different seed. Its raw support shortcut uses essentiality of every input.

## Reproduction

The 10-vertex replay on all 100 catalogue rows with depth 10 and seed order 8 reproduces the original output and its 115,744 visited prefixes byte for byte. The alternative seed order 9 also verifies all 100 and visits 53,832 prefixes. The recalculated scalar critical derivatives, the slot-based cost, and the reverse orphan-liveness method are in replay.cpp. replay.py generates that file from the reviewed arbitrary.cpp source. The same graph and topological canonicalization are retained in these two runs.

    c++ -O3 -std=c++17 -DVERTICES=10 work/gap519/audit/replay.cpp -o /tmp/prefix-audit
    /tmp/prefix-audit 10 8 work/gap519/prefix/high-10.txt

A third, seed-eight run disables both input symmetry rejection and topological-order rejection in the gate search. All 100 lower bounds agree after 4,102,917 visited prefixes. Board isomorphism reuse for already-proved induced subgraphs remains enabled. See replay_nocanon.cpp and replay-without-lex.txt.
