# Exact circuit minima with AND, OR and NOT

An input chooses a set of vertices. The output indicates whether the set contains an edge. Here each binary AND, binary OR and unary NOT costs one gate. An intermediate result may have any number of readers.

For every nonempty graph of maximum degree three and girth at least seven on at most **12 nonisolated vertices**, the minimum equals the number of edges plus the minimum vertex-cover size, minus one. At twelve vertices this accounts for 469 isomorphism classes and 94,013,864,835 labeled graphs. The project asks whether the formula holds at all sizes in L-meta-519. This is a finite result using external, reproducible computation.

For the broader family of graphs with no triangle or four-cycle, the same exact value holds on at most **nine nonisolated vertices**, including all 179 nine-vertex isomorphism classes and 22,771,971 labeled graphs. Isolated inputs can be removed by restriction for both statements. The zero-edge function is outside the claims.

The upper circuit assigns every edge to an incident vertex of a minimum cover, builds the corresponding stars and ORs them together. The coverage programs independently check that the available representatives account for all labeled graphs, check their distinct isomorphism types, and evaluate every upper circuit on its complete Boolean cube.

The restriction search for the lower bound uses full truth tables and permits a NOT at every eligible step. For a live circuit on n essential inputs with k gates, the number of NOT gates plus the number of extra reader slots beyond one per wire equals k−n+1, counting the final output use. Pinning variables to constants and removing the resulting constant, duplicate or unused gates gives lower bounds via smaller graphs. On each sensitive pair, at least one wire into the remaining circuit must distinguish the two assignments. The two possible directions of a bit change are both permitted. See review.md for the counting proof and implementation audit.

## Reproduce

Use a C++17 compiler with unsigned 128-bit integers and Python 3.10 or later. Both runs use only the standard libraries. Each verification begins with the single-edge graph and proceeds by increasing graph size, using only bounds already checked for its own gate basis. On the largest graphs the gate search can take longer than the coverage check.

    python3 reproduce.py subcubic
    python3 reproduce.py girth5

The independent ten-vertex replay turns off gate-order and input-symmetry rejection. Its separate scalar sensitive-pair calculation and backward liveness traversal establish all 100 ten-vertex subcubic cases, with more than four million enumerated prefixes when starting from the eight-vertex bounds. The following uses the nine-vertex bound established by the main run.

    c++ -O3 -std=c++17 -DVERTICES=10 replay_nocanon.cpp -o replay
    ./replay 10 9 catalogue-10.txt

The four-vertex controls include graphs containing a four-cycle for which the canonical upper size is strictly larger than the exact minimum. control-result.txt records the independent exhaustive truth-table comparison.
