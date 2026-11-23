# Exact monotone formula size for graph edge functions

Let G be a finite simple graph with at least one edge, with no triangles or four-cycles. Its edge function accepts precisely the vertex sets that contain both endpoints of an edge. Every monotone binary formula computing this function needs at least |E(G)| + τ(G) − 1 gates, and a construction from a minimum vertex cover attains that value. Here τ(G) is the minimum vertex-cover size. Input and constant leaves are free.

The manuscript in formula-exact.md gives the argument. FormulaRank.lean proves the lower bound, constructs the matching formula and checks the exact size over official Mathlib. The proof partitions a communication matrix into leaf rectangles. The leaf reached on the diagonal orients each edge toward one endpoint. Around each vertex, real matrix rank bounds its number of occurrences in the formula. Summing those bounds accounts for both the edge count and a vertex cover.

For the exact 52 incidences and 26 inputs in project search L-meta-650, ProjectivePlane650.lean proves that the minimum is 64 formula gates. The incidence certificate includes a matching of 13 edges and a cover of 13 points. The Heawood and Petersen formula minima are 27 and 20 by the general argument.

The project searches for smaller circuits allowing shared intermediate wires. The separate local-auxiliary.md excludes a class of such circuits on the order-three plane, using an arbitrary private auxiliary circuit with support up to 14 and a specified star output. We verified its finite calculation by two different optimizations.

## Reproduction

Use a Mathlib workspace with Lean 4.36.0. From that workspace put these source files in the same directory and include that directory in LEAN_PATH alongside the environment supplied by Lake. Compile FormulaRank.lean to FormulaRank.olean before checking ProjectivePlane650.lean. Both kernel checks succeeded in the disposable project VM. Their principal theorem axiom reports are in AUDIT.txt.

For the local auxiliary calculation, use a C++17 compiler and Python 3.10 or later. The independent Python program recomputes all 26 maxima from a vertex-cover optimization. It requires only the standard library.

    c++ -O3 -std=c++17 support.cpp -o support
    ./support
    python3 check_support.py
