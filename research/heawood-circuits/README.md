# How many gates does the Heawood edge function need?

The input consists of 14 vertex bits, and the output asks whether the selected vertices contain one of the 21 incidences in the Fano plane. With binary monotone gates and unrestricted reuse, the minimum is between **25 and 27** inclusive. The project's L-meta-582 asks whether 26 gates suffice. The two candidate sizes 25 and 26 remain undecided here.

Every proper nonempty induced subgraph, after removal of isolated vertices, has minimum equal to its number of edges plus its minimum vertex-cover size minus one. In particular deleting any one vertex leaves a function of exact size 23. The standalone external lower.cpp computes bounds from the single edge in increasing order without an input table. replay.txt records all 68 representatives including the whole graph, with mask, proved lower bound, constructed upper bound and number of search nodes. Compare a fresh run with the complete transcript.

    c++ -O3 -std=c++17 lower.cpp -o lower
    ./lower > fresh.txt
    diff replay.txt fresh.txt

The upper construction groups the edges into stars. HeawoodUpper.lean checks its size of 27 and its behavior on every input in the project's actual circuit encoding. For formulas, the exact answer is also 27. HeawoodFormula.lean gives a separate Lean certificate using a signed weight on the monotone communication game. Each variable leaf can capture weight at most six and the total is 168, giving at least 28 leaves. The two audits in AUDIT.txt use only the standard Lean axioms. The circuit lower bound uses the external C++ program.

The file deleting-a-vertex.md also deduces the whole-graph lower bound from the exact 23 single deletion and gives additional constraints on any potential 25-gate circuit. search-review.md explains the lower search and its normalization. formula-exact.md gives the independent general formula argument on high-girth graphs.

The private-cone enumeration in cone-sharing.md proves that any circuit of at most 26 gates must either reuse two internal gates on the same directed path or reuse a gate whose private input formula contains at least nine gates. Run the following standard-library commands in this directory. cone_profiles.py writes intermediate signature lists in the current directory.

    python3 weights.py
    python3 cone_profiles.py 8
    c++ -O3 -std=c++17 rectpack.cpp -o rectpack
    python3 verify_cones.py

Use Lean 4.36.0 with the pinned project/Mathlib revision. The formula certificate imports only Mathlib. The circuit witness imports PEqualNP.Defs and should be checked from the project's lean directory with its normal Lake environment.

## Safe conjunctions of disjunctions

A safe monotone CNF must reject every independent input. If it accepts any 20 of the 21 edges, it already requires at least 37 clauses. CnfFootprint.lean checks the theorem and the general equivalence with coloring the conflict graph on negative rows. For two, three, four and five clauses the maximum numbers of edges accepted are 3, 5, 6 and 7. The external programs footprints.cpp (set cover) and coloring.cpp (graph coloring) produce the same complete table in footprints.txt. Compile each with c++ -O3 -std=c++17 and compare its output with that transcript. See cnf-footprints.md for the proof, the classification for three clauses and an implication for circuits with one internal unsafe AND.
