# Sparse samples and monotone formula minimization

For every simple cubic base graph \(G\) with \(n\) vertices and \(m\) edges, a polynomial-time construction makes an explicit binary sample on \(n+2m\) named variables. It has \(3m\) positive rows of weight two and \(3m\) negative rows of weight two or three. Each coordinate occurs in at most six rows. A read is one occurrence of a named input in a binary monotone AND/OR formula. Size counts its gates; subformulas are trees with no sharing.

Give all variables a cap of two reads except a designated subset \(U\) of the original vertices, whose cap is three. The minimum number of gates is exactly
\[
                       4m+n-1-\alpha(G[U]).
\]
This is both the minimum over formulas agreeing only with the sample and the minimum over formulas computing the entire target edge function. A polynomial-time repair turns a cap-respecting formula with \(s\) gates and \(t\) incorrectly labeled rows into a cap-respecting exact formula using at most \(s+2t\) gates.

[The sample construction and repair](sparse-formula-consistency.md) proves the local occurrence bound, the exact read-budget hierarchy, APX-completeness for restricted sample minimization, and the counting and noisy-learning consequences. It compares the result with earlier hardness for partial truth tables and lists of examples.

[Fixed data and varying read permissions](fixed-sample-read-permissions.md) characterizes the query languages from a fixed polynomial-size sample and fixed size threshold. Each external bit can enable one extra occurrence of one designated coordinate. The languages are precisely the monotone members of NP/poly. The paper gives uniform SAT and CLIQUE examples, including unconditional monotone circuit lower bounds for answering budget queries after preprocessing. Independent mathematical review covered the repair bound, the cap-preserving reconstruction, the fixed-data encoding and the uniform SAT counts. The manuscripts contain mathematical proofs; the accompanying programs perform finite checks.

[The feasible-mask polytope](budget-polytopes.md) gives a fixed sample of quadratic size whose permission predicate is existence of a perfect matching. Pinning all other coordinates and minimizing the number of permissions exposes the complete-graph perfect-matching polytope. Its known extension-complexity lower bound gives an exponential obstruction to small exact linear programs, even though the query predicate has a polynomial-time general algorithm. The note also gives a face representation for arbitrary nonempty NP/poly witness polytopes.

[Learning a hidden instance](learning-hidden-instances.md) shows that variable gate thresholds identify the graph in optimal order n log n Boolean queries. Asking only whether two gates can be saved takes quadratic query complexity even with bounded-error randomization. A known linear-size set of independent anchors restores optimal query complexity with a single gate threshold. It connects both bounds to prior results on hidden graphs.

[Arbitrary read budgets](arbitrary-read-budgets.md) gives the exact minimum for every graph of girth at least five and arbitrary per-variable caps. Feasibility is a polynomial-time orientation problem. Once feasible, the remaining size term is the independence number on vertices whose budget reaches their degree. This yields a density characterization of uniform readability.

[Sharp repair costs](sharp-noise-repair.md) recovers the entire target from a formula with mislabeled examples. On the original paired sample, with one extra negative singleton per degree-one input when needed, the optimal universal cost is three gates per error for arbitrary feasible caps, and two for the cubic subdivisions. Both constants are witnessed by a single mislabeled row, even at uniform read cap two. The fixed-data classification also holds with the two-gate penalty on the original cubic sample.

The `lean/` directory contains the original sources needed for the full-function constrained minimum. `WeightedFormula.CappedMinimum.exact_capped_gates` proves a lower bound over all respecting formulas and constructs an attaining formula. A fresh Lean 4.36.0 replay compiled all five included source modules from an empty output directory and reported only propext, Classical.choice and Quot.sound. The transcript is in `lean/clean-replay.txt`. For a compiled compatible Mathlib checkout, run `python3 -B lean/replay.py /path/to/mathlib --lean /path/to/lean`. The sparse/noise, query-complexity and polyhedral arguments are mathematical proofs with finite Python controls.

## Reproduce the controls

The scripts use only the Python 3 standard library.

1. Run `python3 -B check_sparse_formulas.py`. It constructs sparse samples, enumerates all 262,144 physical orientations on one instance, checks all 16 of its read allocations, compares 800 polynomial-time repairs with their inputs and does independent exact formula minimization over all reachable boundary signatures on two small cycles.
2. Run `python3 -B check_fixed_sample.py`. A graph-based independent-set solver checks all 256 masks of the three-variable universal SAT sample, a nontrivial monotone verifier, and small fixed samples whose permission predicates are CLIQUE.
3. Run `python3 -B check_budget_faces.py` to test every input on the four-vertex matching sample and a dual-rail face.
4. Run `python3 -B check_query_learning.py` to reconstruct 144 labeled cubic graphs from threshold queries.
5. Run `python3 -B check_arbitrary_caps.py` to compare the general formula with 1,799 nonuniform budgets and with direct formula synthesis on two small graphs.
6. Run `python3 -B check_sharp_repair.py` to check two sharp single-error examples and an additional 362 general-cap repairs.
7. Compare their output to the six included logs. The archive manifest records the SHA-256 of every source and log.
