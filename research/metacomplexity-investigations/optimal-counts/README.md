# Counting minimum gate programs

For an all-essential Boolean function with a binary read-once realization, this supplement counts all optimal ordered formulas and topologically numbered gate lists and gives their common number of XOR/XNOR gates. The closed formulas, size conventions, and runtime are in `optimal-counts.md`. `algebraic.md` contains the independent factorization and recovery proof on which the counts rely.

Run `python3 -B syntax_check.py` with Python 3.10 or later. There are no third-party dependencies. `syntax-check.log` records the results. `split_check.py` supplies truth-table indexing helpers. The algorithm and counting results have mathematical proofs and exhaustive small-instance checks. The counting formulas have not been formalized in Lean.
