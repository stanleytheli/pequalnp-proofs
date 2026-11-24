# The cost of negations for all line ORs of a finite projective plane

The input is a bit for each of n=q²+q+1 points. For each of the n lines, output the OR of its q+1 point bits. AND and OR gates have fan-in at most two. NOT gates can occur anywhere, all gates count, and different outputs can share wires.

A circuit of s gates using t NOT gates satisfies, for every integer 1≤h≤q,

    s ≥ h·max{0, n−1−q(2ᵗ−1)h}.

This gives s=Ω(q³/2ᵗ) when 2(2ᵗ−1)≤q and t≥1. A circuit of n·polylog(n) gates must use at least ½log₂ n−O(log log n) negations. The kernel-checked theorem `LimitedNegation.Project.plane_tradeoff` proves the first formula for the actual physical gate model and for any incidence system satisfying the listed linearity, cardinality and joining hypotheses. The asymptotic statements follow by the substitution in `negation-tradeoff.md`. The separate one-negation projective-plane proof gives a stronger numerical bound for q=7.

For Desarguesian planes over every finite field, there are circuits of size O(n log³ n) with at most ⌈log₂(n+1)⌉ NOT gates. For q a power of two the size is O(n log² n). Together these pin down the order of the NOT count for almost-linear size throughout this family. The upper bounds are written constructions. The program for characteristic two emits actual Boolean gates and tests every output at q=2,4,8,16. The odd-characteristic program checks the modular transform for q=3,5,7,9,11,25, and emits and exhaustively tests all 8,192 inputs of an actual 45,477-gate q=3 netlist with 4 NOT gates.

The proof freezes every negation on a small upward Hamming ball. Within that ball a monotone frontier argument assigns disjoint sets of gates to the lines avoiding its base. This combines the classical monotonicity of the lexicographic inversion pattern with private gate counts inside a restricted domain. Large monotone circuit lower bounds for projective-plane incidence operators are classical. Priority for this joint size/negation tradeoff has not been established. [Markov](https://doi.org/10.1145/320941.320945) [Earlier work on incidence operators](https://tsapps.nist.gov/publication/get_pdf.cfm?pub_id=920253)

## Verification

The complete project-dependent Lean chain was built in the disposable guest against Lean 4.36.0 and the collaboration's circuit definitions. `verification.txt` includes the final axiom lists and executable results. `WindowCore997.lean` includes the reviewed monotone cut helper derived from the collaboration's L988, with its original namespace retained. [L988 source](https://github.com/brilliant-hq/pequalnp-proofs/blob/48a1a46a56b8b906a7e15b4f98bbceb16b50e5d2/lean/PEqualNP/Outside/L_meta_988.lean)

Extract the packet, set `LEAN_PROJECT` to the `lean` directory of the existing collaboration checkout, then run the following commands. The script builds only these listed modules and writes the compiled modules to the extracted directory.

```sh
sh replay.sh
python3 fourier_circuit.py
python3 odd_transform.py
```
