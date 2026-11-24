# One-NOT circuits for the projective plane of order seven

A fan-in-two AND/OR/NOT circuit computing the 57 line ORs of the projective plane of order seven with at most one NOT has **at least 234 physical gates**. The included Lean proof checks both the circuit argument and the finite incidence statements. A second theorem counts specific **OR gates** in any linearly intersecting output subfamily disjoint from a true assignment of the NOT's input.

## Exact claims

- `Plane234.lean` proves `PEqualNP.Outside.Window997.plane57_one_not_234`. Its 57 lines are the translates of {0,1,3,13,32,36,43,52} modulo 57. The circuit can designate any wire for each output. Fan-out is unrestricted and size is the length of the gate list. The hypotheses allow zero or one NOT and at most two operands per gate. A NOT reads its first operand under the project semantics. The proof handles empty gates, repeated operands and invalid or forward wire references. See [the numerical proof](near-saturation.md).
- `OrHeavy997.lean` proves the monotone single-row and oriented multi-row OR bounds `heavy_or997` and `or_family997`. `PinnedOr997.lean` proves the corresponding original one-NOT circuit bounds `physical_or_oriented997` and `physical_or_family997`. See [the OR-count proof](or-witnesses.md).
- The unrestricted one-NOT refund inequality in project gap L-meta-997 and the exact optimum for the 57 outputs remain open. Independently computing the 57 eight-input ORs gives a 399-gate monotone circuit.

## Replay

Use an existing checkout of the project with Lean **4.36.0**, mathlib at `fc4f59e577feb1a4956671bc04ac18aaaf8cd842`, and a built `PEqualNP.Defs.CircuitLowerBounds` module. From the extracted packet run:

```sh
LEAN_PROJECT=/absolute/path/to/pequalnp-proofs/lean sh verify.sh
```

The script uses a fresh temporary directory for compiled objects, compiles all fourteen supplied sources in dependency order, and prints axiom dependencies for the principal results. The attached `verification.txt` records the guest replay. There are no package-install, network or publication steps. The foundational monotone cut adapts [the source of L-meta-988 at the reviewed project revision](https://github.com/brilliant-hq/pequalnp-proofs/blob/48a1a46a56b8b906a7e15b4f98bbceb16b50e5d2/lean/PEqualNP/Outside/L_meta_988.lean).
