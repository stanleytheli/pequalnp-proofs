# Infinitely often hard physical trace tables from failure of a three-round speedup

This Lean development proves a conditional three-round verification theorem in the P=NP collaboration's machine model. Its main result is `StackTrace.OneOpeningGame.fp3_of_small_tables`. For a natural number a, it proves the collaboration's exact `FP3 (5a+4) (5a+5)` under two hypotheses. A fixed saving in the size of circuits for the physical trace table supplies the first message. One uniformly linear-time machine must decide the specified relation on the three messages. The unrestricted research question remains open.

## Infinitely often hard tables

For each fixed integer a, the main new theorem is `StackTrace.OneOpeningGame.hard_trace_if_no_fp3`. Assume the named local front-end verifier exists for every deterministic multistack decider. If the project’s `FP3 (5a+4) (5a+5)` fails, then one fixed decider, with one fixed time coefficient, has infinitely many hard input lengths. At those lengths n, a single joint Boolean function on m bits encodes the trace at every input x and every time/bit address. It has no fan-in-two De Morgan circuit with at most 2^⌊am/(a+1)⌋ gates. The machine and time coefficient may depend on a.

The proof checks a physical machine that attaches a finite-state flag during an ordinary decider run. This proves the project’s `SigmaV j s` classes tolerate changes at finitely many input lengths, for every j and every block-length function s. Therefore compression is sufficient at all sufficiently large lengths.

The exact joint truth table has an explicit chronological producer. For each x, `streamingTick` obtains the machine operation from current control and stack heads, then updates at most one stack, storing the timestamp next to every pushed symbol. `physicalSweep_bit` proves each emitted bit agrees with the table. `Generated.bit_count` proves the output has exactly 2^m bits. These statements establish the scan structure, row count and values. They do not give an end-to-end real bit-machine time theorem for generating the full table.

## What each message contains

1. On an input x of length n, the first player commits to a De Morgan circuit. Given an atomic time t and a bit index j, its honest answer is bit j in the timestamped row at time t of the actual finite multistack machine. The first message contains a binary commitment with a trailing delimiter.
2. The universal player selects one time i and proposes all the rows that would make the local trace check fail there. With k stacks, these are the four anchor rows at 0, T, i and min(i+1,T), plus at most two rows of earlier pushes for each stack. At row width (4+k)d, every such message fits within d+(4+2k)(1+d+(4+k)d)+1 bits. The width d is the binary width of T and the fixed machine description. Every pointer decoded from arbitrary bits also fits d bits.
3. A malformed challenge or a sample that passes its own local test can be dismissed. For a well-formed alleged failure, the final player identifies one discrepant time and bit position and supplies one circuit opening to the opposite bit. This opening is checked by `OwnedRadix.Code.queryVerifier`, a fixed physical machine. The final binary block contains the two little-endian coordinates, the opening and padding.

For every binary first message, the physical circuit verifier accepts at most one bit value on a specified circuit input. Complete the partially openable answers to one total Boolean function. If its claimed trace fails at some time, the universal player can submit the local rows from that same function. No valid opening refutes a bit of that challenge. For an honest accepting computation, every proposed bad local sample differs from the genuine computation in at least one listed bit and that bit has a short physical opening. Consistency across all challenges therefore follows from a single commitment.

## Exponents and scope

For a decider running in K·2^((5a+5)n)+K steps, m is the address length for its time and bit coordinate. The named function `StackTrace.RowAddress.table` assigns a Boolean answer to each address. The hypothesis in `fp3_of_small_tables` bounds its circuit size by 2^⌊am/(a+1)⌋ for each fixed x. The physical commitment length, honest opening length, time needed to check that opening and local challenge length all fit K′·2^((5a+4)n)+K′. The constant K′ may depend on the decider. The first and last blocks retain the exact lengths required by `PEqualNP.Library.SigmaV`.

The theorem defines the complete response relation in `FP3Game.lean`. A single linear-time machine for that relation is an explicit premise. The actual circuit-opening machine, the relation between winning the three-message game and source-language membership, and the numerical bounds are proved. The construction supplies neither a universal circuit-size upper bound for unrestricted deterministic traces nor the full machine implementing the outer finite local test.

The companion result `speedup_of_joint_tables` uses one circuit at each length n with x, t and j as joint inputs. Specializing its x-inputs adds at most two constant gates and preserves the public circuit semantics for missing wires. The common input length is at most (5a+7)n+C. The guarded variant `guarded_game` allows a raw machine that halts quickly on honest accepted transcripts and has sound accepting endpoints. A proved physical wrapper gives the resulting verifier a linear clock even on malformed short data.

## Reproduce the checks

Use Lean 4.36.0 and a prepared checkout of [the public proof project](https://github.com/brilliant-hq/pequalnp-proofs/tree/a285ace2301a31d8cdea9fd9e718bca202b4d06d). The proofs use that checkout's Mathlib revision `fc4f59e577feb1a4956671bc04ac18aaaf8cd842`. The project modules named by the imports at the beginning of each source must have been built, including `PEqualNP.Library.Machines.FirstGRun` and `PEqualNP.Library.Machines.Transducer`. The local review and check used a Linux VM.

Run the standard-library Python script from any directory. Its argument is the original project's `lean` subdirectory.

```sh
python3 verify.py /absolute/path/to/pequalnp-proofs/lean
```

The script runs a single Lean worker, writes temporary object files and checks the named declarations' transitive axioms. The accepted axioms are `propext`, `Classical.choice` and `Quot.sound`. The script uses the installed project and toolchain.

| File | Contents |
|---|---|
| FP3KernelC.lean | Binary circuit compiler, fixed physical verifier and consistent interpretation of every accepted bit. |
| FP3KernelR.lean | Timestamped physical rows, finite representations and soundness of local trace checks for unrestricted multistack machines. |
| FP3Bases.lean | Imports the circuit and trace modules together. |
| FP3GameBase.lean | Framed first block, row addressing, finite local samples, universal binary encoding and one-opening refutations. |
| FP3Game.lean | Final-message encoding, exact game semantics and the project’s conditional three-block verifier result. |
| FP3Speedup.lean | Physical resource bounds, the per-language result and the precise fixed-pair implication. |
| FP3Guarded.lean | Physical clock, arbitrary-commitment soundness and a guarded verifier for padded transcripts. |
| FP3Joint.lean | Circuit hardwiring, common input-length arity, physical budgets and the jointly indexed circuit implication. |
| FP3Receipt.lean | An independent batch machine reuses one immutable physical circuit commitment and checks any finite number of openings. |
| FP3Override.lean | A real machine attaches a finite-state flag to an arbitrary decider run, then overrides its answer if flagged. |
| FP3Splice.lean | Finite-change closure for every project verifier class with a fixed alternation count. |
| FP3Eventual.lean | Eventual joint circuit compression, the fixed-pair implication and infinitely often hard tables under failure. |
| FP3Generated.lean | The complete joint table from chronological timestamped stack sweeps and its exact bit count. |
