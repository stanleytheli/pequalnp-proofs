# A binary finite-state checker for three-round verification of physical stack traces

The challenge in this proof family specifies a short, possibly inconsistent collection of timestamped machine rows. The new theorem `ColumnCheck.Table.physical_counter` constructs one finite multistack machine for each fixed source and verifies the complete counterexample predicate on binary, interleaved columns. On a serialized window of length L, the machine produces the correct Boolean within 2L+3 physical steps. The time address, horizon, and original input symbol at the chosen time must match the surrounding computation.

Local checking includes initialization, terminal acceptance, finite control, pushes, peeks, pops, timestamps, and all parent-pointer comparisons. The machine reconstructs the required list of four anchor rows and the earlier rows named by the two relevant stack states. If a timestamp is repeated it uses the first matching record. Missing records, malformed opcodes and out-of-range finite encodings receive the same defaults as the trace definition.

With r sample slots and k stacks the concrete encoder has 3+r(6+k) lanes. A width-d window occupies d times this number of bits. The three header values describe the chosen time, final time and optional input symbol. `ColumnCheck.Wire.represent_word` proves every legal sample of at most r rows has an exact representation in any sufficiently long ordinary fixed-length binary word.

The underlying three-round verifier uses a Boolean circuit for the trace as its first message. The universal message describes a candidate failure. A consistent commitment can answer a false allegation with a single circuit opening showing one disputed bit. The raw circuit-opening verifier `OwnedRadix.Code.queryVerifier` and the window checker are physical machines. Producing the entire uniform front end on the project's pair-encoded input also requires authenticating the full timing header, framing and routing the needed strings, and controlling the surrounding cost. The separate problem of achieving a fixed exponent saving for circuits of arbitrary physical trace tables also remains open.

## Authenticating the original input symbol

The source-index machine receives x followed by the little-endian bits of the time address, with the two parts carrying the same left/right tags as the project’s pair encoding. For each address bit the machine retains the even or odd positions of its current stack and restores the survivors to their original order. After all bits, the first surviving cell is exactly the symbol at that address in the reversed source input. The output is empty for an address past the end, including when x is empty. Leading zeros in the address are allowed.

The theorem `DyadicLookup.physical_binary_address` proves the output and the physical bound 4|x|+5|address|+3. Its full implementation is in `FP3SourceRead.lean` and uses only Mathlib. The two machines have separately proved interfaces. A joint verifier still needs to extract and route the original source and header digits from the full tagged input, check the horizon implied by the original input length, and dispatch to the single-opening proof when a valid counterexample remains.

## Reproduction

Use Lean 4.36.0 and a prepared checkout of [the proof project](https://github.com/brilliant-hq/pequalnp-proofs/tree/a285ace2301a31d8cdea9fd9e718bca202b4d06d), with the repository's pinned Mathlib revision `fc4f59e577feb1a4956671bc04ac18aaaf8cd842`. The official imported modules must have been built. The checker uses only the installed project and the Python standard library.

```sh
python3 verify.py /absolute/path/to/pequalnp-proofs/lean
```

The script uses one Lean worker, fresh temporary compiled objects, and a transitive axiom audit. Its accepted axioms are `propext`, `Classical.choice` and `Quot.sound`.
