# Three-block verification of multistack computations

This bundle contains Lean proofs about L-lib-123 in the public P=NP collaboration. The assigned question asks whether some integers p<q give a three-block verification speedup for **every** language decidable in deterministic time O(2^(qn)). The unrestricted statement remains open. The results here establish a physical verifier for succinct circuit commitments, speedups under a stack-access hypothesis, and a lower bound on one explicit trace-verification method.

## Results

| Source | Main theorem | Result |
|---|---|---|
| CircuitCommitment.lean | OwnedRadix.Compiler.realize_official | Every official size-s Boolean circuit on m inputs has a single binary commitment that a fixed finite multistack machine can query on all inputs. |
| StackTraffic.lean | DeterministicPadding.sigma_of_sublinear_switches | A fixed total deterministic decider with uniformly sublinear changes of popped stack belongs to the project’s Σ₃ verifier class with block bound 2^(⌊n/q⌋), for every positive integer q. |
| ExplicitOpenings.lean | StackLayout.Wired.explicit_opening_barrier | On a fixed multistack machine for each q, some N-bit input forces every explicit predecessor-opening scheme with openings of at most K·2^(pN)+K vertices to commit more than that many vertices. |
| PascalReader.lean | PascalStream.labels_without_witness | The true labels of that Pascal grid have a fixed direct-address stack machine for each dimension. It returns one label in W+1 macrosteps on its dW-bit coordinate address. |
| PhysicalRows.lean | StackTrace.PhysicalSigma.sigmaV_of_honest_bits | A succinct truthful reader for encoded physical trace rows, together with the stated uniform local verifier, yields membership in the exact project class. |
| ExponentBudget.lean | TraceBudget.padded_size | A fixed fractional saving in the exponent for the indexed row circuit absorbs polynomial costs for addressing, gate verification and padding. |

### Circuit commitment

For m+s≤2^d, define B=(6(d+1)+9)(2+m+s)+2(d+1)+3. The commitment and each honest opening have at most B bits. On an honest opening of length l the verifier takes at most (7(d+1)+23)l+19 actual Mathlib FinTM2 macrosteps. The two constant ports, false and true, allow the compiler to implement the project's nullary gates and its zero default for missing wires. The other ports carry the query bits and the requested answer. The machine's finite input alphabet distinguishes the three binary streams. Its representation reads the commitment and the query in reverse order, then the opening in forward order.

The opening supplies two proposed operand bits per gate. A stable radix partition groups every definition and use of each wire name. A group must have one definition before all uses, and every use must match its defined bit. The grammar and commitment comparison run on arbitrary raw input strings. The theorem OwnedRadix.Code.commitment_function shows that for each binary commitment there is one Boolean function consistent with **every** accepted query answer, including openings of arbitrary length. The machine accepts an honest opening of the true value for each input to the compiled circuit. Its polynomial factor in d records the cost of processing binary addresses on real stacks.

### Stack traffic

For a fixed machine M, let s count changes of the popped stack after each macrostep is split into atomic operations. Let F count pushes to a stack different from the last popped stack, starting with the input stack as the reference. For a terminating run on n input cells, the actual elapsed time is at most C_M(n+s+F+1). Conversely s+F is at most a machine constant times the actual elapsed time. These estimates are StackTrace.Atomic.switch_write_clock and StackTrace.Atomic.switch_write_cost. DeterministicPadding.sigma_of_transfer_budget applies the former estimate to the project's uniform time-bounded verifier. BudgetGuard.time_guard enforces a linear clock on the entire encoded input, including short or malformed witnesses.

### Explicit predecessor openings

The data-dependency graph comes from an actual multistack traversal of a q-dimensional Pascal grid. Its cascade of local XOR gates produces parities of multinomial coefficients. For the selected inputs of length N, a Boolean circuit of size at most 3(N−1)q²+1 supplies all genuine vertex labels. The physical machine reaches every designated grid position within 9·2^(qN) steps. The disclosure lower bound quantifies over the particular CutVerification.Scheme definition in the source. The direct coordinate reader gives an explicit small alternative for these same labels.

## Remaining work on L-lib-123

The commitment theorem supplies a verifier when the relevant row function already has a small circuit. An unconditional speedup requires truthful short descriptions for every fixed unrestricted multistack decider, or a different argument. The row-reduction theorem also has an explicit hypothesis for one linear-time verifier implementing a complete local challenge on the concatenation of the three padded blocks. The provided physical circuit evaluator checks individual challenges to a circuit. Connecting all adaptive row lookups, pointer checks, padding and rejection paths to that single project verifier is a separate step. The unrestricted assignment includes machines that change their popped stack and write to other stacks frequently.

## Reproduction

The reference checkout is brilliant-hq/pequalnp-proofs at commit a285ace2301a31d8cdea9fd9e718bca202b4d06d. It specifies leanprover/lean4:v4.36.0 and Mathlib commit fc4f59e577feb1a4956671bc04ac18aaaf8cd842. Each source is a complete independent Lean file. Related files repeat some declarations so they can be checked separately.

Use a prepared checkout with the project’s pinned toolchain, Mathlib and the following official modules built. The module list comprises PEqualNP.Defs, PEqualNP.Defs.TimeAlt, PEqualNP.Library.Machines.ComposeRun, PEqualNP.Library.Machines.FilterMap and PEqualNP.Library.Machines.Transducer. The imports at the start of each source give its precise Mathlib dependencies.

Run from the bundle directory with the path to the checkout’s lean directory.

    python3 verify.py /path/to/pequalnp-proofs/lean

The script uses the installed Lake executable to check one file at a time. It verifies the kernel exit status and the printed axiom dependencies for every listed result. The accepted standard axioms are propext, Classical.choice and Quot.sound. The proofs include routine unused-tactic or style linter warnings under the pinned toolchain. The script preserves full diagnostics on a failed check.

The public project and the assigned statement can be found through the [proof repository](https://github.com/brilliant-hq/pequalnp-proofs) and the [project desk](https://pequalnp.com/).
