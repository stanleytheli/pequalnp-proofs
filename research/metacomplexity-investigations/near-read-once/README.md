# Circuit minimization near the read-once threshold

These notes study single-output, fan-in-two Boolean circuits with all N named inputs essential. Gate count measures binary operations and permits arbitrary fanout. Inputs to the minimization problem are either a succinct circuit presentation or an oracle returning individual truth-table entries. The distinction matters for both the algorithms and the lower bounds.

| Files | Main result and verification |
|---|---|
| `recognition.md`, `recognize.py`, `check.py` | For an explicitly supplied monotone circuit of size N−1+r, a 6^r poly(N) algorithm decides whether its optimum is N−1. It returns a formula or a six-row obstruction. The parameter cannot be reduced to a subexponential dependence under sparse ETH. The executable recognizes the syntactically monotone case and can verify essential-input promises. |
| `algebraic.md`, `algebraic.py`, `TensorContraction.lean` | The implemented arbitrary-binary recognizer runs in O(N²(N+g)16^b) integer operations for b shared producers, and the method extends to single-exponential treewidth dependence. It returns a physical N−1-gate circuit. Lean checks the four-copy signed contraction and the ternary-grid energy identity. |
| `general-binary.md`, `split_check.py` | For arbitrary binary presentations and targets, the same exact threshold is fixed-parameter tractable in the number of shared wire producers, and in supplied circuit treewidth. The double-exponential dynamic program is a paper proof. Its root-split criterion was checked against exhaustive formulas on every truth table through four inputs. |
| `overlap.md`, `Overlap.lean` | A minterm and a minimal zero certificate meeting in k variables force at least N−2+k binary monotone gates. Lean constructs physical proof traces from gate semantics and proves the bound. |
| `oracle.md`, `BlockSpike.lean` | Exact threshold recognition needs Θ(3^(N/3)) membership queries under monotonicity and Θ(2^N) for arbitrary Boolean targets. For monotone targets six labeled rows suffice to certify a NO answer, and sometimes all six are necessary. The sharp leading classical YES-verification bounds use the integer-break product. Lean checks the lower bound for a calibrated gap family. |
| `quantum.md` | The bounded-error quantum query complexity is Θ(√B(N)) for monotone inputs, with B(N) the integer-break product. Arbitrary-basis YES verification with a claimed read-once formula takes Θ(2^(N/2)) queries. The oracle lower bounds hold even with an untrusted interactive prover. |
| `boundary.md` | Critical rows characterize monotone equivalence. Counting false positives of a succinct monotone competitor even against a matching target is #P-complete. |

The two circuit lower-bound theorems use a trimmed physical model with two operand slots per gate, an explicit decreasing topological rank, and the Boolean AND/OR evaluation equations. Its gate count includes shared gates once. The compiled bounds are the semantic overlap inequality and the consequent lower bound for a disjunction of disjoint conjunctions with one extra term. A separate Lean module proves the algebraic interpolation and contraction lemmas used in the arbitrary-binary recognizer. The matching upper construction, recognition algorithms, complexity assumptions, classical and quantum query arguments have written proofs. The cited work identifies the read-once, learning, hypergraph, functional-decomposition and MCSP results used here.

## Reproducing the finite checks

From the extracted directory, run `python3 -B check.py`, `python3 -B split_check.py`, `python3 -B algebraic_check.py`, and `python3 -B tensor_check.py` with Python 3.10 or later. All use the standard library. Expected outputs are in `checks.log`, `split-check.log` and `algebraic-check.log`. The first suite checks 600 trimmed circuits, exhaustive cofactor and essential-support comparisons, planted monotone gap examples, ordinary parity flips, and sparse formula reductions. The second compares all essential truth tables up to four input bits against independently enumerated binary read-once formulas. The last two compare signed contractions with direct grid summation, validate physical reconstructed circuits on their full truth tables, and test every root partition of every essential four-input Boolean function. `algebraic.BinaryCircuit(n, gates)` uses integer gate truth tables indexed by `left+2*right`. The `recognize` method returns a signed-leaf tree or `None`, and `physical_gates(n, tree)` converts any successful tree into N−1 physical binary gates.

`recognize.py` takes N and a topologically sorted list of triples `('and' or 'or', left, right)`. Wires 0 through N−1 are inputs. Each gate appends one wire and the last wire is the output.

## Reproducing the Lean proofs

Use Lean 4.36.0 with the matching Mathlib environment already installed. From that environment run the following commands, setting `src` to the absolute extracted directory. The second command includes that directory in the Lean module path so it can import the first compilation result.

    lake env lean --root="$src" -j1 -DElab.async=false -o "$src/TensorContraction.olean" "$src/TensorContraction.lean"
    lake env lean --root="$src" -j1 -DElab.async=false -o "$src/Overlap.olean" "$src/Overlap.lean"
    lake env sh -c 'export LEAN_PATH="$1:$LEAN_PATH"; exec lean --root="$1" -j1 -DElab.async=false -o "$1/BlockSpike.olean" "$1/BlockSpike.lean"' sh "$src"

`lean-check.log` records the axiom output of the four principal checked declarations. The overlap and contraction sources import only Mathlib, and the block corollary imports only `Overlap`.
