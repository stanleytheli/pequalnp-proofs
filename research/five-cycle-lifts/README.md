# Flattening every minimum circuit for a five-cycle with three leaves

For the graph with cycle edges 01, 12, 23, 34, 04 and pendant edges 35, 46, 07, every 11-gate monotone Boolean circuit computing the edge function reaches a circuit with no AND below another AND through at most three moves. Each intermediate circuit computes the same edge function. This is an exhaustive computational result for the graph and moves of project question L-meta-648. The project records credit through its own Lean checker. This package provides external certificates.

The binary AND/OR search found no circuit through size 10 matching even the 28 weight-two inputs. At size 11 it visited 8,150,828,190 complete candidate programs across 481 binary discovery-tree shapes. Of the 3,658 matching representations, 846 fail on at least one other input, 1,324 are already flat, and 1,488 have comparable AND gates. The included paths for these use one move in 1,058 cases, two in 384, and three in 46. Representations may repeat an isomorphism class. These are counts of the recorded witnesses, without a minimality claim for their lengths.

## Reproduction

Compile with a C++17 compiler. Python verification uses the standard library.

    c++ -O3 -std=c++17 enumerate.cpp -o enumerate
    ./enumerate 7 11 0 10000
    python3 moves.py
    python3 independent_review.py

The included outputs permit running the last command alone. The checker evaluates all 256 inputs. For each lift it tests that the operand is a prior gate whose function implies the current output, reconstructs the physical deletion of its OR gate, redirects the consumers, and appends the new output OR. A junk drop replaces an OR input at an AND gate by one of the inputs of that OR. The checker verifies equality of the output after each change. It checks the final circuit by a fresh traversal for strict ancestry among AND gates. It verifies all 1,950 lifts and 14 junk drops.

## Coverage

A circuit matching the weight-two slice must use all eight inputs. If input i is absent, take a neighbor j. The positive pair ij forces the circuit true on the singleton j. Monotonicity then forces a positive pair jk for any other vertex k, even one nonadjacent to j. This graph has such a k for every j. A connected binary output cone with eight essential inputs needs at least seven gates.

In a minimum circuit on the weight-two tests, every gate is in the output cone, and no gate can have the value of a prior wire on that slice, since redirecting its uses removes it. Nullary constants, missing or forward operands, and repeated or unary operands can be simplified out of a nonconstant minimum circuit. The search finds the minimum to be 11. Thus these reductions preserve every full-cube circuit of size 11.

Traverse the output cone depth first. Explore first the operand having more undiscovered reachable gates before either child is visited. When the final positive subtree sizes tie, the two initial sets had equal size and were disjoint, so either order works. The search then orders by the popcount on the pair inputs. Two immediate leaf operands can be ordered by discovery age. Number fresh inputs by first occurrence, test every gate operator, and match the output modulo every permutation of the input names. These steps represent every minimum circuit up to input renaming, commuting the two operands, and choice of topological order. These transformations preserve eligibility and results of the moves: old consumers of the erased wire are rewired, its upstream operands survive, and the new OR is last. They preserve strict ancestry. Automorphisms of the graph preserve its target truth table.

The search uses a state signature to avoid revisiting circuits while looking for paths. Completeness of that shortcut is unnecessary for this positive result: a concrete path was found and independently verified for every recorded correct circuit.
