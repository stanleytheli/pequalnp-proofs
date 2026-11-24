"""Cross-check signed contractions and reconstruction against direct interpolation."""
from itertools import combinations, product
from random import Random

from algebraic import BinaryCircuit, MODES, physical_gates, tree_value
from check import circuit_samples, essential
from split_check import formula_tables


def direct_energy(circuit, pins, i, j, mode):
    free = [k for k in range(circuit.n) if k not in pins and k not in (i,j)]
    baseline = sum(value << k for k, value in pins.items())
    cube = []
    for labels in product((0, 1), repeat=len(free)):
        x = baseline | sum(value << k for k, value in zip(free, labels))
        values = []
        for a, b in product((0, 1), repeat=2):
            bit = circuit.evaluate(x | (a << i) | (b << j))
            values.append(bit if mode == 'one' else 1-bit if mode == 'zero' else 1-2*bit)
        cube.append((labels, values))
    total = 0
    for points in product((0, 1, 2), repeat=len(free)):
        corners = [0]*4
        for labels, values in cube:
            coefficient = 1
            for x, z in zip(labels, points):
                coefficient *= z if x else 1-z
            for k, val in enumerate(values):
                corners[k] += coefficient*val
        total += (corners[0]*corners[3] - corners[1]*corners[2])**2
    return total


def run(circuit, rng, full):
    n = circuit.n
    table = tuple(circuit.evaluate(x) for x in range(1 << n))
    checks = 0
    layout = list(combinations(range(n), 2))
    if not full:
        layout = [rng.choice(layout)]
    for i, j in layout:
        remaining = [k for k in range(n) if k not in (i,j)]
        for pins in ({}, {k: rng.randrange(2) for k in remaining if rng.randrange(2)}):
            for mode in MODES:
                expected = direct_energy(circuit, pins, i, j, mode)
                actual = circuit.energy(pins, i, j, mode)
                assert actual == expected, (n, circuit.gates, pins, i, j, mode, actual, expected)
                checks += 1
    if not essential(n, table):
        return checks, False, False
    membership = sum(bit << i for i, bit in enumerate(table)) in formula_tables(n, (1 << n)-1)
    tree = circuit.recognize()
    assert (tree is not None) == membership, (circuit.gates, tree, membership)
    if tree is not None:
        assert table == tuple(tree_value(tree, x) for x in range(1 << n))
        rebuilt = BinaryCircuit(n, physical_gates(n, tree))
        assert len(rebuilt.gates) == n-1 and not rebuilt.shared
        assert table == tuple(rebuilt.evaluate(x) for x in range(1 << n))
    return checks, True, membership


if __name__ == '__main__':
    rng = Random(16384)
    operations = (1, 2, 4, 6, 7, 8, 9, 11, 13, 14)
    total = verified = reconstructed = 0
    examples = []
    for n in range(2, 6):
        for _ in range(20):
            while True:
                gates = [(rng.choice(operations), a, b) for _, a, b in circuit_samples(rng, n)]
                circuit = BinaryCircuit(n, gates)
                if len(circuit.shared) <= 2:
                    break
            examples.append(circuit)
    # Multiplexer and simultaneous-equality functions include non-read-once behavior.
    examples.extend((BinaryCircuit(3, [(8,0,1),(4,0,2),(14,3,4)]),
                     BinaryCircuit(3, [(9,0,1),(9,1,2),(8,3,4)]),
                     BinaryCircuit(4, [(8,0,1),(8,2,3),(8,0,2),(14,4,5),(14,6,7)])))
    for circuit in examples:
        checks, is_essential, is_read_once = run(circuit, rng, len(circuit.shared) <= 1)
        total += checks
        verified += is_essential
        reconstructed += is_read_once
    print(f'{len(examples)} arbitrary binary circuit presentations; {total} exact energies versus direct ternary-grid interpolation')
    print(f'{verified} all-essential presentations verified against binary formula enumeration; {reconstructed} read-once formulas reconstructed and evaluated on every input')
