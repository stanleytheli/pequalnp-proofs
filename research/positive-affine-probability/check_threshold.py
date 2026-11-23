"""Exact finite-weight controls for the bipartite positive-border separator.

Weights are rational exponents with a common denominator. The tests compare
enumerated covers with a flow network, including zero, repeated and infinite
weights, ties exactly at threshold, and changes of active label on cube inputs.
"""
from collections import deque
from fractions import Fraction
from itertools import product
from math import lcm
from random import Random


def cut_value(weights, edges, split):
    n = len(weights)
    source, sink = n, n + 1
    residual = [[0] * (n + 2) for _ in range(n + 2)]
    for v, weight in enumerate(weights):
        if v < split:
            residual[source][v] = weight
        else:
            residual[v][sink] = weight
    barrier = 1 + sum(weights)
    for u, v in edges:
        residual[u][v] = barrier
    flow = 0
    while True:
        parent = {source: -1}
        queue = deque([source])
        while queue and sink not in parent:
            u = queue.popleft()
            for v, cap in enumerate(residual[u]):
                if cap and v not in parent:
                    parent[v] = u
                    queue.append(v)
        if sink not in parent:
            return flow
        gain = barrier
        v = sink
        while v != source:
            u = parent[v]
            gain = min(gain, residual[u][v])
            v = u
        v = sink
        while v != source:
            u = parent[v]
            residual[u][v] -= gain
            residual[v][u] += gain
            v = u
        flow += gain


def scan(weights, edges):
    value = None
    for bits in product((0, 1), repeat=len(weights)):
        if any(not (bits[u] or bits[v]) for u, v in edges):
            continue
        used = [w for w, b in zip(weights, bits) if b]
        if None in used:
            continue
        cost = sum(used)
        if value is None or cost < value:
            value = cost
    return value


def check():
    rng = Random(92141)
    total = ties = impossible = 0
    weights = [None, None, Fraction(0), Fraction(1, 3), Fraction(5, 7), Fraction(4)]
    for _ in range(40):
        split, nbits = 3, 3
        edges = [(u, v) for u in range(3) for v in range(3, 6) if rng.randrange(3)]
        table = [[rng.choice(weights) for _ in range(nbits + 1)] for _ in range(6)]
        table[rng.randrange(6)] = [None] * (nbits + 1)
        polarity = [[rng.randrange(2) for _ in range(nbits)] for _ in range(6)]
        threshold = rng.choice(weights[2:])
        den = lcm(threshold.denominator, *(w.denominator for row in table for w in row if w is not None))
        high = 1 + max([int(den * threshold)] +
                       [int(den * w) for row in table for w in row if w is not None])
        for x in product((0, 1), repeat=nbits):
            active = [[row[0]] + [row[i+1] for i in range(nbits) if x[i] == sign[i]]
                      for row, sign in zip(table, polarity)]
            chosen = [min((w for w in row if w is not None), default=None) for row in active]
            stored = [min(high if w is None else int(w * den) for w in row) for row in active]
            value = scan(chosen, edges)
            flow = cut_value(stored, edges, split)
            expected = 1 if value is None or value > threshold else 0 if value == threshold else -1
            actual = (flow > den * threshold) - (flow < den * threshold)
            assert expected == actual
            total += 1
            ties += expected == 0
            impossible += value is None
    assert ties and impossible
    print(f"{total} min-cut threshold controls passed, including {ties} exact ties and {impossible} infinite cover minima")


if __name__ == '__main__':
    check()
