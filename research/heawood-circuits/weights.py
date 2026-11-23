"""Check exact monotone-formula lower bounds for Heawood and four induced graphs.

Run with standard Python 3, with weights-8127.json beside this file.
The matrix entries and every rectangle calculation are integers.
"""
from itertools import combinations
from pathlib import Path
import json

LINES = ((0, 1, 3), (0, 2, 6), (1, 5, 6), (0, 4, 5), (3, 4, 6), (2, 3, 5), (1, 2, 4))
EDGES = [(point, 7 + line) for line, points in enumerate(LINES) for point in points]
NEIGHBORS = [sum(1 << (a if v == b else b) for a, b in EDGES if v in (a, b)) for v in range(14)]
FULL = (1 << 14) - 1


def induced_edges(mask):
    return [edge for edge in EDGES if all(mask & (1 << v) for v in edge)]


def universal(mask):
    edges = induced_edges(mask)
    columns = []
    for z in range(14):
        other_side = 127 if z >= 7 else 127 << 7
        columns.append(mask & ((1 << z) | (other_side & ~NEIGHBORS[z])))
    weights = []
    for a, b in edges:
        row = []
        for z in range(14):
            opposite = a if z >= 7 else b
            row.append(2 if z in (a, b) else -1 if NEIGHBORS[z] & (1 << opposite) else 1)
        weights.append(row)
    return edges, columns, weights, 6


def check_weights(mask, edges, columns, weights, cap):
    assert edges == induced_edges(mask)
    assert len(columns) > 0 and len(weights) == len(edges) and cap > 0
    assert all(len(row) == len(columns) and all(type(w) is int for w in row) for row in weights)
    for independent in columns:
        assert independent >= 0 and not independent & ~mask
        assert all(not (independent & (1 << a) and independent & (1 << b)) for a, b in edges)
    max_weight = 0
    for v in range(14):
        incident = [i for i, edge in enumerate(edges) if v in edge]
        eligible = [j for j, independent in enumerate(columns) if not independent & (1 << v)]
        for k in range(1, len(incident) + 1):
            for rows in combinations(incident, k):
                # Among all column subsets, choosing each positive column sum is optimal.
                best = sum(max(0, sum(weights[i][j] for i in rows)) for j in eligible)
                max_weight = max(max_weight, best)
    assert max_weight <= cap
    total = sum(map(sum, weights))
    return total, cap, (total + cap - 1) // cap


def star_leaf_upper(mask, edges):
    vertices = [v for v in range(14) if mask & (1 << v)]
    for k in range(len(vertices) + 1):
        for choice in combinations(vertices, k):
            chosen = set(choice)
            if all(a in chosen or b in chosen for a, b in edges):
                return len(edges) + k
    raise AssertionError("no vertex cover")


def main():
    record = json.loads(Path(__file__).with_name('weights-8127.json').read_text())
    assert record['mask'] == 8127
    for mask in (4091, 8127, 8175, 8191, FULL):
        data = universal(mask)
        if mask == 8127:
            data = ([tuple(edge) for edge in record['edges']], record['columns'],
                    record['weights'], record['denominator'])
        total, cap, leaves = check_weights(mask, *data)
        upper = star_leaf_upper(mask, data[0])
        assert leaves == upper
        print(f"mask {mask:5d}  edges {len(data[0]):2d}  weight {total}/{cap}"
              f"  exact formula leaves {leaves:2d}  gates {leaves-1:2d}")


if __name__ == '__main__':
    main()
