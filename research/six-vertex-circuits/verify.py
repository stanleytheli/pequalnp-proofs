"""Check six-input catalogue coverage, labeling, gate ordering, and all truth tables."""
from collections import Counter
from itertools import combinations, permutations
from pathlib import Path
import json

def edge_mask(p, edges, positions):
    return sum(1 << positions[tuple(sorted((p[i], p[j])))] for i,j in edges)

def main():
    data = json.loads(Path(__file__).with_name('catalogue.json').read_text())
    pairs = list(combinations(range(6), 2))
    assert [tuple(p) for p in data['edge_order']] == pairs
    positions = {edge: i for i, edge in enumerate(pairs)}
    all_images = set()
    declared = set()
    histogram = Counter()
    for record in data['circuits']:
        graph, size, gates = record['graph'], record['size'], record['gates']
        edges = [e for i,e in enumerate(pairs) if graph & (1 << i)]
        assert set().union(*(set(e) for e in edges)) == set(range(6))
        images = {edge_mask(p, edges, positions) for p in permutations(range(6))}
        assert graph == min(images) and graph not in declared and all_images.isdisjoint(images)
        declared.add(graph)
        all_images.update(images)
        assert size == len(gates)
        for mask in range(64):
            wires = [bool(mask & (1 << i)) for i in range(6)]
            for op, a, b in gates:
                assert op in (0,1) and 0 <= a < len(wires) and 0 <= b < len(wires)
                wires.append((wires[a] and wires[b]) if op else (wires[a] or wires[b]))
            assert wires[-1] == any((mask & (1 << a)) and (mask & (1 << b)) for a,b in edges)
        histogram[size] += 1
    incident = [sum(1 << k for k,e in enumerate(pairs) if v in e) for v in range(6)]
    assert all_images == {g for g in range(1 << 15) if all(g & m for m in incident)}
    assert len(declared) == 122
    assert histogram == {5:7, 6:10, 7:24, 8:25, 9:33, 10:15, 11:7, 13:1}
    print('Checked', len(declared), 'isomorphism classes and', len(all_images), 'labeled graphs.')
    print('Optimum histogram', sorted(histogram.items()))

if __name__ == '__main__':
    main()
