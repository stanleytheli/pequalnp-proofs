"""Check physical circuit witnesses by complete truth tables and independent cover search."""
from optimal_circuit import build


def edge_list(n, paths):
    result = []
    for a, b, length in paths:
        vertices = [a] + list(range(n, n + length - 1)) + [b]
        n += length - 1
        result.extend(zip(vertices, vertices[1:]))
    return n, result


def check(n, paths):
    circuit = build(n, paths)
    size, edges = edge_list(n, paths)
    assert size == circuit["inputs"]
    cover = set(circuit["cover"])
    assert all(a in cover or b in cover for a, b in edges)
    masks = [(1 << a) | (1 << b) for a, b in edges]
    tau = min(choice.bit_count() for choice in range(1 << size) if all(e & choice for e in masks))
    assert len(circuit["gates"]) == len(edges) + tau - 1
    width = 1 << size
    every = (1 << width) - 1
    wires = []
    for v in range(size):
        half = 1 << v
        block = (1 << half) - 1
        wires.append(((every // ((1 << (2*half)) - 1)) * block) << half)
    expected = 0
    for a, b in edges:
        expected |= wires[a] & wires[b]
    for op, a, b in circuit["gates"]:
        assert 0 <= a < len(wires) and 0 <= b < len(wires) and op in {"OR", "AND"}
        wires.append(wires[a] | wires[b] if op == "OR" else wires[a] & wires[b])
    assert wires[circuit["output"]] == expected
    return width


if __name__ == "__main__":
    cases = [(2, [(0, 1, length)]) for length in range(7, 12)]
    cases += [(2, [(0, 1, a), (1, 0, b)]) for a, b in [(7, 7), (7, 8), (8, 8)]]
    cases += [(3, [(0, 1, 7), (1, 2, 8)]), (4, [(0, 1, 7), (2, 3, 7)])]
    count = sum(check(n, paths) for n, paths in cases)
    print(f"Verified {len(cases)} constructed circuits on all {count:,} input assignments and checked minimum covers independently.")
