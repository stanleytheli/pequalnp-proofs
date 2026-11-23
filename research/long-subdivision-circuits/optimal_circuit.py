"""Build an optimal edge-detection circuit for a specified long subdivision.

Usage: python3 optimal_circuit.py input.json
Input: {"vertices": 3, "paths": [[0,1,7],[1,2,8],[2,0,9]]}
Input wires precede all gate wires. Each gate is ["AND"|"OR", first, second].
"""
import json
import sys


def choose_cover(pairs):
    """Exact vertex cover on the remaining quotient. Loops force a vertex."""
    forced = {u for u, v in pairs if u == v}
    edges = {(min(u, v), max(u, v)) for u, v in pairs if u not in forced and v not in forced}

    def search(remaining):
        if not remaining:
            return set()
        a, b = min(remaining)
        take_a = {a} | search({e for e in remaining if a not in e})
        take_b = {b} | search({e for e in remaining if b not in e})
        return take_a if len(take_a) <= len(take_b) else take_b

    return forced | search(edges)


def original_choices(n, paths):
    neighbors = [[] for _ in range(n)]
    for u, v, length in paths:
        if length % 2 == 0:
            neighbors[u].append(v)
            neighbors[v].append(u)
    parts = []
    owner = [-1] * n
    for u in range(n):
        if owner[u] != -1:
            continue
        idx = len(parts)
        owner[u] = idx
        part = [u]
        for v in part:
            for w in neighbors[v]:
                if owner[w] == -1:
                    owner[w] = idx
                    part.append(w)
        parts.append(part)
    cyclic = {i for i, part in enumerate(parts) if sum(len(neighbors[v]) for v in part) >= 2*len(part)}
    quotient = [(owner[u], owner[v]) for u, v, length in paths
                if length % 2 and owner[u] not in cyclic and owner[v] not in cyclic]
    selected = cyclic | choose_cover(quotient)
    return {v for i in selected for v in parts[i]}


def build(n, paths):
    if not isinstance(n, int) or n < 1 or not paths:
        raise ValueError("expected positive vertex count and at least one path")
    for u, v, length in paths:
        if not all(isinstance(x, int) for x in (u, v, length)) or not (0 <= u < n and 0 <= v < n and u != v and length >= 7):
            raise ValueError("each path needs distinct valid endpoints and length at least seven")
    originals = original_choices(n, paths)
    cover = set(originals)
    edges = []
    next_wire = n
    for u, v, length in paths:
        middle = list(range(next_wire, next_wire + length-1))
        next_wire += length-1
        use_even_positions = u in originals if length % 2 else u in originals and v in originals
        cover.update(middle[1::2] if use_even_positions else middle[0::2])
        chain = [u] + middle + [v]
        edges.extend(zip(chain, chain[1:]))
    stars = {}
    for u, v in edges:
        if u in cover:
            stars.setdefault(u, []).append(v)
        else:
            assert v in cover
            stars.setdefault(v, []).append(u)
    gates = []

    def emit(op, u, v):
        gates.append([op, u, v])
        return next_wire + len(gates) - 1

    def join(wires):
        acc = wires[0]
        for w in wires[1:]:
            acc = emit("OR", acc, w)
        return acc

    output = join([emit("AND", u, join(leaves)) for u, leaves in stars.items()])
    assert len(gates) == len(edges) + len(cover) - 1
    return {"inputs": next_wire, "gates": gates, "output": output, "cover": sorted(cover)}


if __name__ == "__main__":
    with open(sys.argv[1], encoding="utf-8") as f:
        instance = json.load(f)
    print(json.dumps(build(instance["vertices"], instance["paths"])))
