"""Exact controls for positive permanent-oracle derivatives and support recovery."""
from collections import Counter
from itertools import combinations, combinations_with_replacement, permutations, product
from math import prod
from random import Random


def numeric_permanent(matrix):
    return sum(prod(matrix[i][j] for i, j in enumerate(p))
               for p in permutations(range(len(matrix))))


def polynomial_product(a, b):
    result = Counter()
    for e, c in a.items():
        for f, d in b.items():
            result[tuple(x+y for x, y in zip(e, f))] += c*d
    return result


def expand(circuit, n):
    """Ordinary semantic expansion, with a separate sum for each permutation."""
    one = Counter({(0,)*n: 1})
    values = []
    for op, arg in circuit:
        if op == "var":
            result = Counter({tuple(int(i == arg) for i in range(n)): 1})
        elif op == "const":
            result = Counter({(0,)*n: arg}) if arg else Counter()
        elif op == "add":
            result = values[arg[0]] + values[arg[1]]
        elif op == "mul":
            result = polynomial_product(values[arg[0]], values[arg[1]])
        elif op == "perm":
            result = Counter()
            for p in permutations(range(len(arg))):
                term = one
                for i, j in enumerate(p):
                    term = polynomial_product(term, values[arg[i][j]])
                result.update(term)
        else:
            raise ValueError(op)
        values.append(result)
    return values[-1]


def derivative(poly, labels):
    result = poly
    for j in labels:
        result = {e[:j]+(e[j]-1,)+e[j+1:]: c*e[j]
                  for e, c in result.items() if e[j]}
    return result


def value(poly, point):
    return sum(c*prod(x**i for x, i in zip(point, e)) for e, c in poly.items())


def labeled_jets(circuit, point, labels):
    """Compute numerical values of every mixed partial without expanding monomials."""
    values = []
    k = len(labels)
    for op, arg in circuit:
        out = []
        for mask in range(1 << k):
            active = [j for j in range(k) if mask & (1 << j)]
            if op == "var":
                total = point[arg] if not active else int(len(active) == 1 and labels[active[0]] == arg)
            elif op == "const":
                total = int(mask == 0)*arg
            elif op == "add":
                total = sum(values[g][mask] for g in arg)
            elif op == "mul":
                total = 0
                sub = mask
                while True:
                    total += values[arg[0]][sub]*values[arg[1]][mask ^ sub]
                    if not sub:
                        break
                    sub = (sub-1) & mask
            elif op == "perm":
                total = 0
                n = len(arg)
                cells = [(i, j) for i in range(n) for j in range(n)]
                for selected in product(cells, repeat=len(active)):
                    assigned = {}
                    for label, pos in zip(active, selected):
                        assigned[pos] = assigned.get(pos, 0) | (1 << label)
                    rows = {i for i, _ in assigned}
                    cols = {j for _, j in assigned}
                    if len(rows) != len(assigned) or len(cols) != len(assigned):
                        continue
                    gate_factors = prod(values[arg[i][j]][subset]
                                        for (i, j), subset in assigned.items())
                    if not gate_factors:
                        continue
                    minor = [[values[arg[i][j]][0] for j in range(n) if j not in cols]
                             for i in range(n) if i not in rows]
                    total += gate_factors*numeric_permanent(minor)
            else:
                raise ValueError(op)
            out.append(total)
        values.append(out)
    return values[-1]


def check_jets():
    # Repeated entries, shared parents, zero constants, nested or empty oracles.
    circuits = [
        [("var", 0), ("var", 1), ("const", 0), ("add", (0, 1)),
         ("perm", ((3, 0), (1, 3))), ("mul", (4, 4)),
         ("perm", ((5, 2, 3), (1, 4, 5), (0, 3, 4)))],
        [("var", 0), ("var", 1), ("const", 3), ("perm", ()),
         ("mul", (0, 1)), ("perm", ((0, 4), (4, 2))),
         ("perm", ((3, 5), (5, 4))), ("add", (6, 6))],
    ]
    rng = Random(145929)
    tests = 0
    for circuit in circuits:
        explicit = expand(circuit, 2)
        for labels in [(), (0,), (1, 0), (1, 1, 0), (0, 1, 0, 1)]:
            for point in [(0, 0), (1, 1), (0, 3), tuple(rng.randrange(1, 5) for _ in range(2))]:
                jets = labeled_jets(circuit, point, labels)
                for mask, actual in enumerate(jets):
                    active = [j for i, j in enumerate(labels) if mask & (1 << i)]
                    assert actual == value(derivative(explicit, active), point)
                    tests += 1
    return tests


def check_recovery():
    # Three disjoint two-element target supports. The final monomial introduces
    # a fourth, larger support that contains NONE of these target witnesses.
    n, h = 6, 2
    witness = {(0, 1), (2, 3), (4, 5)}
    variables = [("var", i) for i in range(n)]
    poly = variables + [("mul", (0, 0)), ("mul", (6, 1)),
                        ("mul", (2, 2)), ("mul", (8, 3)), ("mul", (9, 3)),
                        ("mul", (4, 5)), ("add", (7, 10)), ("add", (12, 11)),
                        ("mul", (0, 2)), ("mul", (14, 4)), ("add", (13, 15))]
    expanded = expand(poly, n)
    for corner in product((0, 1), repeat=n):
        if sum(corner) <= h:
            support = tuple(i for i, x in enumerate(corner) if x)
            assert bool(value(expanded, corner)) == (support in witness)
    assert value(expanded, (1, 0, 1, 0, 1, 0)) > 0
    source_excess = {s: min(sum(e)-h for e in expanded
                           if tuple(i for i, x in enumerate(e) if x) == s)
                     for s in witness}
    assert sorted(source_excess.values()) == [0, 1, 2]
    tested = 0
    for bound in range(3):
        found = set()
        for size in range(bound+1):
            for marks in combinations_with_replacement(range(n), size):
                keep = sorted(set(marks))
                deriv = derivative(expanded, [*marks, *keep])
                corrected = {tuple(x + int(i in keep) for i, x in enumerate(e))
                             for e in deriv}
                assert all(sum(x > 0 for x in e) >= h for e in corrected)
                found.update(tuple(i for i, x in enumerate(e) if x) for e in corrected if sum(e) == h)
                tested += 1
        assert found == {s for s, excess in source_excess.items() if excess <= bound}
    return tested


def check_faces():
    """Check every candidate K on random supports, also with spurious heavy supports."""
    rng = Random(224471)
    tested = 0
    for n in range(1, 8):
        for h in range(1, n+1):
            for _ in range(12):
                exponents = []
                for size in range(h, n+1):
                    for support in combinations(range(n), size):
                        if rng.randrange(5) == 0:
                            for _ in range(rng.randrange(1, 4)):
                                exponents.append(tuple(rng.choice((1, 1, 2, 4, 11))
                                                       if i in support else 0 for i in range(n)))
                if not any(sum(x > 0 for x in a) == h for a in exponents):
                    exponents.append((9,)*h + (0,)*(n-h))
                witness = {}
                for a in exponents:
                    support = frozenset(i for i, x in enumerate(a) if x)
                    if len(support) == h:
                        witness.setdefault(support, []).append(frozenset(i for i, x in enumerate(a) if x >= 2))
                rank = max(min(map(len, repeats)) for repeats in witness.values())
                recovered = set()
                for selection in combinations(range(n), rank):
                    keep = set(selection)
                    found = set()
                    for a in exponents:
                        outside = sum(x for i, x in enumerate(a) if i not in keep)
                        support = {i for i, x in enumerate(a) if x}
                        difference = (len(support)-h + len(keep-support) +
                                      sum(a[i]-1 for i in support-keep))
                        assert outside-(h-len(keep)) == difference >= 0
                        if not difference:
                            projected = tuple(1 if i in keep else x for i, x in enumerate(a))
                            assert all(x in (0, 1) for x in projected)
                            found.add(frozenset(i for i, x in enumerate(projected) if x))
                    expected = {s for s, repeats in witness.items()
                                if keep <= s and any(r <= keep for r in repeats)}
                    assert found == expected
                    recovered |= found
                    tested += 1
                assert recovered == set(witness)
    return tested


if __name__ == "__main__":
    print(f"{check_jets()} labeled oracle partials match expanded formal derivatives")
    print(f"{check_recovery()} correction slices recover exactly their permitted target supports")
    print(f"{check_faces()} padded fixed-rank faces have exactly their predicted target images")
