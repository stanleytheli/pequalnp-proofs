"""Exhaust the switch graph of a small nonbipartite matching instance and a dual-rail face."""
from itertools import combinations, product
from check_fixed_sample import host, solver


def matching_sample(n):
    edges = list(combinations(range(n), 2))
    selector = {e: j for j, e in enumerate(edges, 1)}
    next_variable = len(edges)
    cnf = []
    for v in range(n):
        bits = [selector[e] for e in edges if v in e]
        prefix = bits[0]
        for new in bits[1:]:
            next_variable += 1
            out = next_variable
            cnf.extend([(out, -prefix, -prefix), (out, -new, -new),
                        (-out, prefix, new), (-prefix, -new, -new)])
            prefix = out
        cnf.append((prefix, prefix, prefix))
    cnf.extend([(-i, -i, ('switch', e)) for e, i in selector.items()])
    return edges, host(cnf)


def check_matching():
    ed, graph = matching_sample(4)
    evaluate = solver(graph)
    minimum, yes = [], 0
    for s in range(1 << len(ed)):
        mask = {e for j, e in enumerate(ed) if (s >> j) & 1}
        correct = any(set(a).isdisjoint(b) for a, b in combinations(mask, 2))
        assert evaluate(mask) == correct
        if correct:
            yes += 1
            if len(mask) == 2:
                minimum.append(mask)
    assert len(minimum) == 3
    assert all(set.union(*(set(e) for e in solution)) == set(range(4)) for solution in minimum)
    print(f"K4: all 64 permission masks checked on cubic graph, {yes} feasible, three perfect matchings on the minimum-weight face")


def check_rails():
    # Arbitrary nonmonotone accepted language on two original bits: equality.
    cnf = [(-1, 2, 2), (1, -2, -2)]
    rails = list(product((1, 2), (0, 1)))
    for v, bit in rails:
        # This rule is active on precisely the assignments using this rail.
        lit = -v if bit else v
        cnf.append((lit, lit, ('switch', (v, bit))))
    evaluate = solver(host(cnf))
    minimum = set()
    for code in range(16):
        mask = {r for j, r in enumerate(rails) if (code >> j) & 1}
        extensions = [b for b in (0, 1) if {(1, b), (2, b)} <= mask]
        assert evaluate(mask) == bool(extensions)
        if len(mask) == 2 and extensions:
            minimum.add((extensions[0], extensions[0]))
    assert minimum == {(0, 0), (1, 1)}
    print("Dual rails: all 16 ambient masks checked, and exact weight-two face projects onto 00 and 11")


if __name__ == "__main__":
    check_matching()
    check_rails()
