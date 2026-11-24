"""Recover feasible orientations and check sharp repair costs for the original paired sample with a singleton per leaf."""
from collections import Counter
from itertools import combinations, product
from random import Random
from check_sparse_formulas import sample, star, subdivision, value, witness, measure, mask


def orientation(edges, n, caps):
    degree = Counter(x for e in edges for x in e)
    demand = {v: degree[v] - caps[v] + 1 for v in range(n) if caps[v] < degree[v]}
    at = [[] for _ in range(n)]
    for j, e in enumerate(edges):
        for v in e:
            at[v].append(j)
    match = {}
    def augment(v, seen):
        for j in at[v]:
            if j in seen:
                continue
            seen.add(j)
            if j not in match or augment(match[j], seen):
                match[j] = v
                return True
        return False
    for v, count in demand.items():
        for _ in range(count):
            if not augment(v, set()):
                return None
    return [match.get(j, e[0]) for j, e in enumerate(edges)]


def leaf_rows(n, edges):
    adj = [set() for _ in range(n)]
    for v, w in edges:
        adj[v].add(w)
        adj[w].add(v)
    return [mask(s) for s in adj if len(s) == 1]


def repair(n, edges, caps, f):
    feasible = orientation(edges, n, caps)
    assert feasible is not None
    deg = Counter(v for e in edges for v in e)
    required = {v for v in range(n) if deg[v] > caps[v]}
    used, missing, t = set(), [], 0
    for e, (p, neg) in zip(edges, sample(n, edges)):
        good = value(f, p)
        bad = value(f, neg)
        t += int(not good) + int(bad)
        if good and not bad:
            used.add(witness(f, p, neg))
        else:
            missing.append(e)
    t += sum(value(f, row) for row in leaf_rows(n, edges))
    for e in missing:
        used.update(required.intersection(e))
        if used.isdisjoint(e):
            used.add(e[0])
    assert required <= used
    rebuilt = star(edges, [a if a in used else next(v for v in e if v != a) for a, e in zip(feasible, edges)])
    count, reads = measure(rebuilt)
    assert all(reads[v] <= caps[v] for v in range(n))
    return count, t


def exhaustive_opt(n, edges, caps):
    deg = Counter(v for e in edges for v in e)
    best = None
    for choices in product((0, 1), repeat=len(edges)):
        head = [e[s] for e, s in zip(edges, choices)]
        owned = Counter(head)
        if all(deg[v] - owned[v] + bool(owned[v]) <= caps[v] for v in range(n)):
            cost = len(edges) + len(owned) - 1
            if best is None or cost < best[0]:
                best = cost, head
    return best


def run():
    core = [(0, 1), (0, 2), (0, 3), (1, 4), (1, 5)]
    core += [(v, j) for v in range(2, 6) for j in (6 + 2*(v-2), 7 + 2*(v-2))]
    n = 14
    caps = [2] * n
    goal, _ = exhaustive_opt(n, core, caps)
    short, owners = exhaustive_opt(n, core[1:], caps)
    assert (goal, short) == (18, 15)
    assert repair(n, core, caps, star(core[1:], owners)) == (18, 1)
    print("Subcubic tree: 18-gate optimum and 15-gate single-error witness, sharp coefficient three")

    base = list(combinations(range(4), 2))
    edges, _ = subdivision(4, base)
    n = 16
    caps = [2] * n
    # Old vertices head every outer edge; the middle edge goes to its first tip.
    head = [e[0] if j % 3 != 2 else e[1] for j, e in enumerate(edges)]
    old = star(edges, head)
    short = star([e for j, e in enumerate(edges) if j != 1],
                 [a for j, a in enumerate(head) if j != 1])
    assert measure(old)[0] == 27 and measure(short)[0] == 25
    count, errors = repair(n, edges, caps, short)
    assert (count, errors) == (27, 1)
    print("Three-edge K4 subdivision: 27-gate optimum and 25-gate single-error witness, sharp coefficient two")

    rng = Random(20611)
    cases = 0
    for n, ed in [(14, core), (16, edges)]:
        degree = Counter(v for e in ed for v in e)
        for _ in range(700):
            caps = [rng.randrange(1, degree[v] + 1) for v in range(n)]
            if orientation(ed, n, caps) is None:
                continue
            keep = [e for e in ed if rng.random() < 0.84]
            own = orientation(keep, n, caps)
            assert own is not None
            f = star(keep, own)
            if rng.random() < 0.5:
                # Replace by a permitted arbitrary formula, including misclassified negatives.
                labels = rng.sample(range(n), rng.randrange(1, n+1))
                f = labels.pop()
                for v in labels:
                    f = (rng.choice(("|", "&")), f, v)
            count, errors = repair(n, ed, caps, f)
            assert count <= measure(f)[0] + 3*errors
            cases += 1
    print(f"{cases} additional nonuniform feasible cap vectors: repaired formulas meet all original read caps and s+3t")


if __name__ == "__main__":
    run()
