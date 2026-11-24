"""Compare the full gate/cap theorem with independent orientation enumeration and formula synthesis."""
from itertools import combinations, product


def graph_data(n, edges):
    degree = tuple(sum(v in e for e in edges) for v in range(n))
    sizes = [bin(s).count("1") for s in range(1 << n)]
    inside = [sum((s >> a) & (s >> b) & 1 for a, b in edges) for s in range(1 << n)]
    alpha = [max(sizes[t] for t in range(1 << n) if t & ~s == 0 and inside[t] == 0) for s in range(1 << n)]
    return degree, inside, alpha


def predicted(n, edges, data, budget):
    degree, inside, alpha = data
    required = sum(1 << v for v in range(n) if budget[v] < degree[v])
    region = required
    while region:
        if inside[region] > sum(budget[v] - 1 for v in range(n) if region >> v & 1):
            return None
        region = (region - 1) & required
    return len(edges) + n - 1 - alpha[((1 << n) - 1) ^ required]


def star_options(n, edges, degree):
    options = set()
    for orientation in product((0, 1), repeat=len(edges)):
        owned = [0] * n
        for e, k in zip(edges, orientation):
            owned[e[k]] += 1
        reads = tuple(d - a + (a > 0) for d, a in zip(degree, owned))
        options.add((reads, sum(reads) - 1))
    return options


def exact_formulas(n, edges, caps):
    # These functions are disjunctions of all physical edges. Constants simplify away
    # in every nonconstant optimum, so enumerate trees by their exact named-leaf counts.
    rows = 1 << n
    variables = [sum(1 << s for s in range(rows) if s >> i & 1) for i in range(n)]
    target = sum(1 << s for s in range(rows) if any((s >> a) & (s >> b) & 1 for a, b in edges))
    zero = (0,) * n
    costs = {}
    states = {}
    vectors = sorted(product(*(range(c + 1) for c in caps)), key=sum)
    for reads in vectors:
        count = sum(reads)
        if count == 0:
            continue
        if count == 1:
            values = {variables[reads.index(1)]}
        else:
            values = set()
            for left in product(*(range(r + 1) for r in reads)):
                right = tuple(r - l for l, r in zip(left, reads))
                if left == zero or right == zero or left > right:
                    continue
                for a in states[left]:
                    for b in states[right]:
                        values.add(a & b)
                        values.add(a | b)
        states[reads] = values
        if target in values:
            costs[reads] = count - 1
    return costs


def run():
    examples = [
        (3, [(0, 1)]),  # isolated input plus a degree-one edge
        (4, [(0, 1), (1, 2), (2, 3)]),
        (5, [(0, 1), (1, 2), (2, 3), (3, 4), (4, 0)]),
        (6, [(0, 1), (1, 2), (2, 3), (3, 4), (4, 0), (0, 5)]),
        (7, [(0, 1), (0, 2), (0, 3), (1, 4), (2, 5), (3, 6)])
    ]
    trials = 0
    exact = 0
    for n, edges in examples:
        data = graph_data(n, edges)
        options = star_options(n, edges, data[0])
        exhaustive = n <= 4
        if exhaustive:
            formulas = exact_formulas(n, edges, tuple(max(1, d) for d in data[0]))
        for budget in product(*(range(max(1, d) + 1) for d in data[0])):
            want = predicted(n, edges, data, budget)
            opt = min((cost for reads, cost in options if all(a <= b for a, b in zip(reads, budget))), default=None)
            assert want == opt
            trials += 1
            if exhaustive:
                full = min((s for reads, s in formulas.items() if all(a <= b for a, b in zip(reads, budget))), default=None)
                assert full == opt
                exact += 1
    print(f"All {trials} read-budget vectors agree with exhaustive ownership optimization on five graphs")
    print(f"All {exact} cap vectors on the isolated-edge and 4-path examples also agree with full truth-table tree synthesis")


if __name__ == "__main__":
    run()
