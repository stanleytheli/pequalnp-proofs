"""Verify variable-threshold learning, fixed-threshold learning and padding on small hidden graphs."""
from functools import lru_cache
from itertools import combinations, permutations


def make_graph(n, edges):
    adj = [0] * n
    for a, b in edges:
        adj[a] |= 1 << b
        adj[b] |= 1 << a
    assert all(bin(row).count("1") == 3 for row in adj)
    @lru_cache(None)
    def alpha(mask):
        if not mask:
            return 0
        first = mask & -mask
        v = first.bit_length() - 1
        return max(alpha(mask ^ first), 1 + alpha((mask ^ first) & ~adj[v]))
    return alpha


def matching_graph(perm):
    b = len(perm)
    ed = [(i, (i + 1) % b) for i in range(b)]
    ed += [(b + i, b + (i + 1) % b) for i in range(b)]
    ed += [(i, b + j) for i, j in enumerate(perm)]
    return set(tuple(sorted(x)) for x in ed)


def learn(n, independent):
    classes = [[], [], [], []]
    recovered = set()
    for v in range(n):
        blocked = set()
        def discover(group, color):
            if not group or independent([v] + group):
                return
            if len(group) == 1:
                recovered.add((group[0], v))
                blocked.add(color)
                return
            mid = len(group) // 2
            discover(group[:mid], color)
            discover(group[mid:], color)
        for color, group in enumerate(classes):
            discover(group, color)
        color = next(c for c in range(4) if c not in blocked)
        classes[color].append(v)
    return recovered


def test():
    cases = 0
    for b in (4, 5):
        for perm in permutations(range(b)):
            edges = matching_graph(perm)
            n = 2*b
            alpha = make_graph(n, edges)
            def mask(group):
                return sum(1 << u for u in group)
            def ordinary(group):
                return alpha(mask(group)) == len(group)
            def padded(group):
                # One anchor is enabled in each of n-len(group) known disjoint K4s.
                return alpha(mask(group)) + n - len(group) >= n
            assert learn(n, ordinary) == learn(n, padded) == edges
            recovered = {(u, v) for u, v in combinations(range(n), 2)
                         if alpha((1 << u) | (1 << v)) < 2}
            assert recovered == edges
            for bits in range(1 << n):
                if bin(bits).count("1") >= 3:
                    assert alpha(bits) >= 2
            cases += 1
    print(f"{cases} hidden cubic graphs: learned exactly by variable thresholds, fixed threshold with anchors, and fixed pair tests")
    print("Every mask of size at least three qualifies at saving two on all tested permutation instances")


if __name__ == "__main__":
    test()
