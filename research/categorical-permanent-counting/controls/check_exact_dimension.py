"""Exact rank controls for the exceptional three-by-three factors (Python 3.8+)."""
from collections import Counter, defaultdict
from fractions import Fraction
from itertools import combinations, combinations_with_replacement, permutations, product


def matchings(n, board):
    cells = defaultdict(list)
    for e, uv in enumerate(board):
        cells[uv].append(e)
    return [frozenset(x) for p in permutations(range(n))
            for x in product(*(cells[i, p[i]] for i in range(n)))]


def full_factors(n, board, seen=None):
    if n <= 3:
        return int(n == 3 and len(set(board)) == 9)
    R, C = set(range(n)), set(range(n))
    for k in range(1, n):
        for T in combinations(R, k):
            L = set(T)
            N = {v for u, v in board if u in L}
            if len(N) == k:
                block = lambda u, v, X, Y: (sorted(X).index(u), sorted(Y).index(v))
                b1 = [block(u, v, L, N) for u, v in board if u in L]
                b2 = [block(u, v, R-L, C-N) for u, v in board if u not in L]
                return full_factors(k, b1) + full_factors(n-k, b2)
    for k in range(1, n-1):
        for T in combinations(R, k):
            L = set(T)
            N = {v for u, v in board if u in L}
            if len(N) != k+1:
                continue
            r1, c1, r2, c2 = map(sorted, (L, N, R-L, C-N))
            b1 = [(r1.index(u) if u in L else k, c1.index(v)) for u, v in board if v in N]
            b2 = [(r2.index(u), c2.index(v) if v not in N else n-k-1) for u, v in board if u not in L]
            return full_factors(k+1, b1) + full_factors(n-k, b2)
    return 0


def rational_rank(bits, n):
    pivot = {}
    for b in set(bits):
        row = [Fraction((b >> i) & 1) for i in range(n)]
        for j in sorted(pivot):
            if row[j]:
                multiple = row[j]
                row = [r - multiple * q for r, q in zip(row, pivot[j])]
        lead = next((j for j, x in enumerate(row) if x), None)
        if lead is not None:
            pivot[lead] = [x / row[lead] for x in row]
    return len(pivot)


def check(n, board, tally):
    matches = matchings(n, board)
    if not matches:
        return None
    live = set.union(set(), *(set(m) for m in matches))
    t = full_factors(n, [uv for i, uv in enumerate(board) if i in live])
    full = (1 << len(matches)) - 1
    edges = [sum(1 << j for j, m in enumerate(matches) if i in m) for i in live]
    hits = {0}
    for b in edges:
        hits |= {h | b for h in hits}
    pure = [h for h in hits if h ^ full in hits]
    dim0 = rational_rank([full] + edges, len(matches))
    dim1 = rational_rank([full] + pure, len(matches))
    assert dim1 == dim0 + t, (n, board, dim0, dim1, t)
    tally[t] += 1
    return len(matches), dim0, dim1, t


def representatives(n):
    patterns = range(1 << n)
    actions = [[sum(((m >> j) & 1) << p[j] for j in range(n)) for m in patterns]
               for p in permutations(range(n))]
    for rows in combinations_with_replacement(patterns, n):
        if all(tuple(sorted(a[m] for m in rows)) >= rows for a in actions):
            yield [(i, j) for i, bit in enumerate(rows) for j in range(n) if bit >> j & 1]


if __name__ == '__main__':
    tally = Counter()
    for n in range(1, 5):
        for board in representatives(n):
            check(n, board, tally)
            if n == 3:
                for edge in board:
                    check(n, board+[edge], tally)
    for counts in product(range(3), repeat=4):
        check(2, [divmod(i, 2) for i, c in enumerate(counts) for _ in range(c)], tally)
    glued = ([(i, j) for i in (0, 1) for j in (0, 1, 2)]
             + [(i, j) for i in (2, 3, 4) for j in (3, 4)]
             + [(i+2, i) for i in range(3)])
    for ext in ([], [(2, 0)], [(0, 0)]):
        print('two-brace splice', sorted(ext), check(5, glued+ext, tally))
    print('exact rank census by number of exceptional leaves:', sorted(tally.items()))
