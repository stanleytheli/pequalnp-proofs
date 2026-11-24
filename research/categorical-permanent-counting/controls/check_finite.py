"""Independent finite controls for the categorical cut and brace arguments."""
from itertools import permutations, product
from random import Random


def cut_controls():
    alphabet = (None, 0, 1, 2)
    words = [w for n in (1, 2, 3) for w in product(alphabet, repeat=n)]
    rectangles = identities = 0
    for l, r in product(words, repeat=2):
        pairs = list(product(l, r))
        if any(len({v for v in (a, b) if v is not None}) != 1 for a, b in pairs):
            continue
        rectangles += 1
        lo, ro = set(l) - {None}, set(r) - {None}

        def complete(loc, x):
            if len(loc) >= 2:
                assert x is not None
                return x
            return next(iter(loc), None)

        for a, b in pairs:
            g = a if a is not None else b
            for c in alphabet[1:]:
                lc, rc = complete(lo, a), complete(ro, b)
                assert (g == c) + ((c in lo) and (c in ro)) == (lc == c) + (rc == c)
                identities += 1
    return rectangles, identities


def matchings(n, cells):
    indices = {cell: i for i, cell in enumerate(cells)}
    mm = []
    for p in permutations(range(n)):
        if all((r, c) in indices for r, c in enumerate(p)):
            mm.append(sum(1 << indices[r, c] for r, c in enumerate(p)))
    return mm


def brace_controls(name, n, cells, exhaustive):
    mm = matchings(n, cells)
    full = (1 << len(cells)) - 1
    for i, e in enumerate(cells):
        for j, f in enumerate(cells):
            if e[0] != f[0] and e[1] != f[1]:
                assert any((m >> i) & (m >> j) & 1 for m in mm)
    rectangles = 0
    for r, s in permutations(range(n), 2):
        for a, b in permutations(range(n), 2):
            bad = sum(1 << i for i, (v, w) in enumerate(cells) if v in (r, s) and w in (a, b))
            assert any(m & bad == 0 for m in mm)
            rectangles += 1
    maskset = range(1 << len(cells))
    if not exhaustive:
        rng = Random(194827)
        maskset = [rng.randrange(full+1) for _ in range(4000)]
    cases = pure = 0
    for A in maskset:
        cases += 1
        avoid_A = [m for m in mm if m & A == 0]
        if not avoid_A or len(avoid_A) == len(mm):
            continue
        # Any second color must avoid every edge used by an A-hitting matching.
        # Taking all remaining cells gives the maximal possible second color.
        B = full
        repeated_A = False
        for m in mm:
            if m & A:
                B &= ~m
                repeated_A |= bin(m & A).count("1") >= 2
        if not all(m & B for m in avoid_A):
            continue
        pure += 1
        repeated_B = any(bin(m & B).count("1") >= 2 for m in avoid_A)
        assert not (repeated_A and repeated_B)
        for m in mm:
            for c, d, repeated in [(A, B, repeated_A), (B, A, repeated_B)]:
                val = 1 - bin(m & d).count("1") if repeated else bin(m & c).count("1")
                assert val == bool(m & c)
    print(name, 'matchings', len(mm), 'ordered_rectangles', rectangles,
          'first_colors', cases, 'nonconstant_binary_when_maximal', pure)


def b3_exception():
    n = 3
    cells = list(product(range(n), repeat=2))
    A = sum(1 << cells.index(e) for e in [(0, 0), (1, 2)])
    B = sum(1 << cells.index(e) for e in [(0, 2), (1, 0)])
    mm = matchings(n, cells)
    parities = [sum(p[i] > p[j] for i in range(n) for j in range(i+1, n)) % 2
                for p in permutations(range(n))]
    assert all(bool(m & A) ^ bool(m & B) for m in mm)
    assert max(bin(m & A).count("1") for m in mm) == max(bin(m & B).count("1") for m in mm) == 2
    for i in range(9):
        assert sum((m >> i) & 1 for m, p in zip(mm, parities) if p == 0) == 1
        assert sum((m >> i) & 1 for m, p in zip(mm, parities) if p == 1) == 1
    totals = [sum(bool(m & A) for m, p in zip(mm, parities) if p == h) for h in (0, 1)]
    assert totals == [2, 1]


if __name__ == '__main__':
    print('valid rectangles and indicator comparisons:', *cut_controls())
    b3_exception()
    print('K3,3 nonaffine counterexample: all three even and three odd vertices verified')
    brace_controls('K4,4', 4, list(product(range(4), repeat=2)), True)
    brace_controls('K4,4 minus diagonal', 4,
                   [(i, j) for i, j in product(range(4), repeat=2) if i != j], True)
    brace_controls('K5,5 minus diagonal', 5,
                   [(i, j) for i, j in product(range(5), repeat=2) if i != j], False)
