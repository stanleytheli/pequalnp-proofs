"""Finite controls for the dense counting gap and the coefficient-query families."""
from collections import Counter
from fractions import Fraction
from itertools import combinations, permutations, product
from math import comb, factorial


def single_cycle(row):
    v = 0
    reached = set()
    while v not in reached:
        reached.add(v)
        v = row[v]
    return v == 0 and len(reached) == len(row)


def rectangular(row):
    return all(j < max(1, i) for i, j in enumerate(row))


def reduced_tables():
    cases = coefficients = margins = 0
    for m in range(2, 6):
        rows = list(product(range(m), repeat=m))
        assert sum(map(single_cycle, rows)) == factorial(m-1)
        assert sum(map(rectangular, rows)) == factorial(m-1)
        for t, a, b in product(range(1, 5), (2, 7), (2, 5)):
            bits = list(product((0, 1), repeat=t))
            counts = [Counter(), Counter()]
            for row in rows:
                tables = []
                for h, selected in enumerate((single_cycle(row), rectangular(row))):
                    table = {}
                    for w in bits:
                        parity = sum(w) % 2
                        table[w] = 2*(b if parity else a) if selected else a+b
                        formal = a+b+(a-b)*selected*(-1)**sum(w)
                        assert table[w] == formal
                    counts[h].update(table.values())
                    tables.append(table)
                assert (tables[0][(0,)*t] - (a+b)) == (a-b)*single_cycle(row)
                for w in bits:
                    for i in range(t):
                        if w[i]:
                            continue
                        v = w[:i]+(1,)+w[i+1:]
                        sums = [tab[w]+tab[v] for tab in tables]
                        assert sums == [2*(a+b)]*2
                        margins += 1
                coefficients += len(bits)
            assert counts[0] == counts[1]
            cases += 1
    print(f"balanced tables: {cases} parameter cases, {coefficients} coefficients, {margins} conditional marginals")


def tagged_tables():
    m, ell, t, base = 3, 4, 3, 5
    rows_h, rows_q = set(), set()
    for row in product(range(m), repeat=m):
        mask = sum(1 << (m*i+j) for i,j in enumerate(row))
        if single_cycle(row):
            rows_h.add(mask)
        if rectangular(row):
            rows_q.add(mask)
    assert len(rows_h) == len(rows_q) == 2
    for hidden in range(1 << ell):
        for z in range(1 << ell):
            hist = [Counter(), Counter()]
            for x in range(1 << (m*m)):
                for w in range(1 << t):
                    sign = (-1)**bin(w).count("1")
                    easy = base+sign*(x in rows_q)
                    hard = base+sign*(x in (rows_h if z == hidden else rows_q))
                    if z != hidden:
                        assert hard == easy
                    if not w:
                        assert hard-easy == (z == hidden)*((x in rows_h)-(x in rows_q))
                    hist[0][easy] += 1
                    hist[1][hard] += 1
            assert hist[0] == hist[1]
    print("hidden tags: all 16 planted locations, all 16 per-tag histograms at every location")


def orbital_controls():
    # A small data orbit allows literal enumeration of all coordinate permutations.
    n, k = 7, 3
    planted = ((0, 1, 2), (0, 3, 4))
    incidences = Counter()
    for pi in permutations(range(n)):
        keys = {tuple(sorted(pi[i] for i in monomial)) for monomial in planted}
        assert len(keys) == len(planted)
        incidences.update(keys)
    assert set(incidences) == set(combinations(range(n), k))
    assert set(incidences.values()) == {factorial(n)*len(planted)//comb(n, k)}
    for t in range(1, 6):
        for affected in (0, 1):
            table = [5+(1-2*affected)*(-1)**bin(s).count("1") for s in range(2**t)]
            assert Counter(table) == {4: 2**(t-1), 6: 2**(t-1)}
            for s,i in product(range(2**t),range(t)):
                assert table[s]+table[s ^ (1 << i)] == 10
    print("coordinate orbit: 5040 relabelings, exact hit probability 2/35, five parity dimensions")


def rank(matrix):
    a = [[Fraction(v) for v in row] for row in matrix]
    rows = len(a)
    i = 0
    for j in range(len(a[0])):
        pivot = next((h for h in range(i,rows) if a[h][j]), None)
        if pivot is None:
            continue
        a[i],a[pivot] = a[pivot],a[i]
        for h in range(i+1,rows):
            ratio = a[h][j]/a[i][j]
            a[h] = [u-ratio*v for u,v in zip(a[h],a[i])]
        i += 1
        if i == rows:
            break
    return i


def bilinear_controls():
    for k in range(2, 10):
        for a,b in product((2,3,7),repeat=2):
            matrix = [[a if i != j else b for j in range(k)] for i in range(k)]
            hessian = [[0]*k+row for row in matrix]+[row+[0]*k for row in matrix]
            want = 1 if a == b else k
            assert rank(matrix) == want and rank(hessian) == 2*want
        for c,d in product(range(1,k+1), repeat=2):
            h = max(k,c*d)
            assert 2*k-c-d+2*h-1 >= 3*k-2
    print("bilinear forms: 72 exact rational matrix and Hessian ranks, all partition bounds through k=9")


if __name__ == "__main__":
    reduced_tables()
    tagged_tables()
    orbital_controls()
    bilinear_controls()
