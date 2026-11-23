"""Exact signed-weight capacities for all shared two-input bottom gates."""
from functools import lru_cache
from itertools import combinations
from weights import FULL, universal

EDGES, COLUMNS, W, _ = universal(FULL)


def maximum_by_axis(matrix):
    """For each row mask, give the maximum rectangle with rows inside the mask."""
    m = len(matrix)
    count = 1 << m
    columns = len(matrix[0]) if m else 0
    values = [0] * count
    # Keep one vector of column sums. Binary reflected Gray order flips one row.
    sums = [0] * columns
    previous = 0
    for step in range(1, count):
        mask = step ^ (step >> 1)
        changed = mask ^ previous
        row = matrix[changed.bit_length() - 1]
        sign = 1 if mask & changed else -1
        sums = [a + sign*b for a, b in zip(sums, row)]
        values[mask] = sum(x for x in sums if x > 0)
        previous = mask
    for i in range(m):
        flag = 1 << i
        for mask in range(count):
            if flag & mask:
                values[mask] = max(values[mask], values[mask ^ flag])
    two = max(x + values[count-1 ^ mask] for mask, x in enumerate(values))
    return values[-1], two


def capacities(p,q):
    rows = [i for i in range(len(EDGES)) if (p>>i)&1]
    cols = [j for j in range(len(COLUMNS)) if (q>>j)&1]
    if not rows or not cols:
        return 0,0,0
    matrix = [[W[i][j] for j in cols] for i in rows]
    transpose = list(zip(*matrix))
    one, row2 = maximum_by_axis(matrix)
    one_t, col2 = maximum_by_axis(transpose)
    assert one == one_t
    positive = sum(max(0,v) for row in matrix for v in row)
    return one, max(row2,col2), positive


def raw(v):
    return (sum(1<<i for i,e in enumerate(EDGES) if v in e),
            sum(1<<j for j,m in enumerate(COLUMNS) if not m&(1<<v)))


def combine(a,b,op):
    return (a[0]&b[0],a[1]|b[1]) if op=='and' else (a[0]|b[0],a[1]&b[1])


def main():
    table = {}
    for op in ('and','or'):
        for v,w in combinations(range(14),2):
            case=(op,'same' if v//7==w//7 else 'edge' if (v,w) in EDGES else 'nonedge')
            cap = capacities(*combine(raw(v),raw(w),op))
            if case in table:
                assert table[case] == cap
            table[case]=cap
            assert cap[1] <= 18 and cap[2] <= 24
    for case, cap in sorted(table.items()):
        print(*case,*cap)


if __name__ == '__main__':
    main()


def three_rectangles(p, q):
    """Exact three-disjoint-rectangle weight, with column choices independent."""
    from itertools import combinations_with_replacement
    rows = [i for i in range(len(EDGES)) if (p >> i) & 1]
    cols = [j for j in range(len(COLUMNS)) if (q >> j) & 1]
    matrix = [[W[i][j] for j in cols] for i in rows]
    if len(cols) < len(rows):
        matrix = list(zip(*matrix))
    n, m = len(matrix), len(matrix[0])
    sums = [[0] * m]
    for mask in range(1, 1 << n):
        bit = mask & -mask
        sums.append([x+y for x,y in zip(sums[mask ^ bit], matrix[bit.bit_length()-1])])
    best = 0
    for a,b,c in combinations_with_replacement(range(1 << n), 3):
        ab, ac, bc = not a & b, not a & c, not b & c
        all_disjoint = ab and ac and bc
        score = 0
        for x,y,z in zip(sums[a],sums[b],sums[c]):
            score += max(0, x, y, z, (x+y) if ab else 0, (x+z) if ac else 0,
                         (y+z) if bc else 0, (x+y+z) if all_disjoint else 0)
        best = max(best,score)
    return best
