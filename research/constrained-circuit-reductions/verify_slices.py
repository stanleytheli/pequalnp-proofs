"""Original finite checks for transportation-slices.md. Python standard library."""

from functools import lru_cache
from itertools import permutations
from math import prod
from random import Random


def reduce(x, p):
    return x % p if p else x


def half(x, p):
    if p:
        return x * pow(2, -1, p) % p
    assert x % 2 == 0
    return x // 2


def affine_perm(matrix, degree, p):
    """All coefficients through degree, by partial injective row assignments."""
    rows, cols = len(matrix), len(matrix[0])

    @lru_cache(maxsize=None)
    def expand(used):
        i = used.bit_count()
        if i == rows:
            return (1,) + (0,) * degree
        result = [0] * (degree + 1)
        for j, (a, b) in enumerate(matrix[i]):
            if used & (1 << j) or not (a or b):
                continue
            rem = expand(used | (1 << j))
            for k in range(degree + 1):
                result[k] += a * rem[k]
                if k:
                    result[k] += b * rem[k - 1]
        return tuple(reduce(v, p) for v in result)

    assert all(len(row) == cols for row in matrix)
    return expand(0)


def brute(A, p):
    return reduce(sum(prod(row[j] for row, j in zip(A, inj))
                      for inj in permutations(range(len(A[0])), len(A))), p)


def margins(A, rows, cols, p):
    assert all(reduce(sum(row) - target, p) == 0 for row, target in zip(A, rows))
    assert all(reduce(sum(col) - target, p) == 0 for col, target in zip(zip(*A), cols))


def rectangle(rng, r, s, p):
    m = r - 2
    rows = [rng.randint(-7, 7) for _ in range(r)]
    cols = [rng.randint(-7, 7) for _ in range(s-1)]
    cols.append(sum(rows) - sum(cols))
    X = [[rng.randint(-4, 4) for _ in range(m)] for _ in range(m)]

    def value(w):
        A = [[0] * s for _ in range(r)]
        for i in range(m):
            A[i][:m] = X[i]
        A[r-2][s-2] = w
        for i in range(r-1):
            A[i][-1] = rows[i] - sum(A[i])
        for j in range(s):
            A[-1][j] = cols[j] - sum(row[j] for row in A[:-1])
        margins(A, rows, cols, p)
        return brute(A, p)

    assert reduce(value(1) + value(-1) - 2*value(0) - 4*brute(X,p),p) == 0


def symmetric(rng, m, triangle, p):
    q = 2*m + 3*triangle
    n = q + 4
    X = [[rng.randint(-4, 4) for _ in range(m)] for _ in range(m)]
    d = [rng.randint(-5, 5) for _ in range(n)]
    rows = [rng.randint(-5, 5) for _ in range(n)]
    # Make the data integral even in the intermediate triangle solve over Q.
    if (sum(rows) - sum(d)) % 2:
        rows[-1] += 1

    H = [[0]*q for _ in range(q)]
    for i in range(m):
        for j in range(m):
            H[i][m+j] = H[m+j][i] = X[i][j]
    if triangle:
        for i in range(2*m, q):
            for j in range(2*m, q):
                H[i][j] = int(i != j)

    core = [[(d[i] if i == j else 0,H[i][j]) for j in range(q)] for i in range(q)]
    kappa = 2 if triangle else 1
    expected = reduce(kappa * brute(X, p)**2, p)
    assert affine_perm(core,q,p)[q] == expected

    for t in (-3, 0, 2):
        A = [[0]*n for _ in range(n)]
        for i in range(n):
            A[i][i] = d[i]
        for i in range(q):
            for j in range(q):
                A[i][j] += t * H[i][j]
            A[i][q] = A[q][i] = rows[i] - sum(A[i])
        h = [rows[k] - sum(A[k]) for k in range(q,n)]
        A[q][q+3] = A[q+3][q] = h[3]
        g = (h[0]-h[3], h[1], h[2])
        for i,j,k in [(0,1,2),(0,2,1),(1,2,0)]:
            A[q+i][q+j] = A[q+j][q+i] = half(g[i]+g[j]-g[k],p)
        margins(A,rows,rows,p)
        assert A == list(map(list,zip(*A)))
        assert [A[i][i] for i in range(n)] == d
        D = [[0]*n for _ in range(n)]
        for i in range(2):
            for j in range(2):
                D[q+i][q+2+j] = D[q+2+j][q+i] = (-1)**(i+j)
        margins(D,[0]*n,[0]*n,p)
        pencil = [[(A[i][j],D[i][j]) for j in range(n)] for i in range(n)]
        core_value = affine_perm([[(A[i][j],0) for j in range(q)] for i in range(q)],0,p)[0]
        assert affine_perm(pencil,5,p)[4:] == (reduce(4*core_value,p),0)

    # Evaluate the square-root recurrence to its full degree in a formal variable.
    lift = [[(int(i==j),X[i][j]-int(i==j)) for j in range(m)] for i in range(m)]
    double = [[(0,0) for _ in range(2*m)] for _ in range(2*m)]
    for i in range(m):
        for j in range(m):
            double[i][j+m] = double[j+m][i] = lift[i][j]
    squares = affine_perm(double,m,p)
    f = [1]
    for k in range(1,m+1):
        f.append(half(squares[k] - sum(f[i]*f[k-i] for i in range(1,k)),p))
    assert tuple(f) == affine_perm(lift,m,p)
    assert reduce(sum(f),p) == brute(X,p)


if __name__ == '__main__':
    rng = Random(0x58792)
    rectangles = squares = 0
    for p in (0,3,5,7):
        for r in (3,4,5):
            for s in (r,r+1,r+2):
                for _ in range(3):
                    rectangle(rng,r,s,p)
                    rectangles += 1
        for m in (1,2,3):
            for triangle in (False,True):
                symmetric(rng,m,triangle,p)
                squares += 1
    print(f'Passed {rectangles} rectangular and {squares} symmetric checks over Z, F3, F5 and F7.')
