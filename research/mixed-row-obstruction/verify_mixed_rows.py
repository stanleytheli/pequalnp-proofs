"""Verify supports three and four when a low rank-three row is present.

All phase configurations and certificates are regenerated from the formulas.
Requires Python 3.10 or newer, NumPy and Python assertions enabled.
"""

import argparse
from collections import Counter
from fractions import Fraction
from functools import reduce
from itertools import combinations_with_replacement, product
from math import gcd, lcm
from random import Random

import numpy as np

import verify_full_rows as full
from verify_sparse_rows import (
    Rat, check_open, divexact, gcdq, idet, inter, multiply, passes,
    plus, primitive, quotient, raw_mac, remove, trim,
)



def times(*xs):
    return reduce(multiply, xs, [1])


def primitive_common(rows):
    g = reduce(gcdq, rows, [])
    rr = [divexact(r, g) for r in rows] if g else rows
    den = reduce(gcd, (x for r in rr for x in r), 0) or 1
    return ([[x // den for x in r] for r in rr], g)


def common_den(rats):
    d = [1]
    for X in rats:
        val = X.d
        g = gcdq(d, val)
        v = times(divexact(d, g), val)
        c = reduce(gcd, v, 0)
        c1 = reduce(gcd, d, 0)
        c2 = reduce(gcd, val, 0)
        z = lcm(c1, c2)
        d = [x // c * z for x in v]
    return (d, [times(divexact(d, r.d), r.n) for r in rats])


def squarefree(p):
    p = primitive(p)
    if len(p) <= 1:
        return p
    derivative = [j * x for j, x in enumerate(p) if j]
    return quotient(p, gcdq(p, derivative))


def duplicate(a):
    if isinstance(a, list):
        return [duplicate(v) for v in a]
    z = np.zeros_like(a)
    return np.block([[a, z], [z, a]])


def quad(P, Q):
    I = np.eye(len(P), dtype=object)
    Z = np.zeros_like(P)
    return np.block([[Z, -Q], [I, -P]])


def cm(u, inside):
    free = tuple(product(range(4), (-1, 0, 2)))
    for cols in combinations_with_replacement(free, 5 - u):
        if inside and all((s != -1 for h, s in cols)):
            continue
        if not inside and all((s == -1 for h, s in cols)):
            continue
        if not inside:
            nz = next((s for h, s in cols if s != -1))
            if nz != 0:
                continue
        yield (*((0, 0 if inside else -1),) * u, *cols)


def choices(u, shape):
    E = ((0,) * 5, *zip(*shape))
    high = E[1]
    vals = set(high)
    if vals == {0, 2}:
        a = [('sign', 1, 0, (), (), 0, 0)]
    elif len(vals) == 3:
        k = next((v for v in vals if (v + 2) % 4 not in vals))
        B = tuple((j for j in range(5) if high[j] == (k + 1) % 4))
        C = tuple((j for j in range(5) if high[j] == (k - 1) % 4))
        a = [('three', 1, 0, B, C, 0, 0), ('three', 1, 0, C, B, 1, 0)]
    else:
        return
    b = [a]
    S = [j for j in range(5) if E[2][j] != -1]
    T = [j for j in range(5) if j not in S]
    for i in range(2):
        rs = [(E[2][j] - E[i][j]) % 4 for j in S]
        val = set(rs)
        c = rs[0]
        if len(val) == 1:
            a = []
            for z in product(range(3), repeat=len(T)):
                if 1 in z and 2 in z:
                    P = tuple((j for j, k in zip(T, z) if k == 1))
                    Q = tuple((j for j, k in zip(T, z) if k == 2))
                    a.append(('unicolor', 2, i, P, Q, 0, c))
            if not a:
                return
        elif val == {c, (c + 2) % 4}:
            P = tuple((j for j, k in zip(S, rs) if k == c))
            Q = tuple((j for j, k in zip(S, rs) if k != c))
            a = [('sparse', 2, i, P, Q, 0, 0), ('sparse', 2, i, Q, P, 1, 0)]
        else:
            return
        b.append(a)
    return (E, b)


def constraints(E, pp, A, B):
    U = np.array([[full.G[t] if t != -1 else 0 for t in row] for row in E])
    F = np.zeros((8, 4, 5), dtype=complex)
    for i in range(3):
        F[i, i] = U[i]
    F[3, 3, list(A)] = 1
    F[4, 3, list(B)] = 1
    for n, (tag, i, k, P, Q, o, c) in enumerate(pp, 5):
        if tag == 'sign':
            F[n, i] = -U[k]
            F[n, k] = U[i]
        elif tag == 'three':
            F[n, i, list(P)] = U[i, list(P)]
            F[n, k, list(Q)] = U[k, list(Q)]
        elif tag == 'sparse':
            F[n, i, list(Q)] = U[i, list(Q)]
            F[n, k, list(P)] = U[k, list(P)]
        else:
            F[n, i, list(P)] = full.G[c] * U[k, list(P)]
            F[n, k, list(Q)] = U[k, list(Q)]
    return (F.reshape(8, 20), U)


def iter_all(inside):
    for u in (2, 3, 4):
        for na in range(1, u // 2 + 1):
            A = tuple(range(na))
            B = tuple(range(na, u))
            for sh in cm(u, inside):
                z = choices(u, sh)
                if z is None:
                    continue
                E, opts = z
                for j, pp in enumerate(product(*opts)):
                    yield (u, na, sh, j, E, pp, A, B)


def geom(u, na, sh, o):
    E, opts = choices(u, sh)
    pp = []
    for opts1 in opts[::-1]:
        o, j = divmod(o, len(opts1))
        pp.append(opts1[j])
    return (E, pp[::-1], tuple(range(na)), tuple(range(na, u)))


def build(u, na, sh, o, inside):
    E, pp, A, B = geom(u, na, sh, o)
    F, V = constraints(E, pp, A, B)
    if inside:
        assert na == 1
        n = 6 - u
        T = np.zeros((5, n), dtype=int)
        T[0, 0] = T[1, 0] = 1
        T[u:, 1:] = 2 * np.eye(5 - u, dtype=int)
    else:
        n = 4
        T = np.vstack([[int(j in B) - int(j in A) for j in range(1, 5)], np.eye(4, dtype=int)])
    S = V @ T
    forms = [list(map(full.zz, r)) for r in S]
    if inside:
        forms.extend([[(int(i == j), 0) for j in range(n)] for i in range(n)])
    else:
        forms.extend([list(map(full.zz, r)) for r in T])
        forms.append(list(map(full.zz, T[list(A)].sum(0))))
    eq = []

    def wr(arr):
        q = {}
        for i in range(n):
            for j in range(i, n):
                x = arr[i, j] if i == j else arr[i, j] + arr[j, i]
                if x:
                    q[tuple((int(a == i) + int(a == j) for a in range(n)))] = x
        eq.append(q)

    def agg(v, J):
        return v[list(J)] @ T[list(J)] if J else np.zeros(n, dtype=complex)
    op = np.outer
    for tag, i, k, P, Q, ori, phase in pp:
        if tag == 'sign':
            forms.extend([list(map(full.zz, S[i] + S[k])), list(map(full.zz, S[i] - S[k]))])
        elif tag == 'three':
            a, b, c = (agg(V[k], [j for j in range(5) if j not in (*P, *Q)]), agg(V[k], P), agg(V[k], Q))
            gam = -1j if ori else 1j
            wr(op(a, a) - op(b, b) + op(c, c) - 2 * (1 + gam) * op(b, c))
        elif tag == 'sparse':
            wr(op(S[k], agg(V[i], Q)) + op(S[i], agg(V[k], P)))
        else:
            wr(full.G[phase] * op(S[k], agg(V[k], P)) + op(S[i], agg(V[k], Q)) - op(S[k], S[i]))
    return (E, pp, A, B, V, T, forms, eq)


def gram(V, pp, A, B, M, p, unit=False):
    r = full.sqrt_i(p)
    d = len(M[0][0])
    W = np.array([np.asarray((a + r * b) % p, dtype=np.int64) for a, b in M])
    ph = (V.real.astype(np.int64) + r * V.imag.astype(np.int64)) % p
    v = ph[:, :, None, None] * W[None, :, :, :] % p
    s = v.sum(1) % p
    F = np.zeros((9, 4, 5, d, d), dtype=np.int64)
    for i in range(3):
        F[i, i] = v[i]
    for j in A:
        F[3, 3, j] = W[j]
    for j in B:
        F[4, 3, j] = W[j]
    if unit:
        assert len(A) == len(B) == 1
        F[3, 3, A[0]] = F[4, 3, B[0]] = np.eye(d, dtype=np.int64)
    for g, (tag, i, k, P, Q, o, ph) in enumerate(pp, 5):
        if tag == 'sign':
            for j in range(5):
                F[g, i, j] = -s[k] @ v[k, j] % p
                F[g, k, j] = s[i] @ v[i, j] % p
        elif tag == 'three':
            for j in P:
                F[g, i, j] = s[k] @ v[i, j] % p
            for j in Q:
                F[g, k, j] = s[i] @ v[k, j] % p
        elif tag == 'sparse':
            for j in Q:
                F[g, i, j] = s[k] @ v[i, j] % p
            for j in P:
                F[g, k, j] = s[i] @ v[k, j] % p
        else:
            for j in P:
                F[g, i, j] = pow(r, ph, p) * (s[k] @ v[k, j] % p) % p
            for j in Q:
                F[g, k, j] = s[i] @ v[k, j] % p
    F[8] = np.eye(d, dtype=np.int64)
    F = F.reshape(9, 20, d, d)
    K = np.kron(3 * np.eye(4, dtype=np.int64) - 1, 4 * np.eye(5, dtype=np.int64) - 1)
    FD = np.einsum('xy,ayij->axij', K, F) % p
    return np.einsum('axij,bxjk->abik', F, FD) % p


def tangent(u, inside, pp, A, B, V, T, M):
    d = len(M[0][0])
    I = np.eye(d, dtype=object)
    Z = np.zeros_like(I)

    def actual(t):
        if inside and u == 3:
            return [full.scale((2, 0), M[0]), full.add_many([M[0], (t * I, Z)]), full.add_many([M[0], (-t * I, Z)]), *[full.scale((4, 0), m) for m in M[1:]]]
        return [full.add_many([full.scale((int(c), 0), m) for c, m in zip(row, M)]) for row in T]
    for p in (65521, 1009):
        G = gram(V, pp, A, B, actual(0), p)
        split = inside and u == 3
        if split:
            C = (gram(V, pp, A, B, actual(1), p) - G) % p
            assert np.array_equal((G + 4 * C) % p, gram(V, pp, A, B, actual(2), p))
        top = False
        common = []
        for i in range(16):
            rr = Random(i)
            J = np.array([[rr.randrange(-7, 8) for q in range(9)] for j in range(7)], np.int64)
            base = np.einsum('ia,abuv,jb->iujv', J, G, J).reshape(7 * d, 7 * d) % p
            if not split:
                if full.full_rank(base, p):
                    return True
            else:
                qu = np.einsum('ia,abuv,jb->iujv', J, C, J).reshape(7 * d, 7 * d) % p
                deg = 4 * d
                v = [full.determinant((base + t * qu) % p, p) for t in range(deg + 1)]
                poly = full.interpolate(v, p)
                if len(poly) == deg + 1:
                    top = True
                if poly:
                    common = full.poly_gcd(common, poly, p)
                if top and common == [1]:
                    return True
    return False


def finite(u, na, sh, o, inside):
    E, pp, A, B, V, T, forms, poly = build(u, na, sh, o, inside)
    n = len(T[0])
    d = n + 1
    if len(poly) < n - 1:
        return ('curve', len(poly))
    X, Y = raw_mac(n, d, poly)
    q = full.lift(X, Y, full.EXTENDED)
    if q is None:
        return ('no-lift', -1)
    K = q[0]
    while K and d >= 2:
        M, _ = full.multiplication(K, n, d)
        if M is not None:
            H = check_open(M, forms)
            if H is None:
                return ('excluded', len(K))
            N = full.compressed(M, H)
            if not N:
                return ('no-compression', -1)
            return ('gram' if tangent(u, inside, pp, A, B, V, T, N) else 'unresolved', len(N[0][0]))
        K, _ = full.shrink(K, n, d, forms)
        d -= 1
        if K is None:
            return ('no-compression', -1)
    return ('excluded' if not K else 'positive', len(K))


def scalar_polys(ws):
    den, xi = common_den(ws)
    xi, _ = primitive_common(xi)
    n = max(map(len, xi))
    return np.array([v + [0] * (n - len(v)) for v in xi], dtype=object)


def minors(u, na, V, pp, A, B, M):
    V = V.real.astype(int)
    tails = [*M, *V @ M, M[list(A)].sum(0)]
    S = V @ M
    for tag, i, k, *_ in pp:
        if tag == 'sign':
            tails.extend((S[i] + S[k], S[i] - S[k]))
    forms = [primitive(list(map(int, v))) for v in tails]
    if any((not ff for ff in forms)):
        return ('boundary', 0)
    m = M.shape[1] - 1
    gg = []
    common = []
    K = np.kron(3 * np.eye(4, dtype=int) - 1, 4 * np.eye(5, dtype=int) - 1).astype(object)

    def value(t):
        w = M @ np.array([t ** i for i in range(m + 1)], dtype=object)
        v = V * w[None, :]
        s = v.sum(1)
        F = np.zeros((9, 4, 5), dtype=object)
        for i in range(3):
            F[i, i] = v[i]
        F[3, 3, list(A)] = w[list(A)]
        F[4, 3, list(B)] = w[list(B)]
        for j, (tag, i, k, P, Q, o, c) in enumerate(pp, 5):
            if tag == 'sign':
                F[j, i] = -s[k] * v[k]
                F[j, k] = s[i] * v[i]
            elif tag == 'sparse':
                F[j, i, list(Q)] = s[k] * v[i, list(Q)]
                F[j, k, list(P)] = s[i] * v[k, list(P)]
            else:
                assert c in (0, 2)
                co = 1 if c == 0 else -1
                F[j, i, list(P)] = co * s[k] * v[k, list(P)]
                F[j, k, list(Q)] = s[i] * v[k, list(Q)]
        F[8] = 1
        X = F.reshape(9, 20)
        return X @ K @ X.T
    groups = ((1, 5, 1), (1, 4, 2), (1, 3, 3), (0, 5, 2), (0, 4, 3))
    for seed in range(3 * len(groups)):
        n0, n1, n2 = groups[seed % len(groups)]
        deg = 2 * m * (n1 + 2 * n2)
        gg.extend((value(t) for t in range(len(gg), deg + 1)))
        rr = Random(seed + 103)
        P = np.zeros((7, 9), dtype=object)
        if n0:
            P[0, 8] = 1
        P[n0:n0 + n1, :5] = [[rr.randrange(-7, 8) for j in range(5)] for i in range(n1)]
        P[n0 + n1:, 5:8] = [[rr.randrange(-7, 8) for j in range(3)] for i in range(n2)]
        pol = inter([idet((P @ G @ P.T).tolist()) for G in gg[:deg + 1]])
        h = remove(pol, forms)
        if h:
            common = gcdq(common, h)
        if common == [1]:
            return ('excluded', seed + 1)
    return ('residual', common)


def linear_solution(T, ys):
    d = full.det(T)
    n = len(T)
    assert d
    adj = [[(-1) ** (i + j) * full.det([[T[a][b] for b in range(n) if b != i] for a in range(n) if a != j]) for j in range(n)] for i in range(n)]
    assert np.array_equal(np.array(adj) @ np.array(T), d * np.eye(n, dtype=int))
    return [sum((a * y for a, y in zip(row, ys)), Rat(0)) / d for row in adj]


def pure_curves(V, pp, inside):
    V = V.real.astype(int)
    assert all((t == 'sparse' for t, *_ in pp[1:]))
    v = Rat([0, 1])
    t = 2 / v - v
    if inside:
        miss = next((i for i in range(5) if not V[2, i]))
        act = [0, *[j for j in range(2, 5) if j != miss]]
        coeff = [int(V[k, miss]) for k in range(2)]
    else:
        act = [2, 3, 4]
        coeff = [1, 1]
        miss = 0
    T = V[:, act].tolist()
    hs = {k: int(V[2, P[0]] * V[k, P[0]]) for tag, i, k, P, Q, o, c in pp if tag == 'sparse'}
    assert full.det(T)
    for sign in (0, 1):
        y = [hs[k] + coeff[k] * (v if k == 0 or not sign else -2 / v) for k in range(2)] + [Rat(1)]
        x = linear_solution(T, y)
        w = [Rat(0)] * 5
        for j, a in zip(act, x):
            w[j] = a
        if inside:
            w[1] = w[0] = w[0] / 2
            w[miss] = t
        else:
            w[0] = w[1] = t / 2
        yield scalar_polys(w)


def one_inside(V, pp):
    vr = V.real.astype(int)
    _, _, g, P, Q, _, _ = next((q for q in pp if q[0] == 'unicolor'))
    _, _, k, B, C, _, _ = next((q for q in pp if q[0] == 'sparse'))
    j, = P
    l, = Q
    ep = int(vr[g, j])
    eq = int(vr[g, l])
    f = int(vr[k, j]) * ep
    r = int(vr[k, l]) * eq
    h = int(vr[2, B[0]] * vr[k, B[0]])
    w = Rat([0, 1])
    d = next((j for j in range(2, 5) if vr[2, j]))
    if f == r:
        t = w / (2 - w * w)
        candidate = [(t, w)]
    else:
        t = w
        candidate = [(t, 1 / t), (t, -2 * t)]
    for t, v in candidate:
        y = h + f * v
        ms = [Rat(0)] * 5
        ms[0] = ms[1] = (1 + y) / 4
        ms[d] = int(vr[2, d]) * (1 - y) / 2
        ms[j] = ep * t
        ms[l] = eq * (1 / t - t)
        yield scalar_polys(ms)


def representations(inside, V, pp):
    vr = V.real.astype(int)
    I = np.eye(2, dtype=object)
    Z = np.zeros_like(I)
    p = np.array([[0, Fraction(1, 2)], [1, 0]], dtype=object)
    if inside:
        groups = [q for q in pp if q[0] == 'unicolor']
        assert len(groups) == 2
        _, _, g, P, Q, _, _ = groups[0]
        _, _, k, U, W, _, _ = groups[1]
        j, = P
        l, = Q
        t = Rat([0, 1])
        a = int(vr[g, j]) * t
        b = int(vr[g, l]) * (1 / t - t)
        M = {j: a, l: b}
        u = sum((int(vr[k, n]) * M[n] for n in U))
        v = sum((int(vr[k, n]) * M[n] for n in W))
        q = u * (u + v) - 1
        f = remove(squarefree(q.n), [[0, 1], a.n, b.n])
        assert f in ([1], [-1, 0, 2]), f
        if f == [1]:
            return None
        w = [Z.copy() for _ in range(5)]
        sl = [Z.copy() for _ in range(5)]
        d = next((j for j in range(2, 5) if vr[2, j]))
        w[j] = int(vr[g, j]) * p
        w[l] = int(vr[g, l]) * p
        w[d] = I
        sl[0] = sl[1] = I
        sl[d] = -2 * I
        return (w, sl, False)
    split = [v for v in pp if v[0] == 'sparse']
    s = [j for j in range(2, 5)]
    if split:
        _, _, k, B, C, _, _ = split[0]
        h = int(vr[2, B[0]] * vr[k, B[0]])
        z = quad(2 * h * p, -2 * I)
        I = duplicate(I)
        p = duplicate(p)
        Z = np.zeros_like(I)
        y = h * (z + I)
        agg = [(G, (I + sg * h * y) * Fraction(1, 2)) for G, sg in ((B, 1), (C, -1))]
    else:
        agg = [(tuple(s), I)]
    w = [p, p, *[Z.copy() for _ in range(3)]]
    sl = [Z.copy() for i in range(5)]
    repeated = None
    for G, S in agg:
        phase = int(vr[2, G[0]])
        assert all((vr[2, j] == phase for j in G))
        for j in G:
            w[j] = phase * S * Fraction(1, len(G))
        if len(G) >= 2:
            repeated = G
    assert repeated is not None
    sl[repeated[0]] = I
    sl[repeated[1]] = -I
    return (w, sl, True)


def check_pencil(V, pp, A, B, rep):
    if rep is None:
        return ('inconsistent', 0)
    w, sl, even = rep
    b = len(w[0])
    den = lcm(*(Fraction(v).denominator for a in [*w, *sl] for v in a.flat))
    vec = lambda a: np.vectorize(lambda x: int(x * den), otypes=[object])(a)
    w = list(map(vec, w))
    sl = list(map(vec, sl))
    zero = np.zeros_like(w[0])
    for p in (65521, 1009):

        def G(t):
            return gram(V, pp, A, B, [(a + t * b, zero) for a, b in zip(w, sl)], p, unit=True)
        base = G(0)
        gp = G(1)
        gm = G(-1)
        lin = (gp - gm) * pow(2, -1, p) % p
        qu = ((gp + gm) * pow(2, -1, p) - base) % p
        assert np.array_equal((base + 2 * lin + 4 * qu) % p, G(2))
        if even:
            assert not np.any(lin)
        common = []
        maxdeg = -1
        fullD = False
        for seed in range(18):
            rr = Random(seed)
            U = np.array([[rr.randrange(-7, 8) for j in range(9)] for i in range(7)], dtype=np.int64)
            g, l, q = [np.einsum('ia,abuv,jb->iujv', U, h, U).reshape(7 * b, 7 * b) % p for h in (base, lin, qu)]
            deg = (2 if even else 6) * b
            vals = [full.determinant((g + i * q if even else g + i * l + i * i * q) % p, p) for i in range(deg + 1)]
            f = full.interpolate(vals, p)
            maxdeg = max(maxdeg, len(f) - 1)
            fullD |= len(f) == deg + 1
            if f:
                common = full.poly_gcd(common, f, p)
            if fullD and common == [1]:
                return ('pencil', b)
    return ('residual', (b, maxdeg, common))



def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--support', choices=(3,4), type=int)
    parser.add_argument('--part', choices=('all','profiles','finite','curves'), default='all')
    parser.add_argument('--shard', nargs=2, type=int, metavar=('INDEX','COUNT'), default=(0,1))
    args = parser.parse_args()
    index, shards = args.shard
    assert 0 <= index < shards
    counts = Counter()
    checks = Counter()
    retained = 0
    for inside in (False, True):
        for u, na, shape, o, E, pairs, A, B in iter_all(inside):
            support = sum(s!=-1 for e,s in shape)
            if support not in (3,4) or args.support and support != args.support:
                continue
            F,V = constraints(E,pairs,A,B)
            if not passes(F):
                continue
            counts[inside,support] += 1
            serial = retained
            retained += 1
            if args.part=='profiles' or serial%shards!=index:
                continue
            n = 6-u if inside else 4
            curves = sum(pair[0]!='sign' for pair in pairs)<n-1
            if not curves:
                if args.part in ('all','finite'):
                    tag, size = finite(u,na,shape,o,inside)
                    assert tag in ('gram','excluded'), (shape,o,tag,size)
                    checks[support,tag] += 1
                continue
            if args.part not in ('all','curves'):
                continue
            assert u==2 and pairs[0][0]=='sign'
            common = sum(pair[0]=='unicolor' for pair in pairs)
            if common==0:
                outcomes = [minors(u,na,V,pairs,A,B,M) for M in pure_curves(V,pairs,inside)]
            elif common==1 and inside:
                outcomes = [minors(u,na,V,pairs,A,B,M) for M in one_inside(V,pairs)]
            else:
                outcomes = [check_pencil(V,pairs,A,B,representations(inside,V,pairs))]
            for tag, info in outcomes:
                assert tag in ('boundary','excluded','inconsistent','pencil'),(shape,o,tag,info)
                checks[support,'curve '+tag] += 1
    expected = {(False,3):62,(True,3):98,(True,4):72}
    if args.support:
        expected = {k:v for k,v in expected.items() if k[1]==args.support}
    assert counts==expected, counts
    if args.part=='all' and shards==1:
        actual = {(3,'gram'):90,(3,'excluded'):29,(3,'curve excluded'):38,(3,'curve boundary'):10,
                  (3,'curve pencil'):12,(3,'curve inconsistent'):1,
                  (4,'gram'):48,(4,'curve excluded'):36,(4,'curve boundary'):12}
        if args.support:
            actual = {k:v for k,v in actual.items() if k[0]==args.support}
        assert checks==actual, checks
    print('Retained mixed-row orientations',retained,'checks',dict(checks), flush=True)

if __name__ == '__main__':
    main()
