"""Verify the support-two case of the complex 4 by 5 permanent row obstruction.

The shared arithmetic and sparse/high phase enumeration are in the two sibling
modules. All integer polynomial data and every orientation are generated locally.
"""

import argparse
from collections import Counter
from fractions import Fraction
from functools import lru_cache, reduce
from itertools import combinations, product
from math import factorial, gcd, isqrt, lcm
from random import Random

import numpy as np

import verify_full_rows as full
import verify_sparse_rows as sparse
from verify_sparse_rows import (
    Rat, check_open, divexact, gram, idet, inter, model, multiply, plus,
    primitive, quotient, remove, trim,
)



@lru_cache(None)
def prime_at(i):
    """Select distinct primes deterministically for exact rational polynomial gcd certificates."""
    p = 1000000007 if not i else prime_at(i - 1) - 2
    while any((p % k == 0 for k in range(3, isqrt(p) + 1, 2))):
        p -= 2
    return p


def gcdmod(f, g, p):
    """Compute the monic gcd in a prime polynomial ring."""
    f = trim([x % p for x in f])
    g = trim([x % p for x in g])
    while g:
        k = pow(g[-1], -1, p)
        while len(f) >= len(g):
            j = len(f) - len(g)
            h = k * f[-1] % p
            for (z, x) in enumerate(g):
                f[j + z] = (f[j + z] - h * x) % p
            while f and f[-1] == 0:
                f.pop()
        (f, g) = (g, f)
    if not f:
        return []
    k = pow(f[-1], -1, p)
    return [v * k % p for v in f]


def divides(f, g):
    """Check divisibility by an integer polynomial using exact coefficient cancellation."""
    r = f.copy()
    while len(r) >= len(g):
        (q, remainder) = divmod(r[-1], g[-1])
        j = len(r) - len(g)
        if remainder:
            return False
        for (t, v) in enumerate(g):
            r[j + t] -= q * v
        while r and (not r[-1]):
            r.pop()
    return not r


def gcdq(f, g):
    """Lift modular gcds, then certify exact divisibility and the matching degree upper bound."""
    f = primitive(f)
    g = primitive(g)
    if not f or not g:
        return f or g
    if len(f) == 1 or len(g) == 1:
        return [1]
    L = gcd(f[-1], g[-1])
    res = []
    mod = 1
    degree = 1 + max(len(f), len(g))
    i = 0
    while True:
        p = prime_at(i)
        i += 1
        if f[-1] % p == 0 or g[-1] % p == 0:
            continue
        h = gcdmod(f, g, p)
        if len(h) == 1:
            return [1]
        if len(h) > degree:
            continue
        if len(h) < degree:
            mod = 1
            res = [0] * len(h)
            degree = len(h)
        inv = pow(mod, -1, p)
        res = [x + mod * ((y * L - x) * inv % p) for (x, y) in zip(res, h)]
        mod *= p
        candidate = primitive([x if 2 * x < mod else x - mod for x in res])
        if len(candidate) == degree and divides(f, candidate) and divides(g, candidate):
            return candidate


def sumrat(ws, signs, indices):
    return sum((int(signs[k]) * ws[k] for k in indices), Rat(0))


def section(V, A, par):
    """Solve the first common-ratio conic for the three missing coordinates over the total parameter."""
    (_, i, k, P, Q, _) = A
    R = tuple((j for j in (2, 3, 4) if j not in (*P, *Q)))
    if R:
        a = Q[0]
        b = R[0]
    else:
        a = P[0]
        b = Q[0]
    free = next((j for j in (2, 3, 4) if j != a and j != b))
    coeff = list(map(int, V[k]))
    l = [Rat(coeff[j]) for j in range(5)]
    m = [coeff[j] * par if j in P else Rat(-coeff[j] if j in R else 0) for j in range(5)]
    d = l[a] * m[b] - l[b] * m[a]

    def at(v):
        X = par - l[free] * v
        Y = 1 - m[free] * v
        w = [Rat(0)] * 5
        w[a] = (X * m[b] - l[b] * Y) / d
        w[b] = (l[a] * Y - X * m[a]) / d
        w[free] = Rat(v)
        return w
    c = at(0)
    v = at(1)
    lin = [b - a for (a, b) in zip(c, v)]
    return (c, lin, d)


def conic(data, second, V):
    """Substitute the first conic section into a second common-ratio pair equation."""
    (c, w, d) = data
    (_, i, k, P, Q, _) = second
    R = [j for j in (2, 3, 4) if j not in (*P, *Q)]
    s = V[k]
    L = sumrat(c, s, (2, 3, 4))
    M = sumrat(w, s, (2, 3, 4))
    u = sumrat(c, s, P)
    v = sumrat(w, s, P)
    r = sumrat(c, s, R)
    q = sumrat(w, s, R)
    return [u * L - 1 - r, u * M + v * L - q, v * M]


def equation(V, pp):
    """Choose a section exhibiting a lower degree or a split quadratic when available."""
    V = V.real.astype(int)
    A = [p for p in pp if p[0] == 'unicolor']
    assert len(A) == 2
    t = Rat([0, 1])
    opt = []
    for (a, b) in (A, A[::-1]):
        rep = section(V, a, t)
        eq = conic(rep, b, V)
        degree = next((i for i in (2, 1, 0) if eq[i].n), -1)
        if degree == 2:
            di = eq[1] * eq[1] - 4 * eq[0] * eq[2]
            sq = None if not di.n else polysquare(di.n)
            sd = polysquare(di.d)
            issq = (not di.n or sq is not None) and sd is not None
        else:
            issq = False
        opt.append((degree, 0 if issq else 1, rep, eq, a, b))
    return min(opt, key=lambda z: z[:2])


def polysquare(p):
    """Return an exact integer polynomial square root, if one exists."""
    p = trim(p)
    if not p:
        return []
    if (len(p) - 1) % 2 or p[-1] < 0:
        return None
    from math import isqrt
    h = (len(p) - 1) // 2
    top = isqrt(p[-1])
    if top * top != p[-1]:
        return None
    f = [Fraction(0)] * (h + 1)
    f[h] = Fraction(top)
    for i in range(h - 1, -1, -1):
        k = h + i
        old = sum((f[j] * f[k - j] for j in range(i + 1, h + 1) if 0 <= k - j <= h))
        f[i] = (p[k] - old) / (2 * top)
    if any((v.denominator != 1 for v in f)):
        return None
    f = [int(v) for v in f]
    return f if multiply(f, f) == p else None


def mulint(a, k):
    return trim([k * x for x in a])


def times(*xs):
    return reduce(multiply, xs, [1])


def primitive_common(rows):
    g = reduce(gcdq, rows, [])
    rr = [divexact(r, g) for r in rows] if g else rows
    den = reduce(gcd, (x for r in rr for x in r), 0) or 1
    return ([[x // den for x in r] for r in rr], g)


def common_den(rats):
    """Clear the coefficients of several rational functions by a common integer polynomial."""
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


def tower_charts(V, pp):
    """Build integral monic quadratic algebras for the second and third row equations."""
    (deg, ns, rep, eq, A, B) = equation(V, pp)
    (D, rs) = common_den(eq)
    (rs, content) = primitive_common(rs)
    while rs and (not rs[-1]):
        rs.pop()
    if len(rs) <= 1:
        return ([], content, rs[0] if rs else [])
    lead = rs[-1]
    V = V.real.astype(int)
    (_, _, kk, bb, cc, _) = next((p for p in pp if p[0] == 'sparse'))
    hh = int(V[3, bb[0]] * V[kk, bb[0]])
    profiles = []
    if len(rs) == 2:
        profiles.append((Rat(mulint(rs[0], -1), rs[1]), Rat(0), None))
    else:
        (g0, g1, g2) = rs
        disc = plus(times(g1, g1), mulint(times(g0, g2), -4))
        rt = polysquare(disc)
        if rt is None:
            profiles.append((Rat(0), Rat(1, g2), (g1, times(g2, g0))))
        else:
            for sg in (1, -1) if rt else (1,):
                profiles.append((Rat(plus(mulint(g1, -1), mulint(rt, sg)), mulint(g2, 2)), Rat(0), None))
    (C, L, _) = rep
    charts = []
    for (v0, v1, first) in profiles:
        coords = [v for j in range(2, 5) for v in (C[j] + L[j] * v0, L[j] * v1)]
        (den, num) = common_den(coords)

        def weighted(h):
            return reduce(plus, (mulint(num[2 * j + h], int(V[kk, 2 + j]) * hh) for j in range(3)), [])
        sec = (weighted(0), weighted(1), mulint(times(den, den), -2))
        w = [(mulint(den, 1 + hh), [], [hh], []), (mulint(den, int(V[3, 1]) * (1 - hh)), [], [-int(V[3, 1]) * hh], [])]
        w += [(mulint(num[2 * j], 2), mulint(num[2 * j + 1], 2), [], []) for j in range(3)]
        if first is None:
            disc = plus(times(sec[0], sec[0]), mulint(sec[2], -4))
            rt = polysquare(disc)
            if rt is not None:
                for sg in (1, -1) if rt else (1,):
                    c = plus(mulint(sec[0], -1), mulint(rt, sg))
                    ww = [(plus(mulint(a, 2), multiply(y, c)), [], [], []) for (a, b, y, z) in w]
                    charts.append((None, None, ww))
                continue
        charts.append((first, sec, w))
    return (charts, content, lead)


def evalp(a, t):
    v = 0
    for c in reversed(a):
        v = v * t + c
    return v


def ring(first, second, t):
    """Evaluate the quadratic multiplication and relative norms at an integer parameter."""
    if first is None:
        zz = 0
        unit = 1
        add = lambda a, b: a + b
        sc = lambda a, s: a * s
        mul = lambda a, b: a * b
        norm = lambda a: a
    else:
        (g, f) = (evalp(z, t) for z in first)
        zz = (0, 0)
        unit = (1, 0)
        add = lambda a, b: (a[0] + b[0], a[1] + b[1])
        sc = lambda a, s: (a[0] * s, a[1] * s)

        def mul(a, b):
            q = a[1] * b[1]
            return (a[0] * b[0] - f * q, a[0] * b[1] + a[1] * b[0] - g * q)

        def norm(a):
            return a[0] * (a[0] - g * a[1]) + f * a[1] ** 2
    if second is None:
        return (add, sc, mul, norm, unit, zz)
    (s0, s1, f2) = (evalp(z, t) for z in second)
    seq = s0 if first is None else (s0, s1)

    def plus2(a, b):
        return (add(a[0], b[0]), add(a[1], b[1]))

    def sc2(a, k):
        return (sc(a[0], k), sc(a[1], k))

    def mul2(a, b):
        q = mul(a[1], b[1])
        ac = mul(a[0], b[0])
        mix = mul(add(a[0], a[1]), add(b[0], b[1]))
        return (add(ac, sc(q, -f2)), add(add(mix, sc(ac, -1)), add(sc(q, -1), sc(mul(q, seq), -1))))

    def norm2(a):
        return norm(add(mul(a[0], add(a[0], sc(mul(seq, a[1]), -1))), sc(mul(a[1], a[1]), f2)))
    return (plus2, sc2, mul2, norm2, (unit, zz), (zz, zz))


def ring_weight(w, f, s, t):
    (a, b, c, d) = (evalp(z, t) for z in w)
    if f is None:
        return a if s is None else (a, c)
    return ((a, b), (c, d)) if s is not None else (a, b)


def bound_chart(chart):
    """Bound the magnitudes of the five weight functions on all sheets over the unit circle."""
    (f, s, w) = chart
    l1 = lambda a: sum(map(abs, a))
    U = 1 + max(map(l1, f)) if f else 1
    V = 1 + max(l1(s[0]) + U * l1(s[1]), l1(s[2])) if s else 1
    W = max((l1(a) + U * l1(b) + V * l1(c) + U * V * l1(d) for (a, b, c, d) in w))
    return max(1, W)


def norm_projected(chart, V, pp, P, t):
    """Evaluate the exact integral norm of a projected seven-dimensional determinant."""
    (first, second, weights) = chart
    (add, sc, mul, norm, one, zero) = ring(first, second, t)
    ws = [ring_weight(w, first, second, t) for w in weights]
    v = [[sc(x, int(c)) for (x, c) in zip(ws, row)] for row in V]

    def sm(z):
        return reduce(add, z, zero)
    sums = list(map(sm, v))
    F = [[zero] * 20 for _ in range(11)]
    for i in range(4):
        for j in range(5):
            F[i][5 * i + j] = v[i][j]
    for (q, (tag, i, k, B, C, ori)) in enumerate(pp, 4):
        if tag == 'sign':
            for j in range(5):
                F[q][i * 5 + j] = sc(mul(sums[k], v[k][j]), -1)
                F[q][k * 5 + j] = mul(sums[i], v[i][j])
        elif tag == 'sparse':
            for j in C:
                F[q][i * 5 + j] = mul(sums[k], v[i][j])
            for j in B:
                F[q][k * 5 + j] = mul(sums[i], v[k][j])
        else:
            for j in B:
                F[q][i * 5 + j] = mul(sums[k], v[k][j])
            for j in C:
                F[q][k * 5 + j] = mul(sums[i], v[k][j])
    F[10] = [one] * 20
    Z = [[sm((sc(row[j], v) for (v, row) in zip(proj, F) if v)) for j in range(20)] for proj in P]
    U = []
    for rr in Z:
        rs = [sm(rr[5 * i:5 * i + 5]) for i in range(4)]
        cs = [sm(rr[j::5]) for j in range(5)]
        s = sm(rs)
        U.append([sm((sc(x, 12), sc(rs[j // 5], -3), sc(cs[j % 5], -4), s)) for (j, x) in enumerate(rr)])
    GG = [[zero] * 7 for i in range(7)]
    for i in range(7):
        for j in range(i + 1):
            GG[i][j] = GG[j][i] = sm((mul(a, b) for (a, b) in zip(Z[i], U[j]) if a != zero and b != zero))
    layer = {0: one}
    for i in range(7):
        nxt = {}
        for (mask, h) in layer.items():
            for (j, entry) in enumerate(GG[i]):
                if mask >> j & 1 or entry == zero:
                    continue
                q = mask | 1 << j
                term = mul(h, entry)
                if (mask >> j + 1).bit_count() % 2:
                    term = sc(term, -1)
                nxt[q] = add(nxt.get(q, zero), term)
        layer = nxt
    return norm(layer.get(127, zero))


def projection(seed):
    rules = ((1, 4, 2), (1, 3, 3), (0, 4, 3), (1, 2, 4), (0, 3, 4), (1, 1, 5))
    (a, b, c) = rules[seed % len(rules)]
    rng = Random(103 + seed)
    P = [[0] * 11 for i in range(7)]
    if a:
        P[0][10] = 1
    for row in P[a:a + b]:
        row[:4] = [rng.randrange(-7, 8) for j in range(4)]
    for row in P[a + b:]:
        row[4:10] = [rng.randrange(-7, 8) for j in range(6)]
    return (P, b, c)


def norm_poly(ch, V, pp, seed):
    """Recover every coefficient by a single balanced integer evaluation with a Cauchy bound."""
    (P, b, c) = projection(seed)
    W = bound_chart(ch)
    sheets = 2 ** sum((x is not None for x in ch[:2]))
    bound = (factorial(7) * (20 ** 2 * 6 * 77 ** 2) ** 7 * 5 ** (2 * c) * W ** (2 * (b + 2 * c))) ** sheets
    bits = bound.bit_length() + 2
    value = norm_projected(ch, V.real.astype(int).tolist(), pp, P, 1 << bits)
    coeff = []
    base = 1 << bits
    half = base // 2
    while value:
        (q, r) = divmod(value + half, base)
        r -= half
        assert abs(r) <= bound
        coeff.append(r)
        value = q
    return primitive(coeff)


def squarefree(p):
    p = primitive(p)
    if len(p) <= 1:
        return p
    derivative = [j * x for (j, x) in enumerate(p) if j]
    return quotient(p, gcdq(p, derivative))


def lcmq(a, b):
    assert a and b
    return primitive(multiply(quotient(a, gcdq(a, b)), b))


def required(V, pp, weights):
    out = list(weights)
    V = V.real.astype(int)

    def combo(row):
        return [reduce(plus, (mulint(w[j], int(x)) for (x, w) in zip(row, weights)), []) for j in range(4)]
    out.extend((combo(row) for row in V))
    for (tag, i, k, *_) in pp:
        if tag == 'sign':
            out.extend((combo(V[i] + V[k]), combo(V[i] - V[k])))
    return out


def norm_roots(ch, V, pp):
    """Find a necessary square-free polynomial in the parameter for an individual branch."""
    if any((not any(w) for w in required(V, pp, ch[-1]))):
        return ([1], 'boundary')
    q = []
    for i in range(6):
        f = norm_poly(ch, V, pp, i)
        if f:
            old = q
            q = gcdq(q, squarefree(f))
            if len(q) == 1 or old == q or i >= 2:
                break
    return (q, 'finite' if q else 'zero_norm')


def eq_case(ind, V, pp):
    """Collect all possible parameter values, including denominators, leading coefficients and content."""
    (ch, co, ld) = tower_charts(V, pp)
    avoid = [0, 1]
    ans = lcmq(avoid, squarefree(co) or [1])
    ans = lcmq(ans, squarefree(ld) or [1])
    for c in ch:
        (q, tag) = norm_roots(c, V, pp)
        if not q:
            return (None, tag)
        ans = lcmq(ans, q)
    return (ans, 'complete')


def polydiv(a, b):
    a = trim(a)
    b = trim(b)
    q = [0] * max(0, len(a) - len(b) + 1)
    while len(a) >= len(b):
        k = len(a) - len(b)
        v = Fraction(a[-1], b[-1])
        q[k] = v
        a = plus(a, [0] * k + [-v * t for t in b])
    return (trim(q), a)


def invmod(a, mod):
    x = mod
    y = polydiv(a, mod)[1]
    u = []
    v = [1]
    while y:
        (q, r) = polydiv(x, y)
        (x, y) = (y, r)
        (u, v) = (v, plus(u, [-z for z in multiply(q, v)]))
    assert len(x) == 1
    return [Fraction(t, x[0]) for t in polydiv(u, mod)[1]]


def comp(g):
    n = len(g) - 1
    A = np.zeros((n, n), dtype=object)
    for i in range(1, n):
        A[i, i - 1] = 1
    A[:, -1] = [Fraction(-v, g[-1]) for v in g[:-1]]
    return A


def polmat(a, T):
    I = np.eye(len(T), dtype=object)
    v = np.zeros_like(T)
    for k in reversed(a):
        v = v @ T + k * I
    return v


def rmat(R, T, g):
    inv = invmod(R.d, g)
    return polmat(polydiv(multiply(R.n, inv), g)[1], T)


def duplicate(a):
    if isinstance(a, list):
        return [duplicate(v) for v in a]
    z = np.zeros_like(a)
    return np.block([[a, z], [z, a]])


def quad(P, Q):
    I = np.eye(len(P), dtype=object)
    Z = np.zeros_like(P)
    return np.block([[Z, -Q], [I, -P]])


def rational_mats(ws):
    den = lcm(*(Fraction(z).denominator for w in ws for z in w.flat))
    M = []
    for w in ws:
        a = np.array([int(x * den) for x in w.flat], dtype=object).reshape(w.shape)
        M.append((a, np.zeros_like(a)))
    return M


def check_matrix(V, pp, W):
    """Restrict the exact coordinate algebra to the open factors and certify the Gram rank."""
    M = rational_mats(W)
    vr = V.real.astype(int)
    n = len(M[0][0])
    forms = []

    def cc(row):
        return [(int(v), 0) for v in row]
    forms.extend((cc(r) for r in np.eye(5, dtype=int)))
    forms.extend((cc(r) for r in vr))
    for (tag, i, k, B, C, o) in pp:
        if tag == 'sign':
            forms.extend((cc(vr[i] + vr[k]), cc(vr[i] - vr[k])))
    H = check_open(M, forms)
    if H is None:
        return ('empty', n)
    N = full.compressed(M, H)
    if not N:
        return ('no-compression', n)
    d = len(N[0][0])
    for p in (65521, 1009, 241):
        G = gram(V, pp, N, p)
        for seed in range(16):
            r = Random(seed)
            A = np.array([[r.randrange(-7, 8) for j in range(11)] for i in range(7)], dtype=np.int64)
            sm = np.einsum('ia,abuv,jb->iujv', A, G, A).reshape(7 * d, 7 * d) % p
            if full.full_rank(sm, p):
                return ('gram', d)
    return ('unresolved', d)


def refine(q, h):
    g = gcdq(q, h)
    return (g, quotient(q, g))


def fibre(V, pp, q):
    """Split the parameter polynomial by each possible specialized conic degree and check finite fibers."""
    (degree, ns, rep, eq, A, B) = equation(V, pp)
    (C, L, d) = rep
    R = [j for j in (2, 3, 4) if j not in (*A[3], *A[4])]
    q = remove(q, [[1, 1]] + ([[0, 1]] if not R else []))
    if len(q) <= 1:
        return []
    (den, rs) = common_den(eq)
    assert len(gcdq(q, den)) == 1
    cond = q
    out = []
    vv = V.real.astype(int)
    (_, _, high, K, _, _) = next((p for p in pp if p[0] == 'sparse'))
    hh = int(vv[3, K[0]] * vv[high, K[0]])
    for deg in (2, 1, 0):
        (zero, nonzero) = refine(cond, rs[deg])
        cond = zero
        if len(nonzero) <= 1:
            continue
        if deg == 0:
            out.append(('inconsistent', len(nonzero) - 1))
            continue
        g = nonzero
        T = comp(g)
        nc = len(T)
        co = [rmat(r, T, g) for r in C]
        li = [rmat(r, T, g) for r in L]
        inv = invmod(rs[deg], g)
        if deg == 1:
            v = polmat(polydiv(multiply([-x for x in rs[0]], inv), g)[1], T)
        else:
            v = quad(polmat(polydiv(multiply(rs[1], inv), g)[1], T), polmat(polydiv(multiply(rs[0], inv), g)[1], T))
            co = duplicate(co)
            li = duplicate(li)
        missing = [a + b @ v for (a, b) in zip(co[2:], li[2:])]
        I = np.eye(len(v), dtype=object)
        total = sum((int(c) * m for (c, m) in zip(vv[high, 2:], missing)), np.zeros_like(I))
        Z = quad(hh * total, -2 * I)
        I = duplicate(I)
        split = hh * (Z + I)
        weights = [(I + split) * Fraction(1, 2), int(vv[3, 1]) * (I - split) * Fraction(1, 2), *duplicate(missing)]
        out.append(check_matrix(V, pp, weights))
    if len(cond) > 1:
        out.append(('vertical', tuple(cond)))
    return out


def scalar_component(frac, g):
    vals = polydiv(multiply(frac.n, invmod(frac.d, g)), g)[1]
    return [Fraction(x) for x in vals] + [Fraction(0)] * (2 - len(vals))


def vertical_chart(V, pp, g):
    """At a vertical component, use its free missing coordinate as the univariate parameter."""
    dg = len(g) - 1
    assert dg in (1, 2) and g[-1] == 1
    (_, _, rep, eq, A, B) = equation(V, pp)
    (C, L, _) = rep
    d = next((p for p in pp if p[0] == 'sparse'))
    (_, _, high, bb, _, _) = d
    vr = V.real.astype(int)
    h = int(vr[3, bb[0]] * vr[high, bb[0]])
    sg = int(vr[3, 1])
    coeff = [(scalar_component(C[j], g), scalar_component(L[j], g)) for j in range(2, 5)]
    den = lcm(*(x.denominator for pair in coeff for v in pair for x in v))
    al = [[trim([int(a[k] * den), int(b[k] * den)]) for k in range(2)] for (a, b) in coeff]
    (t0, t1) = [reduce(plus, (mulint(ab[k], h * int(vr[high, j + 2])) for (j, ab) in enumerate(al)), []) for k in range(2)]
    first = ([g[1]], [g[0]]) if dg == 2 else None
    second = (t0, t1, [-2 * den * den])
    W = [([den * (1 + h)], [], [h], []), ([sg * (1 - h) * den], [], [-sg * h], []), *((mulint(a, 2), mulint(b, 2), [], []) for (a, b) in al)]
    return (first, second, W, den, al)


def vertical_finite(V, pp, g, q):
    """At a residual root, construct the algebra of both parameters and the final quadratic root."""
    vr = V.real.astype(int)
    T = comp(g)
    P = comp(q)
    nt = len(T)
    np_ = len(P)
    (_, _, rep, _, _, _) = equation(V, pp)
    (C, L, _) = rep
    W = [np.kron(rmat(C[j], T, g), np.eye(np_, dtype=object)) + np.kron(rmat(L[j], T, g), P) for j in range(2, 5)]
    (_, _, high, bb, _, _) = next((z for z in pp if z[0] == 'sparse'))
    h = int(vr[3, bb[0]] * vr[high, bb[0]])
    eye = np.eye(nt * np_, dtype=object)
    tb = sum((int(vr[high, j + 2]) * v for (j, v) in enumerate(W)), np.zeros_like(eye))
    Z = quad(h * tb, -2 * eye)
    E = duplicate(eye)
    y = h * (Z + E)
    masses = [(E + y) * Fraction(1, 2), int(vr[3, 1]) * (E - y) * Fraction(1, 2), *duplicate(W)]
    return check_matrix(V, pp, masses)


def vertical(V, pp, g):
    (first, second, W, _, _) = vertical_chart(V, pp, g)
    (z, tag) = norm_roots((first, second, W), V, pp)
    if not z:
        return (tag, None)
    if len(z) == 1:
        return ('curve-empty', 0)
    return vertical_finite(V, pp, g, z)


def rational_pos(V, pp):
    """Recover all missing weights on the exceptional two-dimensional profiles as functions of one parameter."""
    V = V.real.astype(int)
    t = Rat([0, 1])
    (A, B, C) = [z for z in pp if z[0] == 'unicolor']
    rep = section(V, A, t)
    b = conic(rep, B, V)
    c = conic(rep, C, V)
    ds = [x - y for (x, y) in zip(b, c)]
    assert not ds[2].n and ds[1].n
    assert gcdq(ds[0].n, ds[1].n) == [1]
    v = -ds[0] / ds[1]
    assert all((eq[0] + eq[1] * v + eq[2] * v * v == 0 for eq in (b, c)))
    (const, lin, _) = rep
    ws = [Rat(1, 2), Rat(1, 2), *(a + b * v for (a, b) in zip(const[2:], lin[2:]))]
    (den, num) = common_den(ws)
    (G, _) = primitive_common(num)
    D = max(map(len, G))
    return (np.array([a + [0] * (D - len(a)) for a in G], dtype=object), v, ds)


def fixed_siding(V, pp, M):
    """Use seven covectors symmetric on the duplicated active columns to test every split simultaneously."""
    vr = V.real.astype(int)
    m = M.shape[1] - 1
    K = np.kron(3 * np.eye(4, dtype=int) - 1, 4 * np.eye(5, dtype=int) - 1).astype(object)
    rows = []
    for t in range(26 * m + 1):
        w = M @ np.array([t ** j for j in range(m + 1)], dtype=object)
        v = vr * w[None, :]
        s = v.sum(1)
        F = np.zeros((7, 4, 5), dtype=object)
        H = np.zeros((11, 4, 5), dtype=object)
        for j in range(4):
            H[j, j] = v[j]
        for (j, (tag, i, k, B, C, o)) in enumerate(pp):
            if tag == 'sign':
                F[j, i] = s[k] * (v[i] - v[k])
                F[j, k] = s[i] * (v[i] - v[k])
                H[j + 4, i] = -s[k] * v[k]
                H[j + 4, k] = s[i] * v[i]
            else:
                F[j, i, list(B)] = s[k] * v[k, list(B)]
                F[j, k, list(C)] = s[i] * v[k, list(C)]
                H[j + 4] = F[j]
        F[-1] = 1
        H[-1] = 1
        rows.append(F.reshape(7, 20) @ K @ H.reshape(11, 20).T)
    gr = m * 12
    degrees = (1, 1, 1, 1, 2, 2, 2, 2, 2, 2, 0)
    common = []
    for cols in combinations(range(11), 7):
        d = gr + m * sum((degrees[i] for i in cols))
        pol = inter([idet(a[:, cols].tolist()) for a in rows[:d + 1]])
        if pol:
            common = gcdq(common, squarefree(pol))
        if len(common) == 1:
            break
    forms = [*M[2:], *vr @ M]
    ss = vr @ M
    for (tag, i, k, *_) in pp:
        if tag == 'sign':
            forms.extend((ss[i] + ss[k], ss[i] - ss[k]))
    return remove(common, [primitive(list(z)) for z in forms])



def verify_curve(V, pairs):
    polynomial, status = eq_case(0, V, pairs)
    assert polynomial and status == 'complete'
    result = Counter()
    for tag, info in fibre(V, pairs, polynomial):
        if tag == 'vertical':
            verdict, size = vertical(V, pairs, list(info))
            assert verdict in ('empty', 'gram', 'curve-empty'), (verdict, size)
            result['vertical components'] += 1
        else:
            assert tag in ('inconsistent', 'empty', 'gram'), (tag, info)
            result[tag] += 1
    return result


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--part', choices=('all','profiles','finite','curves'), default='all')
    parser.add_argument('--shard', nargs=2, type=int, metavar=('INDEX','COUNT'), default=(0,1))
    args = parser.parse_args()
    index, number = args.shard
    assert 0 <= index < number
    raw = kept = curve_count = completed = 0
    stats = Counter()
    for shape in sparse.shapes(2):
        val = sparse.options(2, shape)
        if val is None:
            continue
        E, choices = val
        for pairs in product(*choices):
            raw += 1
            if args.part == 'curves' and any(p[0] == 'three' for p in pairs):
                continue
            F,V = sparse.physical_rows(E,pairs)
            if not sparse.passes(F):
                continue
            ordinal = kept
            kept += 1
            if args.part == 'profiles' or ordinal % number != index:
                continue
            geometry = E,pairs
            _, group, _, _, _, _, _, polys = model(shape,0,geometry)
            if len(polys) < len(group)-1:
                curve_count += 1
                if args.part in ('all','curves'):
                    assert len(group)==5 and sum(p[0]=='unicolor' for p in pairs)==2
                    stats.update(verify_curve(V,pairs))
                    stats['curve orientations'] += 1
                continue
            if args.part not in ('all','finite'):
                continue
            status, size = sparse.check(shape,0,geometry)
            if status == 'positive':
                assert len(group)==4 and sum(p[0]=='unicolor' for p in pairs)==3
                weights, _, _ = rational_pos(V,pairs)
                assert fixed_siding(V,pairs,weights)==[1]
                status='split-independent minors'
            assert status in ('excluded','tangent','split-independent minors'), (shape,pairs,status,size)
            stats[status] += 1
            completed += 1
            if completed % 1000 == 0:
                print('Finite orientations checked:',completed,flush=True)
    assert raw==667352
    assert kept == (1864 if args.part=='curves' else 97472)
    if number==1 and args.part in ('all','finite'):
        assert completed==96752
    if number==1 and args.part in ('all','curves'):
        assert curve_count==720 and stats['vertical components']==60
    print('Support-two orientations', kept, dict(stats), flush=True)

if __name__ == '__main__':
    main()
