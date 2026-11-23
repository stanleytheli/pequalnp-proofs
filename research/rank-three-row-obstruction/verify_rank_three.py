"""Verify the complex rank-three row obstruction on the 4 by 5 permanent level.

Run with Python assertions enabled. The sibling verify_full_rows.py supplies
the shared rational, Gaussian-integer, and finite-field arithmetic routines.
Every geometric profile and Gram minor is regenerated from its defining formula.
Selected row numbers in the four all-sign cases are verifiable acceleration hints.
"""

import argparse
from collections import Counter
from functools import lru_cache, reduce
from itertools import combinations, combinations_with_replacement, permutations, product
from math import factorial, gcd, isqrt, lcm
from random import Random

import numpy as np

from verify_full_rows import (
    EXTENDED, G, add_many, arraydet, compressed, contractions, det, determinant,
    exact_rank, exponents, field, fraction, full_rank, get_kernel, interpolate,
    lift, monomials, mul, mult, multiplication, nonzero, normalize, poly_gcd,
    restricted_Q, rref, scale, shrink, sqrt_i,
)


def fields(u, free, orient):
    """Recover the three high-row phases and the oriented pair groups."""
    shape = (0,) * u + free
    E = [[0] * 5, [x // 4 for x in shape], [x % 4 for x in shape]]
    pairs = []
    sign = []
    seq = 0
    for i in range(3):
        for k in range(i):
            r = [(x - y) % 4 for (x, y) in zip(E[i], E[k])]
            vals = set(r)
            if vals == {0, 2}:
                sign.append((i, k))
                continue
            if len(vals) != 3:
                return None
            center = next((v for v in vals if (v + 2) % 4 not in vals))
            gamma = 1 if not orient >> seq & 1 else 3
            seq += 1
            b = [v if f == (center + gamma) % 4 else -1 for (v, f) in zip(E[k], r)]
            c = [v if f == (center - gamma) % 4 else -1 for (v, f) in zip(E[k], r)]
            pairs.append((i, k, b, c))
    return (E, pairs, sign)

def orbit(free):
    """Act by high-row permutations and compensate for the new base row."""
    E = [(0, q // 4, q % 4) for q in free]
    return {tuple(sorted((4 * ((c[p[1]] - c[p[0]]) % 4) + (c[p[2]] - c[p[0]]) % 4 for c in E))) for p in permutations(range(3))}

def cases():
    """Enumerate high-row shapes up to row and free-column permutations."""
    for u in (2, 3):
        vis = set()
        for f in combinations_with_replacement(range(16), 5 - u):
            if f in vis:
                continue
            vis.update(orbit(f))
            v = fields(u, f, 0)
            if v is not None:
                for o in range(1 << len(v[1])):
                    yield (u, f, o)


UNITS = ((1, 0), (0, 1), (-1, 0), (0, -1))

def low_data(u, f, ori):
    """Collapse the active columns to a single aggregate in all conics."""
    (ph, pairs, sign) = fields(u, f, ori)
    take = [0, *range(u, 5)]
    ag = [[row[j] for j in take] for row in ph]
    pp = [(i, k, [b[j] for j in take], [c[j] for j in take]) for (i, k, b, c) in pairs]
    return (ag, pp, ph, pairs, sign)

def low_ideal(ag, pairs, orient, d):
    """Build all fixed-degree monomial multiples of the oriented pair conics."""
    n = len(ag[0])
    basis = tuple((tuple((int(i == j) for j in range(n))) for i in range(n)))
    (es, ei) = monomials(n, d)
    xs = exponents(d - 2, n)
    A = np.zeros((len(pairs) * len(xs), len(es)), dtype=np.complex128)
    for (k, pair) in enumerate(pairs):
        q = restricted_Q(pair, ag, basis, -1j if orient >> k & 1 else 1j)
        for (z, e) in enumerate(xs):
            for (a, v) in q.items():
                A[z + k * len(xs), ei[tuple((x + y for (x, y) in zip(a, e)))]] = v
    return (A.real.astype(np.int64), A.imag.astype(np.int64))

def terms(ag, sign):
    """Return necessary nonzero linear forms in the aggregate weights."""
    n = len(ag[0])
    sigma = [[UNITS[x] for x in r] for r in ag]
    out = sigma + [[(int(i == j), 0) for i in range(n)] for j in range(n)]
    for (i, k) in sign:
        for z in (-1, 1):
            out.append([(a + z * c, b + z * d) for ((a, b), (c, d)) in zip(sigma[i], sigma[k])])
    return out

def check_open(M, forms):
    """Keep common eigenvectors on which the product of required factors is nonzero."""
    s = len(M[0][0])
    H = (np.eye(s, dtype=object), np.zeros((s, s), dtype=object))
    for coeff in forms:
        H = normalize(mul(H, add_many([scale(a, m) for (a, m) in zip(coeff, M)])))
        if not nonzero(H):
            return None
    h = H
    for k in range(s.bit_length()):
        h = normalize(mul(h, h))
        if not nonzero(h):
            return None
    return H

def low_gram(u, ph, pairs, M, p):
    """Evaluate the nine physical constraints and their Gram blocks at finite operators."""
    r = sqrt_i(p)
    units = [1, r, p - 1, p - r]
    d = len(M[0][0])
    W = np.array([np.asarray((a + r * b) % p, dtype=np.int64) for (a, b) in M])
    e = np.array([[units[x] for x in row] for row in ph])
    E = e[:, :, None, None] * W[None, :, :, :] % p
    s = E.sum(1) % p
    F = np.zeros((9, 4, 5, d, d), dtype=np.int64)
    for i in range(3):
        F[i, i] = E[i]
    F[3, 3, 0] = W[0]
    F[4, 3, 1:u] = W[1:u]
    rel = {(i, k): (b, c) for (i, k, b, c) in pairs}
    z = 5
    for i in range(3):
        for k in range(i):
            if (i, k) in rel:
                (b, c) = rel[i, k]
                for j in range(5):
                    if b[j] != -1:
                        F[z, i, j] = s[k] @ E[i, j] % p
                    if c[j] != -1:
                        F[z, k, j] = s[i] @ E[k, j] % p
            else:
                for j in range(5):
                    F[z, i, j] = -(s[k] @ E[k, j]) % p
                    F[z, k, j] = s[i] @ E[i, j] % p
            z += 1
    F[-1] = np.eye(d, dtype=np.int64)[None, None, :, :]
    K = np.kron(3 * np.eye(4, dtype=np.int64) - 1, 4 * np.eye(5, dtype=np.int64) - 1)
    F = F.reshape(9, 20, d, d)
    FD = np.einsum('xy,ayij->axij', K, F) % p
    return np.einsum('axij,bxjk->abik', F, FD) % p

def low_tangent(u, ph, pairs, M):
    """Exclude all choices of the within-block split using projected Gram determinants."""
    d = len(M[0][0])
    E = np.eye(d, dtype=object)
    zero = np.zeros((d, d), dtype=object)

    def actual(t):
        if u == 2:
            return [M[0], M[0], *[scale((2, 0), a) for a in M[1:]]]
        return [scale((2, 0), M[0]), add_many([M[0], (t * E, zero)]), add_many([M[0], (-t * E, zero)]), *[scale((4, 0), a) for a in M[1:]]]
    for p in (65521, 1009, 241):
        G = low_gram(u, ph, pairs, actual(0), p)
        if u == 3:
            inc = (low_gram(u, ph, pairs, actual(1), p) - G) % p
            assert np.array_equal((G + 4 * inc) % p, low_gram(u, ph, pairs, actual(2), p))
        common = []
        full = False
        for seed in range(15):
            rand = Random(seed)
            A = np.array([[rand.randrange(-7, 8) for z in range(9)] for i in range(7)], dtype=np.int64)
            B = np.einsum('ia,abuv,jb->iujv', A, G, A).reshape(7 * d, 7 * d) % p
            if u == 2:
                if full_rank(B, p):
                    return (p, seed)
            else:
                C = np.einsum('ia,abuv,jb->iujv', A, inc, A).reshape(7 * d, 7 * d) % p
                dg = 4 * d
                v = [determinant((B + j * C) % p, p) for j in range(dg + 1)]
                pol = interpolate(v, p)
                if len(pol) == dg + 1:
                    full = True
                if pol:
                    common = poly_gcd(common, pol, p)
                if full and common == [1]:
                    return (p, seed)
    return None

def finite_case(u, f, o):
    """Certify a single finite aggregate case by contractions and the isotropic rank bound."""
    (ag, pp, ph, pairs, sign) = low_data(u, f, o)
    n = len(ag[0])
    d = n + 1
    forms = terms(ag, sign)
    (A, B) = low_ideal(ag, pp, o, d)
    res = lift(A, B, EXTENDED)
    if res is None:
        return ('lift', -1)
    (E, _, _) = res
    while E and d >= 2:
        (M, reason) = multiplication(E, n, d)
        if M is not None:
            H = check_open(M, forms)
            if H is None:
                return ('excluded', len(E))
            N = compressed(M, H)
            if N is None:
                return ('compression', -1)
            ok = low_tangent(u, ph, pairs, N)
            return ('tangent' if ok else 'unresolved', len(N[0][0]))
        (E, _) = shrink(E, n, d, forms)
        d -= 1
        if E is None:
            return ('compression', -1)
    return ('excluded' if not E else 'positive', len(E))


def curve_data(f, o):
    """Build center totals and the two signed differences in flattened variables."""
    (ag, pp, ph, pairs, sign) = low_data(2, f, o)
    if len(pp) != 2:
        return
    g = next((j for j in range(3) if all((j in (i, k) for (i, k, _, _) in pp))))
    info = []
    for (ix, (i, k, b, c)) in enumerate(pp):
        B = tuple((j for (j, z) in enumerate(b) if z != -1))
        C = tuple((j for (j, z) in enumerate(c) if z != -1))
        if g == i:
            (B, C) = (C, B)
        A = tuple((j for j in range(4) if j not in B + C))
        info.append((A, B, C, -1 if o >> ix & 1 else 1))
    P = info[0][0]
    Q = tuple((j for j in range(4) if j not in P))
    T = [[int(j in P) for j in range(4)], [int(j in Q) for j in range(4)]]
    for (a, b, c, sg) in info:
        T.append([int(j in b) - int(j in c) for j in range(4)])
    typ = [(int(a != P), sg) for (a, b, c, sg) in info]
    assert all((a in (P, Q) for (a, b, c, sg) in info))
    return (ag, pp, ph, pairs, sign, g, info, T, typ)

def curve_models(f, o):
    """Recover aggregate weights from the center totals and their quadratic radicals."""
    (ag, pp, ph, pairs, sign, g, info, T, typ) = curve_data(f, o)
    d = det(T)
    if not d:
        return []
    N = 4
    adj = np.array([[(-1) ** (i + j) * det([[T[a][b] for b in range(N) if b != i] for a in range(N) if a != j]) for j in range(N)] for i in range(N)])
    assert np.array_equal(adj @ np.array(T), d * np.eye(4, dtype=np.int64))
    types = list(dict.fromkeys(typ))
    K = len(types)
    out = []
    for signs in product((-1, 1), repeat=2 - K):
        used = set()
        z = 0
        R = np.zeros((4, 2 + K), dtype=np.complex128)
        R[0, 0] = R[1, 1] = 2
        for (i, t) in enumerate(typ):
            (fix, sg) = t
            s = 1
            if t in used:
                s = signs[z]
                z += 1
            used.add(t)
            R[2 + i, 1 - fix] = 1 - sg * 1j
            R[2 + i, 2 + types.index(t)] = s
        W = adj @ R * np.array([G[-r % 4] for r in ag[g]])[:, None]
        Wa = np.vstack([W[0], W[0], 2 * W[1:]])
        S = np.array([[G[x] for x in row] for row in ph]) @ Wa
        no = [*Wa, *S]
        for (i, k) in sign:
            no.extend((S[i] + S[k], S[i] - S[k]))
        out.append(None if any((np.all(v == 0) for v in no)) else (ph, pairs, types, Wa))
    return out


LOW_PROFILES = ((1, 5, 1), (1, 4, 2), (1, 3, 3), (0, 5, 2), (0, 4, 3))

def build_low(model, orient, lam, p, deg):
    """Evaluate all radical branches of the nine-row Gram over a split finite-field extension."""
    (ph, pairs, types, W) = model
    (I, sq, has, v, vi, inv) = field(p)
    sheets = 2 ** len(types)
    ts = np.arange(deg + 1, dtype=np.int64)
    A = ts
    B = (1 - lam * ts) % p
    vals = [A, B]
    rs = []
    ims = []
    for (fixed, sign) in types:
        gamma = sign * I % p
        a = vals[fixed]
        t = vals[1 - fixed]
        disc = ((4 - 2 * gamma) * (t * t % p) - 4 * (1 - gamma) * (a * a % p)) % p
        rs.append(np.where(has[disc], sq[disc], 0))
        ims.append(np.where(has[disc], 0, sq[disc * vi % p]))
    signs = np.array(list(product((-1, 1), repeat=len(types))), dtype=np.int64)
    E = np.zeros((deg + 1, sheets, 2 + len(types)), dtype=np.int64)
    EE = E.copy()
    E[:, :, 0] = A[:, None]
    E[:, :, 1] = B[:, None]
    E[:, :, 2:] = np.array(rs).T[:, None, :] * signs[None, :, :]
    EE[:, :, 2:] = np.array(ims).T[:, None, :] * signs[None, :, :]
    coef = (W.real.astype(np.int64) + I * W.imag.astype(np.int64)) % p
    wr = (E @ coef.T).reshape(-1, 5) % p
    wi = (EE @ coef.T).reshape(-1, 5) % p
    roots = [1, I, p - 1, p - I]
    ep = np.array([[roots[c] for c in q] for q in ph], dtype=np.int64)
    R = ep[None, :, :] * wr[:, None, :] % p
    J = ep[None, :, :] * wi[:, None, :] % p
    sr = R.sum(2) % p
    si = J.sum(2) % p
    N = len(wr)
    F = np.zeros((N, 9, 4, 5), dtype=np.int64)
    Fi = F.copy()
    for i in range(3):
        F[:, i, i] = R[:, i]
        Fi[:, i, i] = J[:, i]
    F[:, 3, 3, 0] = wr[:, 0]
    Fi[:, 3, 3, 0] = wi[:, 0]
    F[:, 4, 3, 1] = wr[:, 1]
    Fi[:, 4, 3, 1] = wi[:, 1]
    rel = {(i, k): (b, c) for (i, k, b, c) in pairs}
    z = 5
    for i in range(3):
        for k in range(i):
            if (i, k) in rel:
                (b, c) = rel[i, k]
                for j in range(5):
                    if b[j] >= 0:
                        (F[:, z, i, j], Fi[:, z, i, j]) = mult((sr[:, k], si[:, k]), (R[:, i, j], J[:, i, j]), p, v)
                    if c[j] >= 0:
                        (F[:, z, k, j], Fi[:, z, k, j]) = mult((sr[:, i], si[:, i]), (R[:, k, j], J[:, k, j]), p, v)
            else:
                for j in range(5):
                    (rr, ii) = mult((sr[:, k], si[:, k]), (R[:, k, j], J[:, k, j]), p, v)
                    F[:, z, i, j] = -rr % p
                    Fi[:, z, i, j] = -ii % p
                    (F[:, z, k, j], Fi[:, z, k, j]) = mult((sr[:, i], si[:, i]), (R[:, i, j], J[:, i, j]), p, v)
            z += 1
    F[:, 8] = 1
    F = F.reshape(N, 9, 20)
    Fi = Fi.reshape(N, 9, 20)
    K = np.kron(3 * np.eye(4, dtype=np.int64) - 1, 4 * np.eye(5, dtype=np.int64) - 1)
    KFr = F @ K % p
    KFi = Fi @ K % p
    Gr = (F @ KFr.transpose(0, 2, 1) - v * (Fi @ KFi.transpose(0, 2, 1) % p)) % p
    Gi = (F @ KFi.transpose(0, 2, 1) + Fi @ KFr.transpose(0, 2, 1)) % p
    return (Gr, Gi)

def trial_low(model, orient, p, lam):
    """Bound the norm degree and calculate common monic factors of the projected minor norms."""
    sheets = 2 ** len(model[2])
    Dmax = 20 * sheets
    (Gr, Gi) = build_low(model, orient, lam, p, Dmax)
    (_, _, _, v, _, inv) = field(p)
    common = []
    full = False
    for test in range(len(LOW_PROFILES) * 2):
        (n0, n1, n2) = LOW_PROFILES[test % len(LOW_PROFILES)]
        degree = 2 * (n1 + 2 * n2) * sheets
        rng = Random(test + 103)
        A = np.zeros((7, 9), dtype=np.int64)
        if n0:
            A[0, 8] = 1
        A[n0:n0 + n1, :5] = np.array([[rng.randrange(-7, 8) for _ in range(5)] for k in range(n1)], dtype=np.int64).reshape(n1, 5)
        A[n0 + n1:, 5:8] = np.array([[rng.randrange(-7, 8) for _ in range(3)] for k in range(n2)])
        last = (degree + 1) * sheets
        rr = A @ Gr[:last] @ A.T % p
        ii = A @ Gi[:last] @ A.T % p
        (dr, di) = arraydet(rr, ii, p, v, inv)
        dr = dr.reshape(-1, sheets)
        di = di.reshape(-1, sheets)
        nr = np.ones(len(dr), dtype=np.int64)
        ni = np.zeros(len(dr), dtype=np.int64)
        for k in range(sheets):
            (nr, ni) = mult((nr, ni), (dr[:, k], di[:, k]), p, v)
        assert not np.any(ni)
        f = interpolate(nr.tolist(), p)
        if len(f) == degree + 1:
            full = True
        if f:
            common = poly_gcd(common, f, p)
        if full and len(common) == 1:
            return ('excluded', p, lam, test + 1, common)
    return ('rest', p, lam, len(LOW_PROFILES) * 2, common, full)


def physical(ph, pairs, w):
    """Construct the scalar low-row Gram at exactly representable Gaussian integers."""
    ep = np.array([[G[x] for x in row] for row in ph])
    V = ep * w[None, :]
    s = V.sum(1)
    F = np.zeros((9, 4, 5), dtype=np.complex128)
    for i in range(3):
        F[i, i] = V[i]
    F[3, 3, 0] = w[0]
    F[4, 3, 1] = w[1]
    rel = {(i, k): (b, c) for (i, k, b, c) in pairs}
    g = 5
    for i in range(3):
        for k in range(i):
            if (i, k) in rel:
                (b, c) = rel[i, k]
                for j in range(5):
                    if b[j] != -1:
                        F[g, i, j] = s[k] * V[i, j]
                    if c[j] != -1:
                        F[g, k, j] = s[i] * V[k, j]
            else:
                F[g, i] = -s[k] * V[k]
                F[g, k] = s[i] * V[i]
            g += 1
    F[8] = 1
    f = F.reshape(9, 20)
    assert 20 ** 2 * 12 * max((abs(v) for v in f.flat)) ** 2 < 2 ** 51
    K = np.kron(3 * np.eye(4, dtype=np.int64) - 1, 4 * np.eye(5, dtype=np.int64) - 1)
    return f @ K @ f.T

def has_common_endpoint_factor(m):
    """Check over the Gaussian integers that every selected norm vanishes at t=1."""
    (ph, pairs, types, W) = m
    grams = []
    for sign in product((-1, 1), repeat=len(types)):
        u = [v * (1 + sg * 1j) for (v, (fixed, sg)) in zip(sign, types)]
        gr = physical(ph, pairs, W @ np.array([1, -1, *u]))
        grams.append(gr)
        if exact_rank(gr.tolist(), 9) <= 6:
            return True
    for z in range(2 * len(LOW_PROFILES)):
        (n0, n1, n2) = LOW_PROFILES[z % len(LOW_PROFILES)]
        r = Random(z + 103)
        A = np.zeros((7, 9), dtype=np.int64)
        if n0:
            A[0, 8] = 1
        A[n0:n0 + n1, :5] = np.array([[r.randrange(-7, 8) for j in range(5)] for k in range(n1)])
        A[n0 + n1:, 5:8] = np.array([[r.randrange(-7, 8) for j in range(3)] for k in range(n2)])
        assert all((9 ** 2 * 49 * max((abs(x) for x in gr.flat)) < 2 ** 51 for gr in grams))
        if all((exact_rank((A @ gr @ A.T).tolist(), 7) == 7 for gr in grams)):
            return False
    return True


def dependent_data(u, f, o):
    """Identify a repeated aggregate phase while allowing its net mass to vanish."""
    (ag, pp, ph, pairs, sign) = low_data(u, f, o)
    coords = (0, *f)
    profiles = tuple(dict.fromkeys(coords))
    idx = [coords.index(z) for z in profiles]
    assert len(profiles) == 3
    A = [[r[j] for j in idx] for r in ag]
    P = [(i, k, [b[j] for j in idx], [c[j] for j in idx]) for (i, k, b, c) in pp]
    doubled = next((z for z in coords if coords.count(z) == 2))
    forms = terms(A, sign)
    del forms[3 + profiles.index(doubled)]
    return (A, P, ph, pairs, profiles, doubled, forms)

def pencil(f, o, ph, pairs, profiles, doubled, M):
    """Certify every value of the free splitting parameter of a repeated phase."""
    d = len(M[0][0])
    I = np.eye(d, dtype=object)
    zero = np.zeros((d, d), dtype=object)

    def actual(t):
        vec = {q: a for (q, a) in zip(profiles, M)}
        T = (t * I, zero)
        neg = (-t * I, zero)
        if doubled == 0:
            aa = [T, T]
            for q in f:
                aa.append(add_many([vec[q], scale((-2, 0), T)]) if q == 0 else vec[q])
            return aa
        aa = [vec[0], vec[0]]
        seen = False
        for q in f:
            if q != doubled:
                aa.append(scale((2, 0), vec[q]))
            else:
                aa.append(add_many([vec[q], neg if seen else T]))
                seen = True
        return aa
    for p in (65521, 1009):

        def gg(t):
            return low_unit_gram(ph, pairs, actual(t), p)
        G = gg(0)
        Gp = gg(1)
        Gm = gg(-1)
        lin = (Gp - Gm) * pow(2, -1, p) % p
        quad = ((Gp + Gm) * pow(2, -1, p) - G) % p
        assert np.array_equal((G + 2 * lin + 4 * quad) % p, gg(2))
        common = []
        full = False
        for seed in range(15):
            rand = Random(seed)
            A = np.array([[rand.randrange(-7, 8) for j in range(9)] for i in range(7)], dtype=np.int64)
            XX = [np.einsum('ia,abuv,jb->iujv', A, op, A).reshape(7 * d, 7 * d) % p for op in (G, lin, quad)]
            bound = (6 if doubled == 0 else 4) * d
            if doubled != 0:
                assert not np.any(lin)
            vals = [determinant((XX[0] + t * XX[1] + t * t * XX[2]) % p, p) for t in range(bound + 1)]
            pol = interpolate(vals, p)
            if len(pol) == bound + 1:
                full = True
            if pol:
                common = poly_gcd(common, pol, p)
            if full and common == [1]:
                return (p, seed)
    return None

def low_unit_gram(ph, pairs, M, p):
    """Use the two fixed low coordinates as constant unit-weight constraint covectors."""
    r = sqrt_i(p)
    units = [1, r, p - 1, p - r]
    d = len(M[0][0])
    W = np.array([np.asarray((a + r * b) % p, dtype=np.int64) for (a, b) in M])
    e = np.array([[units[x] for x in row] for row in ph])
    E = e[:, :, None, None] * W[None, :, :, :] % p
    s = E.sum(1) % p
    F = np.zeros((9, 4, 5, d, d), dtype=np.int64)
    for i in range(3):
        F[i, i] = E[i]
    F[3, 3, 0] = F[4, 3, 1] = np.eye(d, dtype=np.int64)
    rel = {(i, k): (b, c) for (i, k, b, c) in pairs}
    z = 5
    for i in range(3):
        for k in range(i):
            if (i, k) in rel:
                (b, c) = rel[i, k]
                for j in range(5):
                    if b[j] != -1:
                        F[z, i, j] = s[k] @ E[i, j] % p
                    if c[j] != -1:
                        F[z, k, j] = s[i] @ E[k, j] % p
            else:
                for j in range(5):
                    F[z, i, j] = -(s[k] @ E[k, j]) % p
                    F[z, k, j] = s[i] @ E[i, j] % p
            z += 1
    F[-1] = np.eye(d, dtype=np.int64)[None, None, :, :]
    K = np.kron(3 * np.eye(4, dtype=np.int64) - 1, 4 * np.eye(5, dtype=np.int64) - 1)
    F = F.reshape(9, 20, d, d)
    FD = np.einsum('xy,ayij->axij', K, F) % p
    return np.einsum('axij,bxjk->abik', F, FD) % p

def dependent_case(f, o):
    """Recompute the two conics in three aggregate coordinates and test the split."""
    (ag, P, ph, pairs, prof, double, forms) = dependent_data(2, f, o)
    d = 4
    (A, B) = low_ideal(ag, P, o, d)
    res = lift(A, B, EXTENDED)
    assert res is not None
    (E, _, _) = res
    while E and d >= 2:
        (M, _) = multiplication(E, 3, d)
        if M is not None:
            H = check_open(M, forms)
            if H is None:
                return ('excluded', 0)
            N = compressed(M, H)
            assert N
            cert = pencil(f, o, ph, pairs, prof, double, N)
            return ('pencil' if cert else 'unresolved', len(N[0][0]))
        (E, _) = shrink(E, 3, d, forms)
        d -= 1
    return ('excluded' if not E else 'positive', len(E))


def smallgram(u, f, coords):
    """Construct the all-sign scalar Gram in four integer variables."""
    (t, a, b, c) = coords
    w = np.array((t, t, a, b, c) if u == 2 else (t, a, t - a, b, c), dtype=np.int64)
    (ph, _, _) = fields(u, f, 0)
    E = np.array([[1 if z == 0 else -1 for z in q] for q in ph], dtype=np.int64)
    W = E * w[None, :]
    s = W.sum(1)
    F = np.zeros((9, 4, 5), dtype=np.int64)
    for i in range(3):
        F[i, i] = W[i]
    F[3, 3, 0] = 1
    if u == 2:
        F[4, 3, 1] = 1
    else:
        F[4, 3, 1:3] = w[1:3]
    g = 5
    for i in range(3):
        for k in range(i):
            F[g, i] = -s[k] * W[k]
            F[g, k] = s[i] * W[i]
            g += 1
    F[-1] = 1
    X = F.reshape(9, 20)
    K = np.kron(3 * np.eye(4, dtype=np.int64) - 1, 4 * np.eye(5, dtype=np.int64) - 1)
    assert 20 ** 2 * 6 * max((abs(int(v)) for v in X.flat)) ** 2 < 2 ** 62
    return (X @ K @ X.T).tolist()

def adj(a):
    """Fraction-free elimination for the determinant and adjugate, up to a common adjugate sign."""
    n = len(a)
    A = [r.copy() + [int(i == j) for i in range(n)] for (j, r) in enumerate(a)]
    prev = 1
    sgn = 1
    for q in range(n):
        z = next((i for i in range(q, n) if A[i][q]), None)
        if z is None:
            return None
        if z != q:
            (A[z], A[q]) = (A[q], A[z])
            sgn = -sgn
        v = A[q][q]
        pr = A[q]
        for (i, row) in enumerate(A):
            if i == q:
                continue
            h = row[q]
            for j in range(2 * n):
                if j != q:
                    row[j] = (v * row[j] - h * pr[j]) // prev
            row[q] = 0
        prev = v
    return (sgn * prev, [row[n:] for row in A])

@lru_cache(None)
def grid1(d):
    """The integer simplex unisolvent for all polynomials of total degree at most d."""
    return tuple(((x, y, z) for x in range(d + 1) for y in range(d - x + 1) for z in range(d - x - y + 1)))

@lru_cache(None)
def falling(n, shift):
    """Expand the shifted falling factorial in the ordinary monomial basis."""
    a = [1]
    for j in range(n):
        b = [0] * (len(a) + 1)
        for (k, x) in enumerate(a):
            b[k] -= (j + shift) * x
            b[k + 1] += x
        a = b
    return a

def polify(table, d, shifts):
    """Recover a homogeneous four-variable polynomial by exact simplex differences."""
    vals = {a: table[a] for a in grid1(d)}
    for stage in (0, 1):
        for dim in range(3):
            nxt = {}
            for q in grid1(d):
                if q[dim]:
                    continue
                lim = d - sum(q)
                v = list(q)
                line = []
                for i in range(lim + 1):
                    v[dim] = i
                    line.append(vals[tuple(v)])
                coeff = [0] * (lim + 1)
                if stage == 0:
                    for j in range(lim + 1):
                        (coeff[j], rem) = divmod(line[0], factorial(j))
                        assert rem == 0
                        line = [y - x for (x, y) in zip(line, line[1:])]
                else:
                    for (j, u) in enumerate(line):
                        for (k, w) in enumerate(falling(j, shifts[dim])):
                            coeff[k] += u * w
                for i in range(lim + 1):
                    v[dim] = i
                    nxt[tuple(v)] = coeff[i]
            vals = nxt
    return {(d - sum(k), *k): v for (k, v) in vals.items() if v}

def factors(u, f):
    """List the primitive linear forms that must all be nonzero in an all-sign case."""
    W = [(1, 0, 0, 0), (1, 0, 0, 0), (0, 1, 0, 0), (0, 0, 1, 0), (0, 0, 0, 1)] if u == 2 else [(1, 0, 0, 0), (0, 1, 0, 0), (1, -1, 0, 0), (0, 0, 1, 0), (0, 0, 0, 1)]
    (ph, _, _) = fields(u, f, 0)
    sig = [tuple((sum(((1 if e == 0 else -1) * col[i] for (e, col) in zip(row, W))) for i in range(4))) for row in ph]
    fs = [*W, *sig]
    for i in range(3):
        for j in range(i):
            for a in (-1, 1):
                fs.append(tuple((x + a * y for (x, y) in zip(sig[i], sig[j]))))
    out = set()
    for ff in fs:
        z = reduce(gcd, ff, 0)
        ff = tuple((x // z for x in ff))
        if next((x for x in ff if x)) < 0:
            ff = tuple((-x for x in ff))
        out.add(ff)
    return tuple(sorted(out))

def div_linear(poly, L):
    """Return the exact quotient by a primitive linear factor if division has zero remainder."""
    i = next((k for (k, x) in enumerate(L) if abs(x) == 1), None)
    assert i is not None, L
    A = poly.copy()
    out = {}
    for t in range(max((e[i] for e in A)), 0, -1):
        for e in [k for k in A if k[i] == t]:
            a = A.pop(e)
            v = a * L[i]
            j = list(e)
            j[i] -= 1
            out[tuple(j)] = v
            for (k, b) in enumerate(L):
                if b and k != i:
                    j[k] += 1
                    m = tuple(j)
                    A[m] = A.get(m, 0) - v * b
                    if not A[m]:
                        A.pop(m)
                    j[k] -= 1
    return out if not A else None

def prepare(u, f, maxdeg):
    """Generate homogeneous complementary Gram minors, divide only by required nonzero factors."""
    deg = [1, 1, 1, 0, 0 if u == 2 else 1, 2, 2, 2, 0]
    total = sum(deg)
    pair = list(combinations(range(9), 2))
    spec = []
    for (i, L) in enumerate(pair):
        for R in pair[:i + 1]:
            d = 2 * total - sum((deg[j] for j in (*L, *R)))
            if d <= maxdeg:
                spec.append((d, L, R))
    dd = max((q[0] for q in spec))
    sh = (25, 59, 97)
    tables = [{} for x in spec]
    for z in grid1(dd):
        x = (1, *(a + b for (a, b) in zip(sh, z)))
        gram = smallgram(u, f, x)
        res = adj(gram)
        if res is None:
            raise RuntimeError((u, f, z))
        (det, A) = res
        if z == (0, 0, 0):
            ident = np.array(gram, dtype=object) @ np.array(A, dtype=object)
            assert np.array_equal(ident, det * np.eye(9, dtype=object)) or np.array_equal(ident, -det * np.eye(9, dtype=object))
        for (index, (d, (i, k), (j, l))) in enumerate(spec):
            if sum(z) > d:
                continue
            v = (A[j][i] * A[l][k] - A[l][i] * A[j][k]) * (-1) ** (i + j + k + l)
            tab = tables[index]
            (tab[z], rem) = divmod(v, det)
            assert rem == 0
    fac = factors(u, f)
    result = []
    for ((d, L, R), table) in zip(spec, tables):
        poly = polify(table, d, sh)
        if not poly:
            continue
        for vv in fac:
            while True:
                q = div_linear(poly, vv)
                if q is None:
                    break
                poly = q
                if not sum(next(iter(poly))):
                    break
        red = reduce(gcd, poly.values(), 0)
        red = red if next(iter(poly.values())) > 0 else -red
        vec = [[list(k), v // red] for (k, v) in sorted(poly.items())]
        dd = sum(vec[0][0])
        result.append([list(L), list(R), dd, vec])
    return result


PP = 1000000007

def primes():
    n = PP
    while True:
        if all((n % q for q in range(3, isqrt(n) + 1, 2))):
            yield n
        n -= 2

def source(u, f, d, lim):
    """Construct the indicated subset of degree-fourteen multiples of exact divided Gram minors."""
    gen = prepare(u, f, lim)
    ids = SELECTED_ROWS[(u, *f)]
    assert len(ids) == len(set(ids)) and min(ids) >= 0
    selected = set(ids)
    seen = 0
    (es, indices) = monomials(4, d)
    out = np.zeros((len(ids), len(es)), dtype=object)
    r = 0
    for (L, R, z, vec) in gen:
        if z > d:
            continue
        for a in exponents(d - z, 4):
            if seen in selected:
                for (t, c) in vec:
                    out[r, indices[tuple((i + j for (i, j) in zip(t, a)))]] = c
                r += 1
            seen += 1
    assert r == len(ids)
    return out

def lift_real(A, nprimes=40):
    """Recover a full rational nullspace, with modular rank and exact integer identities."""
    mod = 1
    res = None
    free = None
    for (ip, p) in enumerate(primes()):
        if ip >= nprimes:
            break
        (f, N) = get_kernel(np.asarray(A % p, dtype=np.int64), p)
        if len(f) != A.shape[1] - A.shape[0]:
            continue
        if free is not None and (not np.array_equal(f, free)):
            continue
        free = f
        cur = [int(i) for i in N.flat]
        if res is None:
            res = cur
        else:
            t = pow(mod, -1, p)
            res = [a + mod * ((b - a) * t % p) for (a, b) in zip(res, cur)]
        mod *= p
        qs = [fraction(v, mod) for v in res]
        if any((v is None for v in qs)):
            continue
        E = []
        width = A.shape[1]
        for j in range(len(f)):
            row = qs[j * width:(j + 1) * width]
            den = lcm(*(v.denominator for v in row))
            E.append([int(v * den) for v in row])
        E = np.array(E, dtype=object)
        if not np.any(A @ E.T):
            assert np.all(np.diagonal(E[:, f]) != 0) and (not np.any(E[:, f] - np.diag(np.diagonal(E[:, f]))))
            return (E, ip + 1)
    return (None, None)

def adjr(a):
    """Compute a common nonzero denominator and inverse numerator of an integer matrix."""
    n = len(a)
    A = [list(r) + [int(i == j) for i in range(n)] for (j, r) in enumerate(a)]
    old = 1
    for k in range(n):
        z = next((i for i in range(k, n) if A[i][k]))
        (A[k], A[z]) = (A[z], A[k])
        piv = A[k][k]
        base = A[k]
        for (i, row) in enumerate(A):
            if i == k:
                continue
            f = row[k]
            for j in range(2 * n):
                if j != k:
                    row[j] = (piv * row[j] - f * base[j]) // old
            row[k] = 0
        old = piv
    return (old, np.array([r[n:] for r in A], dtype=object))

def sat_once(E, d, C):
    """Intersect the current monomial dual with exact pullbacks of lower-degree annihilators."""
    axes = contractions(4, d)
    V = [E[:, idx] for idx in axes]
    U = sum((c * a for (c, a) in zip(C, V)), np.zeros_like(V[0]))
    P = np.asarray(U % PP, dtype=np.int64)
    (ii, jj, _) = rref(P.tolist(), P.shape[1], PP)
    r = len(ii)
    if r:
        pivot = P[ii][:, jj]
        augmented = np.hstack((pivot, P[ii]))
        t = augmented.copy()
        for j in range(r):
            pp = j + int(np.flatnonzero(t[j:, j])[0])
            t[[j, pp]] = t[[pp, j]]
            iv = pow(int(t[j, j]), -1, PP)
            t[j] = t[j] * iv % PP
            for q in range(r):
                if q != j:
                    t[q] = (t[q] - t[q, j] * t[j]) % PP
        coeff = t[:, r:]
    else:
        coeff = np.zeros((0, P.shape[1]), dtype=np.int64)
    ob = []
    for A in V:
        base = np.asarray(A % PP, dtype=np.int64)
        left = base[:, jj].copy()
        projected = np.zeros_like(base)
        for j in range(r):
            projected = (projected + left[:, j, None] * coeff[None, j, :]) % PP
        ob.append((base - projected) % PP)
    Z = np.hstack(ob)
    (_, keep, _) = rref(Z.tolist(), Z.shape[1], PP)
    if not keep:
        return E
    if r:
        (det, adj) = adjr(U[ii][:, jj])
    else:
        (det, adj) = (1, np.zeros((0, 0), dtype=object))
    uses = []
    width = U.shape[1]
    for k in keep:
        (block, idx) = divmod(k, width)
        coeff = adj @ U[ii, idx] if r else np.zeros(0, dtype=object)
        assert np.array_equal(det * U[:, idx], U[:, jj] @ coeff)
        val = det * V[block][:, idx] - V[block][:, jj] @ coeff
        dv = reduce(gcd, val, 0)
        assert dv
        uses.append(val // dv)
    T = np.array(uses, dtype=object)
    n = len(E)
    k = len(keep)
    (_, pivot, _) = rref(np.asarray(T % PP, dtype=np.int64).tolist(), n, PP)
    assert len(pivot) == k
    if k == n:
        return np.zeros((0, E.shape[1]), dtype=object)
    (det, adj) = adjr(T[:, pivot])
    result = []
    for j in range(n):
        if j in pivot:
            continue
        a = np.zeros(n, dtype=object)
        a[j] = det
        a[pivot] = -adj @ T[:, j]
        assert not np.any(T @ a)
        row = a @ E
        dv = reduce(gcd, row, 0)
        result.append(row // dv)
    return np.array(result, dtype=object)

def verify_sign(u, f, d, lim):
    """Certify that no degree-fourteen evaluation survives on the required all-sign open set."""
    A = source(u, f, d, lim)
    (E, np1) = lift_real(A)
    if E is None:
        return ('no_lift', [], None)
    st = []
    for k in range(8):
        old = len(E)
        for (i, C) in enumerate(factors(u, f)):
            n = len(E)
            E = sat_once(E, d, C)
            if len(E) != n:
                st.append((i, n, len(E)))
            if not len(E):
                return ('excluded', st, np1)
        if len(E) == old:
            break
    return ('unresolved', st, np1)


# Independent-row hints for multiples of the exact divided Gram minors.
SELECTED_ROWS = {
    (2, 0, 2, 8): tuple(map(int,(
        '0 1 2 3 4 5 6 7 8 9 10 11 13 14 15 16 17 18 19 20 21 22 23 24 25 26 27 28 29 30 31 33 34 35 36 37 38 '
        '39 40 41 42 43 44 45 46 47 48 49 50 51 52 53 54 55 56 57 58 59 60 61 62 63 64 69 70 71 72 73 74 76 '
        '77 78 79 80 81 82 83 84 86 87 88 89 90 91 92 93 94 96 97 98 101 102 103 105 106 107 109 110 111 112 '
        '113 114 115 116 117 118 119 120 121 122 123 124 125 126 127 128 129 130 131 132 133 134 135 136 137 '
        '138 154 156 157 158 159 160 161 162 163 164 165 166 167 168 169 170 171 172 173 174 175 176 177 178 '
        '179 184 185 186 187 188 189 190 191 192 193 194 195 196 197 198 199 200 201 202 203 204 205 206 207 '
        '208 209 210 211 212 213 214 215 216 217 218 219 220 221 222 223 224 225 226 227 228 229 231 232 234 '
        '235 237 240 241 248 249 250 251 252 253 254 255 256 257 258 259 260 261 262 263 264 265 266 267 278 '
        '279 280 281 282 283 284 285 286 287 288 289 290 291 292 293 294 295 296 297 298 299 300 301 302 303 '
        '304 305 306 307 308 309 310 311 312 313 314 315 316 317 318 319 320 321 323 324 325 326 327 328 329 '
        '330 331 332 333 334 335 336 337 338 339 340 341 342 343 344 345 346 347 348 350 351 352 354 355 356 '
        '357 358 359 360 361 366 367 368 369 370 371 372 373 374 375 376 377 378 379 380 381 382 383 384 385 '
        '386 387 388 389 390 391 392 393 394 395 396 397 398 399 400 401 402 403 404 405 406 407 408 409 410 '
        '411 412 413 414 415 416 417 418 419 420 421 422 423 424 425 436 437 438 439 440 441 442 443 444 445 '
        '446 447 448 449 451 452 453 454 455 456 457 458 459 460 461 462 463 464 465 466 467 468 469 471 472 '
        '474 475 476 477 478 479 480 481 483 484 486 487 489 492 493 496 497 498 500 501 503 506 507 508 509 '
        '510 511 512 513 514 515 516 517 518 519 520 521 522 523 524 525 536 537 538 539 540 541 542 543 544 '
        '545 546 547 548 549 551 552 553 555 556 557 558 559 561 562 566 571 572 573 574 575 576 577 578 579 '
        '580 581 582 583 584 586 587 588 589 590 591 592 593 594 595 596 597 598 599 600 601 602 603 604 606 '
        '607 608 610 611 612 613 614 616 617 621 626 627 632 640 641 654 668 669 670 671 672 673 674 675 676 '
        '677 678 679 680 681 682 683 684 685 686 687 688 689 690 691 692 693 694 695 696 697 698 699 700 701 '
        '702 703 704 705 706 707 708 709 710 753 759 760 761 762 763 765 766 767 768 769 770 771 772 773 774 '
        '775 776 777 778 779 780 781 782 783 784 785 786 787 788 789 790 792 793 794 796 797 798 880 881 882 '
        '884 887 908 909 910 912 913 915 918 921 924 928 929 930 932 933 935 938 939 948 949 1002 1003 1004 '
        '1005 1006 1012 1022 1037 1057 1058 1059 1060 1061 1142 1143 1144 1145 1146 1158 1172 1317 1372 1457 '
        '1492 2332 2333 2392 4041 4096 4181 4216 4901 4957 5013 5209 5265 5818 5874 5875 6727 6979 7035 7700 '
        '7840 '
    ).split())),
    (2, 2, 2, 8): tuple(map(int,(
        '0 1 2 3 4 5 8 10 11 12 13 14 15 16 17 18 19 20 21 22 23 24 25 26 27 28 29 30 31 32 33 34 35 36 37 38 '
        '39 50 51 52 53 54 55 56 57 58 59 60 61 62 63 64 65 66 67 68 69 70 71 72 73 74 75 76 77 78 79 80 81 '
        '82 83 84 85 86 87 88 89 90 91 92 93 94 95 96 97 98 99 100 101 102 103 104 105 106 107 108 109 110 '
        '111 112 113 114 125 126 127 128 129 130 131 132 133 134 135 136 137 138 139 140 141 142 143 144 145 '
        '146 147 148 149 150 151 152 153 154 155 156 157 158 160 161 162 163 164 165 166 167 168 169 170 171 '
        '172 173 174 175 176 177 178 179 180 181 182 183 184 185 186 187 188 189 190 191 192 193 195 196 197 '
        '198 199 200 201 202 203 204 205 206 212 213 215 216 221 222 223 224 225 227 232 233 235 236 241 242 '
        '243 244 245 247 252 253 255 256 257 258 259 263 264 265 295 296 297 298 299 300 301 302 303 305 306 '
        '307 309 310 311 312 313 314 315 316 317 318 319 320 321 322 323 324 325 326 327 328 329 330 331 332 '
        '333 334 335 337 338 339 340 341 342 343 344 345 346 347 358 359 360 361 362 363 364 365 366 367 368 '
        '369 374 375 376 377 378 379 380 381 382 383 384 385 386 387 388 389 390 391 392 393 394 395 396 397 '
        '398 399 400 401 402 403 404 405 406 407 408 409 410 411 412 413 414 415 416 418 419 420 421 422 428 '
        '429 430 431 432 434 435 436 437 438 439 440 441 442 443 444 445 446 447 448 449 450 451 452 453 454 '
        '455 460 461 462 463 464 465 466 467 468 469 470 471 472 473 474 475 476 477 478 479 480 481 482 483 '
        '484 485 486 487 488 489 490 491 492 493 494 495 496 497 498 499 500 501 502 504 505 506 507 508 514 '
        '515 516 517 518 520 521 522 523 524 525 526 527 528 529 530 531 532 533 534 535 536 537 538 539 540 '
        '541 542 543 544 545 549 557 560 566 567 568 569 570 571 572 573 577 580 586 587 588 591 597 600 601 '
        '602 607 610 617 623 626 628 633 636 638 643 646 648 664 671 674 675 678 680 684 685 688 690 695 699 '
        '704 708 712 715 768 772 779 780 783 785 789 790 791 794 800 803 805 809 810 811 814 820 823 825 834 '
        '840 843 845 850 853 855 860 863 865 871 879 882 884 888 889 890 892 899 902 904 909 912 914 928 929 '
        '930 932 933 934 938 939 940 943 948 949 950 951 952 953 954 957 958 963 964 967 969 973 974 983 984 '
        '985 986 989 1008 1056 1076 1096 1111 1140 1150 1151 1152 1154 1155 1160 1161 1163 1170 1171 1172 '
        '1173 1176 1235 1245 1246 1247 1248 1280 1305 1477 1512 1637 1638 1639 1860 1895 2092 2127 2202 2203 '
        '2205 3184 3698 3733 3768 3838 3853 3854 3855 3894 3909 3910 3911 3965 3966 3968 3971 4041 4116 4361 '
        '4417 4543 4599 4872 4893 4894 4895 5468 6034 6035 6209 6265 6661 6717 6773 6829 6830 6864 6920 7228 '
        '7249 7250 7445 8617 8618 '
    ).split())),
    (2, 2, 8, 10): tuple(map(int,(
        '0 1 2 3 4 5 6 7 8 9 10 11 13 14 15 16 17 18 19 20 21 22 23 24 25 26 27 28 29 30 31 33 34 35 36 37 38 '
        '39 40 41 42 43 44 45 46 47 48 49 50 51 52 53 54 55 56 57 58 59 60 61 62 63 64 69 70 71 72 73 74 75 '
        '76 78 79 80 81 82 83 84 85 86 88 89 90 91 92 93 94 95 96 98 101 102 104 105 106 107 109 110 111 112 '
        '113 114 115 116 117 118 119 120 121 122 123 124 125 126 127 128 129 137 138 139 140 141 142 143 144 '
        '145 147 148 149 150 151 152 153 154 155 156 157 158 159 160 161 162 163 164 165 166 167 168 169 170 '
        '171 172 173 174 176 178 179 180 181 182 184 185 186 187 188 189 190 191 192 193 194 195 196 197 198 '
        '199 200 201 202 204 205 206 207 208 209 210 211 212 213 214 215 216 217 218 219 220 221 222 223 224 '
        '225 226 227 228 229 230 231 233 235 236 237 238 239 240 241 242 247 248 249 250 251 252 253 254 255 '
        '256 257 258 259 260 261 262 263 264 265 266 267 268 269 270 271 272 273 274 275 276 277 278 283 284 '
        '285 286 287 288 289 290 292 293 294 295 296 297 298 300 302 303 304 305 306 307 308 309 310 312 313 '
        '314 316 317 318 319 320 321 323 324 325 326 327 328 329 330 332 333 334 335 336 337 338 339 340 342 '
        '343 344 345 346 347 348 349 350 352 353 355 356 357 361 362 363 366 367 368 369 370 371 372 373 374 '
        '375 376 377 378 396 397 398 399 400 402 403 404 405 406 407 408 409 410 411 412 413 414 415 416 417 '
        '418 419 420 421 422 423 424 425 426 427 428 429 431 433 434 435 436 437 439 440 441 442 443 444 445 '
        '446 447 448 449 450 451 452 453 454 455 456 457 458 459 460 461 462 463 464 465 466 468 470 471 472 '
        '473 478 479 480 481 482 483 484 485 486 487 492 493 494 495 496 498 499 500 501 502 503 504 505 506 '
        '507 508 509 510 511 512 513 514 515 516 517 518 519 520 521 522 523 524 525 527 529 530 531 532 533 '
        '534 535 536 541 542 543 544 545 546 547 548 549 550 551 552 553 554 555 556 557 558 559 560 561 562 '
        '563 564 565 566 567 568 570 571 572 573 575 577 578 579 580 581 582 583 584 585 586 587 588 589 590 '
        '591 592 593 594 595 596 601 602 603 604 605 606 607 608 613 614 615 616 617 618 619 620 622 623 624 '
        '625 626 627 628 630 632 633 634 635 636 637 638 639 640 642 643 644 646 647 648 649 650 651 653 654 '
        '655 656 657 658 659 660 662 663 664 665 666 667 668 670 672 673 674 675 676 677 678 679 680 682 684 '
        '686 687 688 689 690 691 692 693 695 696 697 698 699 700 701 702 703 705 706 707 708 709 710 716 717 '
        '718 719 729 730 731 737 738 739 740 741 742 743 744 745 746 747 748 750 751 752 753 754 762 763 764 '
        '765 766 768 769 1106 1107 1110 1126 1127 1130 1133 1146 1150 1166 1206 1226 1246 1266 1296 1416 1417 '
        '1420 1516 1571 1731 1881 1981 2016 2470 '
    ).split())),
    (3, 2, 8): tuple(map(int,(
        '0 1 2 3 4 5 6 7 8 9 10 11 12 13 14 15 16 17 18 19 20 21 22 23 24 25 26 27 28 29 30 31 32 33 34 35 36 '
        '37 38 39 40 41 42 43 44 45 46 47 48 49 50 51 52 53 54 55 56 57 58 59 60 61 62 63 64 65 66 67 68 69 '
        '70 71 72 73 74 75 76 77 78 79 80 81 82 83 84 85 86 87 88 89 90 91 92 93 94 95 96 97 98 99 100 101 '
        '102 103 104 105 106 107 108 109 110 111 112 113 114 115 116 117 118 119 120 121 122 123 124 125 126 '
        '127 128 129 130 131 132 133 134 135 136 137 138 139 140 141 142 143 144 145 146 147 148 149 150 151 '
        '152 153 154 155 156 157 158 159 160 161 162 163 164 165 166 167 168 169 170 171 172 173 174 175 176 '
        '177 178 179 180 181 182 183 184 185 186 187 188 189 190 191 192 193 194 195 196 197 198 199 200 201 '
        '202 203 204 205 206 207 208 209 210 211 212 213 214 215 216 217 218 219 220 221 222 223 224 225 226 '
        '227 228 229 230 231 232 233 234 235 236 237 238 239 240 241 242 243 244 245 246 247 248 249 250 251 '
        '252 253 254 255 256 257 258 259 260 261 262 263 264 265 266 267 268 269 270 271 272 273 274 275 276 '
        '277 278 279 280 281 282 283 284 285 286 287 288 289 290 291 292 293 294 295 296 297 298 299 300 301 '
        '302 303 304 305 306 307 308 309 310 311 312 313 314 315 316 317 318 319 320 321 322 323 324 325 326 '
        '327 328 329 330 331 332 333 334 335 336 337 338 339 340 341 342 343 344 345 346 347 348 349 350 351 '
        '352 353 354 355 356 357 358 359 360 361 362 363 364 365 366 367 368 369 370 371 372 373 374 375 376 '
        '377 378 379 380 381 382 383 384 385 386 387 388 389 390 391 392 393 394 395 396 397 398 399 400 401 '
        '402 403 404 405 406 407 408 409 410 411 412 413 414 415 416 417 418 419 420 421 422 423 424 425 426 '
        '427 428 429 430 431 432 433 434 439 440 444 445 446 447 453 454 455 456 457 458 459 460 461 463 468 '
        '469 472 473 477 478 479 481 482 486 487 493 497 505 509 513 517 522 525 526 529 530 531 536 540 543 '
        '544 545 550 554 558 561 562 563 568 571 572 573 578 582 585 586 589 590 591 599 603 607 613 617 621 '
        '622 625 627 631 635 636 643 647 651 655 656 661 665 666 672 676 680 684 688 689 694 698 699 707 711 '
        '715 721 725 729 730 735 739 743 744 751 755 759 763 764 765 769 773 774 780 784 788 792 796 797 802 '
        '806 807 812 816 817 822 826 834 838 839 844 848 849 854 858 859 864 868 869 874 886 890 891 895 896 '
        '900 901 905 908 909 916 920 921 926 930 931 935 938 939 946 954 958 959 964 968 969 974 978 979 983 '
        '986 987 994 998 999 1003 1006 1007 1014 1018 1022 1027 1030 1031 1038 1042 1043 1058 1062 1067 1070 '
        '1071 1560 1580 1600 1670 1690 1786 1793 1814 1834 2014 2034 2044 2351 2482 2488 2745 2800 '
    ).split())),
}


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--part', choices=('all', 'profiles', 'finite', 'curves', 'sign'), default='all')
    part = parser.parse_args().part
    orientations = list(cases())
    counts = Counter((u, len(fields(u, f, o)[1])) for u, f, o in orientations)
    assert counts == {(2,3):224, (2,2):68, (2,0):3, (3,3):16, (3,2):8, (3,0):1}
    print('Rank-three oriented profiles:', len(orientations), flush=True)
    if part in ('all', 'finite'):
        finite = Counter()
        for u, f, o in orientations:
            ag, pairs, *_ = low_data(u, f, o)
            if len(pairs) < len(ag[0])-1:
                continue
            tag, size = finite_case(u, f, o)
            assert tag in ('excluded', 'tangent'), (u, f, o, tag, size)
            finite[tag] += 1
        assert finite == {'excluded':52, 'tangent':196}
        print('Finite cases:', dict(finite), flush=True)
    if part in ('all', 'curves'):
        curve = Counter()
        for u, f, o in orientations:
            if u != 2 or len(fields(u, f, o)[1]) != 2:
                continue
            charts = curve_models(f, o)
            if not charts:
                tag, size = dependent_case(f, o)
                assert tag in ('pencil','excluded'), (f, o, tag, size)
                curve['dependent '+tag] += 1
                continue
            for chart in charts:
                if chart is None:
                    curve['zero required factor'] += 1
                    continue
                result = trial_low(chart, o, 65521, 2)
                if result[0] == 'excluded':
                    curve['coprime norms'] += 1
                    continue
                assert result[-1] and result[-2] == [65520,1]
                assert has_common_endpoint_factor(chart)
                curve['excluded endpoint'] += 1
        assert curve == {'dependent pencil':13, 'dependent excluded':7,
                         'zero required factor':20, 'coprime norms':16, 'excluded endpoint':32}
        print('Curve branches:', dict(curve), flush=True)
    if part in ('all', 'sign'):
        tested = 0
        for u, f, o in orientations:
            if fields(u,f,o)[1]:
                continue
            tag, steps, _ = verify_sign(u, f, 14, 16)
            assert tag == 'excluded' and steps[-1][-1] == 0
            print('All-sign case', (u,*f), 'exact dual dimension', steps[0][1], 'to zero', flush=True)
            tested += 1
        assert tested == 4

if __name__ == '__main__':
    main()
