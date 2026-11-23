"""Verify the two-parameter Gram proof for three distinct high-row columns."""
import argparse
from collections import Counter
from fractions import Fraction
from functools import reduce
from itertools import product
from math import factorial,gcd
import numpy as np
import verify_full_rows as full
from verify_sparse_rows import shapes, options, raw_mac, multiply

def zsum(zs):
    return full.add_many(list(zs))

def zzadd(a,b):
    return a[0]+b[0],a[1]+b[1]


def open_restrict(M, forms):
    p = full.PIVOT
    root = full.sqrt_i(p)
    for f in forms:
        h = full.normalize(zsum((full.scale(c, m) for (c, m) in zip(f, M))))
        for j in range(len(h[0]).bit_length() + 1):
            if not full.nonzero(h):
                return None
            d = len(h[0])
            m0 = np.array((h[0] + root * h[1]) % p, dtype=np.int64)
            (rows, cols, _) = full.rref(m0.tolist(), d, p)
            if len(rows) == d:
                break
            if not rows:
                raise ValueError('bad reduction')
            U = (h[0][rows, :], h[1][rows, :])
            (det, adj) = full.adjugate((U[0][:, cols], U[1][:, cols]))

            def repr(a):
                v = full.mul((a[0][:, cols], a[1][:, cols]), adj)
                b = full.mul(v, U)
                c = full.scale(det, a)
                if not (np.array_equal(b[0], c[0]) and np.array_equal(b[1], c[1])):
                    raise ValueError('bad rank certificate')
                return v
            repr(h)
            MM = [full.scale((det[0], -det[1]), repr(full.mul(U, m))) for m in M]
            div = reduce(gcd, (v for z in MM for m in z for v in m.flat), 0)
            M = [(a // div, b // div) for (a, b) in MM]
            h = full.normalize(zsum((full.scale(c, m) for (c, m) in zip(f, M))))
    return M


def base(E, pp):
    V = np.array([[full.G[e] for e in row] for row in E[:3]])
    sh = list(zip(*E[:3]))
    un = list(dict.fromkeys(sh))
    ids = [sh.index(v) for v in un]
    sizes = [sh.count(v) for v in un]
    n = len(un)
    row = V[:, ids]
    forms = [list(map(full.zz, r)) for r in row] + [[(int(j == k), 0) for j in range(n)] for (k, v) in enumerate(sizes) if v == 1]
    poly = []
    for (tag, i, k, B, C, o) in pp:
        if tag == 'sign':
            forms.extend([list(map(full.zz, row[i] + row[k])), list(map(full.zz, row[i] - row[k]))])
            continue
        b = np.array([int(j in B) for j in ids])
        c = np.array([int(j in C) for j in ids])
        a = (1 - b - c) * row[k]
        b = b * row[k]
        c = c * row[k]
        gam = -1j if o else 1j
        q = np.outer(a, a) - np.outer(b, b) + np.outer(c, c) - 2 * (1 + gam) * np.outer(b, c)
        g = {}
        for j in range(n):
            for l in range(j, n):
                x = q[j, l] if j == l else q[j, l] + q[l, j]
                if x:
                    g[tuple((int(t == j) + int(t == l) for t in range(n)))] = x
        poly.append(g)
    d = n + 1
    (a, b) = raw_mac(n, d, poly)
    vf = full.lift(a, b, full.EXTENDED)
    if vf is None:
        return ('lift', None)
    K = vf[0]
    while K and d >= 2:
        (M, msg) = full.multiplication(K, n, d)
        if M is not None:
            N = open_restrict(M, forms)
            if N is None:
                return ('empty', None)
            return ('spectrum', N)
        (K, _) = full.shrink(K, n, d, forms)
        d -= 1
        if K is None:
            return ('shrink-failed', None)
    return ('empty' if not K else 'positive', None)


def gaussmul(A, B):
    (ar, ai) = A
    (br, bi) = B
    return (ar @ br - ai @ bi, ar @ bi + ai @ br)


def grams(E, pp, M, t, u):
    d = len(M[0][0])
    I = np.eye(d, dtype=object)
    Z = np.zeros_like(I)
    keys = list(zip(*E[:3]))
    un = list(dict.fromkeys(keys))
    W = [None] * 5
    pars = [t, u]
    for (key, m) in zip(un, M):
        js = [j for (j, v) in enumerate(keys) if v == key]
        n = len(js)
        c = 6 // n
        for j in js:
            W[j] = (c * m[0], c * m[1])
        for j in js[1:]:
            v = pars.pop() * I
            W[j] = (W[j][0] + v, W[j][1])
            W[js[0]] = (W[js[0]][0] - v, W[js[0]][1])
    V = [[full.scale(full.zz(full.G[e]), w) for (e, w) in zip(es, W)] for es in E[:3]]
    s = [zsum(r) for r in V]
    F = np.zeros((8, 4, 5, 2, d, d), dtype=object)
    for i in range(3):
        F[i, i] = V[i]
    F[3, 3, 0, 0] = I
    for (n, (tag, i, k, B, C, o)) in enumerate(pp, 4):
        if tag == 'sign':
            for j in range(5):
                F[n, i, j] = full.scale((-1, 0), gaussmul(s[k], V[k][j]))
                F[n, k, j] = gaussmul(s[i], V[i][j])
        else:
            for j in B:
                F[n, i, j] = gaussmul(s[k], V[i][j])
            for j in C:
                F[n, k, j] = gaussmul(s[i], V[k][j])
    F[7, :, :, 0] = I
    K = np.kron(3 * np.eye(4, dtype=int) - 1, 4 * np.eye(5, dtype=int) - 1)
    F = F.reshape(8, 20, 2, d, d)
    Kbig = np.kron(K, I)
    L = F.transpose(2, 0, 3, 1, 4).reshape(2, 8 * d, 20 * d)
    R = F.transpose(2, 1, 3, 0, 4).reshape(2, 20 * d, 8 * d)
    return gaussmul((L[0] @ Kbig, L[1] @ Kbig), R)


def cofactors(G, d):
    I = np.eye(8 * d, dtype=object)
    Z = np.zeros_like(I)
    B = (I, Z)
    for k in range(1, 8):
        H = gaussmul(G, B)
        B = tuple((k * h - np.kron(np.eye(8, dtype=object), np.einsum('iaib->ab', h.reshape(8, d, 8, d))) for h in H))
    return np.array(B, dtype=object).reshape(2, 8, d, 8, d).transpose(1, 3, 0, 2, 4)


def interpolate_axis(vals):
    d = len(vals) - 1
    out = np.zeros_like(vals)
    v = vals
    fall = [1]
    for k in range(d + 1):
        z = v[0]
        den = factorial(k)
        assert not np.any(z % den)
        w = z // den
        for (j, h) in enumerate(fall):
            out[j] += h * w
        v = v[1:] - v[:-1]
        fall = multiply(fall, [-k, 1])
    return out


def polynomial_blocks(E,pp,M):
    for a in M:
        for b in M:
            c=gaussmul(a,b);q=gaussmul(b,a)
            assert all(np.array_equal(x,y)for x,y in zip(c,q))
    d=len(M[0][0]);n=6
    S=np.array([[cofactors(grams(E,pp,M,t,u),d)for u in range(n+1)]for t in range(n+1)],dtype=object)
    Q=interpolate_axis(interpolate_axis(S).swapaxes(0,1)).swapaxes(0,1)
    for t,u in ((7,8),(9,-2)):
        val=sum(t**i*u**j*Q[i,j]for i in range(7)for j in range(7))
        assert np.array_equal(val,cofactors(grams(E,pp,M,t,u),d))
    return Q


def weight_polys(E, M):
    sh = list(zip(*E[:3]))
    un = list(dict.fromkeys(sh))
    d = len(M[0][0])
    I = np.eye(d, dtype=object)
    Z = np.zeros_like(I)
    out = [None] * 5
    params = [(1, 0), (0, 1)]
    for (key, m) in zip(un, M):
        js = [j for (j, v) in enumerate(sh) if v == key]
        q = 6 // len(js)
        for j in js:
            out[j] = {(0, 0): (q * m[0], q * m[1])}
        for j in js[1:]:
            z = params.pop()
            out[js[0]][z] = (-I, Z)
            out[j][z] = (I, Z)
    return out


def times2(a, b):
    out = {}
    for ((i, j), M) in a.items():
        for ((s, t), N) in b.items():
            z = (i + s, j + t)
            q = gaussmul(M, N)
            if z in out:
                q = zzadd(out[z], q)
            out[z] = q
    return {k: v for (k, v) in out.items() if full.nonzero(v)}


def pivots_np(A, p):
    ids = list(range(len(A)))
    A = A.copy()
    pivs = []
    rows = []
    for j in range(A.shape[1]):
        k = len(rows)
        loc = np.flatnonzero(A[k:, j])
        if not len(loc):
            continue
        l = k + int(loc[0])
        A[[k, l]] = A[[l, k]]
        (ids[k], ids[l]) = (ids[l], ids[k])
        A[k] = A[k] * pow(int(A[k, j]), -1, p) % p
        f = A[:, j].copy()
        f[k] = 0
        A = (A - f[:, None] * A[k]) % p
        rows.append(ids[k])
        pivs.append(j)
    return (rows, pivs, A[:len(rows)])


def spanopen(Q, E, M, degree, target):
    n = Q.shape[-1]
    items = []
    p = 65521
    r = full.sqrt_i(p)
    for a in range(8):
        for b in range(a + 1):
            for k in range(n):
                P = Q[:, :, a, b, :, :, k]
                nz = np.argwhere(np.any(P != 0, axis=(2, 3)))
                if not len(nz):
                    continue
                deg = max((int(i + j) for (i, j) in nz))
                div = reduce(gcd, map(int, P.flat), 0)
                items.append((deg, [(int(i), int(j), P[i, j] // div) for (i, j) in nz]))
    ws = weight_polys(E, M)
    I = np.eye(n, dtype=object)
    Z = np.zeros_like(I)
    unit = {(0, 0): (I, Z)}
    targets = [('unit', unit)]
    prod = unit
    for (j, w) in enumerate(ws):
        if len(w) > 1:
            targets.append((str(j), w))
            prod = times2(prod, w)
    targets += [('product', prod)]
    for e in (2, 3, 4):
        targets += [(tag + '^' + str(e), reduce(times2, [w] * e)) for (tag, w) in targets.copy() if '^' not in tag and tag != 'unit']
    for d in [degree]:
        mons = [(i, j) for i in range(d + 1) for j in range(d - i + 1)]
        idx = {z: i for (i, z) in enumerate(mons)}
        rows = []
        for (deg, pts) in items:
            for i in range(d - deg + 1):
                for j in range(d - deg - i + 1):
                    A = np.zeros((2, len(mons), n), dtype=object)
                    for (s, t, c) in pts:
                        A[:, idx[s + i, t + j]] = c
                    rows.append(A.reshape(2, -1))
        if not rows:
            continue
        xx = np.array(rows, dtype=object)
        (re, im) = (xx[:, 0], xx[:, 1])
        cols = re.shape[1]
        A = np.asarray((re + r * im) % p, dtype=np.int64)
        (rr, cc, red) = pivots_np(A, p)
        X = (re[rr, :], im[rr, :])
        inv = None
        for (tag, w) in targets:
            if tag != target:
                continue
            if any((z not in idx for z in w)):
                continue
            goal = np.zeros((2, n, len(mons), n), dtype=object)
            for (z, g) in w.items():
                goal[:, :, idx[z], :] = np.array(g).transpose(0, 2, 1)
            goal = goal.reshape(2, n, cols)
            gm = np.asarray((goal[0] + r * goal[1]) % p, dtype=np.int64)
            if np.any((gm - gm[:, cc] @ red) % p):
                continue
            if inv is None:
                inv = full.adjugate((X[0][:, cc], X[1][:, cc]))
            (det, adj) = inv
            Y = gaussmul((goal[0][:, cc], goal[1][:, cc]), adj)
            test = gaussmul(Y, X)
            dest = full.scale(det, (goal[0], goal[1]))
            if np.array_equal(test[0], dest[0]) and np.array_equal(test[1], dest[1]):
                return (d, len(rr), tag)
    return None


HINTS = {
    (1, 0): (6, 'unit'),
    (1, 2): (6, 'unit'),
    (1, 3): (6, 'unit'),
    (4, 0): (6, 'unit'),
    (4, 3): (6, 'unit'),
    (21, 0): (9, 'unit'),
    (21, 1): (8, 'product^2'),
    (21, 2): (9, 'product^2'),
    (21, 3): (9, 'unit'),
    (36, 0): (11, 'unit'),
    (36, 2): (9, 'product^2'),
    (36, 3): (11, 'unit'),
    (46, 0): (10, 'unit'),
    (46, 1): (8, 'product^2'),
    (46, 3): (10, 'unit'),
    (124, 0): (4, 'unit'),
    (124, 1): (4, 'unit'),
    (124, 3): (4, 'unit'),
    (144, 0): (8, 'unit'),
    (144, 1): (8, 'product'),
    (144, 3): (8, 'unit'),
    (176, 0): (4, 'unit'),
    (176, 3): (4, 'unit'),
    (198, 0): (4, 'unit'),
    (198, 1): (4, 'unit'),
    (198, 3): (4, 'unit'),
    (202, 0): (8, 'unit'),
    (202, 1): (8, 'product'),
    (202, 2): (8, 'product'),
    (202, 3): (8, 'unit'),
}


def main():
    parser=argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--shard',nargs=2,type=int,default=[0,1],metavar=('INDEX','COUNT'))
    args=parser.parse_args();idx,tot=args.shard
    assert tot>0 and 0<=idx<tot
    selected=[(s,options(1,s))for s in shapes(1)if options(1,s) is not None]
    counts=Counter();orient=0;eligible=Counter()
    for id,(sh,(E,opts))in enumerate(selected):
        if len(set(tuple(x[:2])for x in sh))!=3:continue
        genuine=sum(z[0][0]=='three'for z in opts[:3])
        for o,pp in enumerate(product(*opts[:3])):
            eligible[genuine]+=1
            if genuine==0:continue
            use=orient%tot==idx;orient+=1
            if not use:continue
            tag,M=base(E,pp)
            if genuine==3:
                assert tag=='empty'
                counts['three-ratio aggregate exclusions']+=1;continue
            if tag=='empty':
                counts['empty']+=1;continue
            assert tag=='spectrum'
            d,goal=HINTS[id,o]
            result=spanopen(polynomial_blocks(E,pp,M),E,M,d,goal)
            assert result is not None,(id,o)
            counts[result[-1]]+=1
            print('orientation',id,o,'certificate',result,flush=True)
    assert eligible=={0:4,2:40,3:64}
    if tot==1:assert sum(counts.values())==104 and counts['empty']==10 and counts['three-ratio aggregate exclusions']==64
    print('verified',dict(counts),'orientations',sum(counts.values()),flush=True)

if __name__=='__main__':
    main()
