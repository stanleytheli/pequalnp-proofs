"""Exact rational controls for the numerical tree bounds; standard library only."""
from fractions import Fraction
from itertools import product, combinations
from math import comb, ceil, sqrt
from random import Random


def cheb(d, x):
    a, b = 1, x
    for _ in range(d):
        a, b = b, 2*x*b-a
    return a


def symmetric_coefficients(g, epsilon):
    d = 1
    center = Fraction(g+1,g-1)
    while cheb(d,center) < 2/epsilon:
        d += 1
    values = [1-cheb(d,Fraction(g+1-2*w,g-1))/cheb(d,center) for w in range(g+1)]
    coeffs = []
    diff = values
    while diff:
        coeffs.append(diff[0])
        diff = [b-a for a,b in zip(diff,diff[1:])]
    assert not coeffs[0] and all(c==0 for c in coeffs[d+1:])
    assert all(abs(values[w]-int(w>0)) <= epsilon*int(w>0)/2 for w in range(g+1))
    assert all(sum(comb(w,j)*coeffs[j] for j in range(w+1))==values[w] for w in range(g+1))
    assert sum(comb(g,j)*abs(c) for j,c in enumerate(coeffs)) <= 1+15**d
    return d,coeffs


def rank(matrix, modulus):
    m=[r[:] for r in matrix]
    n=len(m)
    rk=0
    for j in range(n):
        pivot=next((i for i in range(rk,n) if m[i][j]%modulus),None)
        if pivot is None:
            continue
        m[rk],m[pivot]=m[pivot],m[rk]
        inv=pow(m[rk][j],-1,modulus)
        for i in range(rk+1,n):
            scale=m[i][j]*inv%modulus
            m[i]=[(a-scale*b)%modulus for a,b in zip(m[i],m[rk])]
        rk+=1
    return rk


def check_support():
    rng=Random(47)
    for k in range(7):
        n=2**k
        for p in (2,3,7,101):
            matrix=[[rng.randrange(1,p) if not a&~b else 0 for b in range(n)] for a in range(n)]
            perm=list(range(n))
            rng.shuffle(perm)
            row_shuffle=[matrix[i] for i in perm]
            rng.shuffle(perm)
            assert rank([[row[j] for j in perm] for row in row_shuffle],p)==n


def check_pattern():
    for t in (1,2,3):
        for z in product((0,1),repeat=2*t):
            bits=tuple(i for bit in z for i in (bit,1-bit))
            for choice in product(range(4),repeat=t):
                selected=any((z[2*j+c//2]^(c%2)) for j,c in enumerate(choice))
                overlap=any(bits[4*j+c] for j,c in enumerate(choice))
                assert overlap==selected


def check_physical():
    # A triangle of paths with an interior bit each. Endpoints are actually shared.
    g=3
    _,coeffs=symmetric_coefficients(g,Fraction(1,3))
    edges=((0,1),(1,2),(2,0))
    probs=[Fraction(i,7) for i in range(1,7)]
    target=approx=Fraction(0)
    for x in product((0,1),repeat=6):
        flags=[x[minterior+3] and (x[left] or x[right]) for minterior,(left,right) in enumerate(edges)]
        y=sum(c*sum(all(flags[i] for i in S) for S in combinations(range(g),j)) for j,c in enumerate(coeffs))
        w=Fraction(1)
        for b,p in zip(x,probs): w*=p if b else 1-p
        target+=w*any(flags)
        approx+=w*y
    assert abs(target-approx)<=target/3
    print(f'shared-root Bernoulli interpolation: target={target}, approximation={approx}')


if __name__=='__main__':
    for g in [2,3,4,7,12,20,40,100]:
        d,_=symmetric_coefficients(g,Fraction(1,3))
        print(f'{g} path indicators, Chebyshev degree {d}, all weights and coefficient masses checked')
    check_support(); check_pattern(); check_physical()
    print('28 support-pattern ranks and all 4-coordinate pattern embeddings through three blocks verified')
