"""Reproduce the complex full-row obstruction for the 4 by 5 permanent.

Requires Python 3.10 or newer and NumPy. Uses no network, input data files,
floating-point root solvers or third-party computer algebra systems.
All decision branches use exact integer arithmetic, finite fields, Gaussian
rational linear algebra or bounded Gaussian integers represented exactly.
See full-row-obstruction.md for the mathematical argument.
"""
import argparse
from collections import Counter
from fractions import Fraction
from functools import lru_cache, reduce
from itertools import permutations, product
from math import gcd, isqrt, lcm
from random import Random
from time import monotonic

import numpy as np

if not __debug__:
    raise RuntimeError("Run this verifier with Python assertions enabled.")

PIVOT = 1_000_000_009
PRIMES = (PIVOT, 998244353, 2013265921)
EXTENDED = (*PRIMES, 469762049, 167772161, 1224736769, 754974721)
G = (1, 1j, -1, -1j)
phase_values = (*G, 0)
p = 17
points = tuple(product(range(4), repeat=3))
s4 = tuple(permutations(range(4)))
PROFILES = ((1,4,2),(1,3,3),(0,4,3),(1,2,4),(0,3,4),(1,1,5),(0,2,5),(1,0,6),(0,1,6))

def zz(value):
    return int(value.real), int(value.imag)


# The finite phase profiles and their linear constraints


def relative_rows():
    rows=[(0,*p) for p in product(range(4), repeat=4)]
    def okay(a,b):
        q={(i-j)%4 for i,j in zip(a,b)}
        return len(q)==3 or q=={0,2}
    r0=rows.pop(0);rows=[a for a in rows if okay(r0,a)]
    adj=[{k for k,b in enumerate(rows[:i]) if okay(a,b)} for i,a in enumerate(rows)]
    for i,a in enumerate(rows):
        for j in adj[i]:
            for k in adj[j]&adj[i]:
                rr=(r0,a,rows[j],rows[k])
                yield tuple(sorted(16*x[1]+4*x[2]+x[3] for x in zip(*rr)))

def orbit(v):
    rows=[(0,*points[i]) for i in v]
    for r in s4:
        aa=[tuple((p[i]-p[r[0]])%4 for i in r[1:]) for p in rows]
        for b in set(aa):
            yield tuple(sorted(((u[0]-b[0])%4)*16+((u[1]-b[1])%4)*4+((u[2]-b[2])%4) for u in aa))

def edges(cols):
    p=[(0,*points[k]) for k in cols]
    e=[]
    for i in range(4):
        for j in range(i):
            v={((u[i]-u[j])%4) for u in p}
            if len(v) in (1,4) or len(v)==2 and len({x%2 for x in v})==2:return None
            e.append(len(v))
    return tuple(e)

def relations(shape,orient):
    n=len(shape);phase=[[(0,z//16,z//4%4,z%4)[i] for z in shape] for i in range(4)]
    pairs=[];j0=0
    for i in range(4):
        for k in range(i):
            vv=[(phase[i][j]-phase[k][j])%4 for j in range(n)]
            vals=set(vv)
            if len(vals)<3:continue
            center=next(x for x in vals if (x+2)%4 not in vals)
            sign=orient>>j0&1;j0+=1
            B=(center+1+2*sign)%4;C=(center+3+2*sign)%4
            pairs.append((i,k,[q if rel==B else -1 for q,rel in zip(phase[k],vv)],[q if rel==C else -1 for q,rel in zip(phase[k],vv)]))
    return phase,pairs

@lru_cache(None)
def exponents(d,n):
    if n==1:return ((d,),)
    return tuple((i,*u) for i in range(d,-1,-1) for u in exponents(d-i,n-1))

def rref(A,n,mod):
    a=[r.copy() for r in A];ids=list(range(len(a)));pivs=[];rows=[]
    for j in range(n):
        h=len(pivs);u=next((k for k in range(h,len(a)) if a[k][j]),None)
        if u is None:continue
        a[h],a[u]=a[u],a[h];ids[h],ids[u]=ids[u],ids[h]
        iv=pow(a[h][j],-1,mod);a[h]=[z*iv%mod for z in a[h]]
        for k,row in enumerate(a):
            if k!=h and row[j]:
                t=row[j];a[k]=[(x-t*y)%mod for x,y in zip(row,a[h])]
        pivs.append(j);rows.append(ids[h])
    null=[]
    for j in range(n):
        if j in pivs:continue
        q=[0]*n;q[j]=1
        for i,k in enumerate(pivs):q[k]=-a[i][j]%mod
        null.append(q)
    return rows,pivs,null

@lru_cache(None)
def det_plan(n):
    return [(v,-1 if sum(v[i]>v[j] for i in range(n) for j in range(i+1,n))%2 else 1) for v in permutations(range(n))]

def det(mat):
    s=0
    for perm,sign in det_plan(len(mat)):
        e=sign
        for i,j in enumerate(perm):e*=mat[i][j]
        s+=e
    return s

def gmul(z,w):
    a,b=z;c,d=w;return a*c-b*d,a*d+b*c

def gmdiv(z,w):
    if w==(1,0):return z
    a,b=z;c,d=w;t=c*c+d*d
    u,r=divmod(a*c+b*d,t);v,s=divmod(b*c-a*d,t)
    assert r==s==0
    return u,v

def exact_rank(A,n):
    M=[[zz(x) for x in row] for row in A];r=0;old=(1,0)
    for j in range(n):
        k=next((i for i in range(r,len(M)) if M[i][j]!=(0,0)),None)
        if k is None:continue
        M[r],M[k]=M[k],M[r];piv=M[r][j]
        for i in range(r+1,len(M)):
            q=M[i][j]
            for t in range(j+1,n):
                a,b=gmul(piv,M[i][t]);c,d=gmul(q,M[r][t]);M[i][t]=gmdiv((a-c,b-d),old)
            M[i][j]=(0,0)
        old=piv;r+=1
        if r==len(M):break
    return r

def restricted_Q(pair,ph,kern,gamma):
    i,k,b,c=pair;lo=ph[k]
    a=[x if y==z==-1 else -1 for x,y,z in zip(lo,b,c)]
    linear=[[sum(phase_values[z]*x for z,x in zip(cs,v)) for v in kern] for cs in (a,b,c)]
    aa,bb,cc=linear;r=len(kern);ts={}
    for i in range(r):
        for j in range(i,r):
            sym=1 if i==j else 2
            coeff=sym*(aa[i]*aa[j]-bb[i]*bb[j]+cc[i]*cc[j])-(1+gamma)*sym*(bb[i]*cc[j]+bb[j]*cc[i])
            exp=tuple(int(k==i)+int(k==j) for k in range(r))
            if coeff:ts[exp]=coeff
    return ts

# Exact homogeneous Macaulay kernels


@lru_cache(None)
def monomials(n,d):return exponents(d,n),{e:i for i,e in enumerate(exponents(d,n))}

def ideal_matrix(shape,orient,d):
    n=len(shape);ph,pairs=relations(shape,orient)
    basis=tuple(tuple(int(i==j) for j in range(n)) for i in range(n))
    es,ei=monomials(n,d);cols=len(es);Eas=exponents(d-2,n)
    A=np.zeros((len(pairs)*len(Eas),cols),np.complex128)
    for k,qs in enumerate(pairs):
        q=restricted_Q(qs,ph,basis,-1j if orient>>k&1 else 1j)
        for j,e in enumerate(Eas):
            for a,v in q.items():
                b=tuple(x+y for x,y in zip(e,a));A[k*len(Eas)+j,ei[b]]=v
    return A.real.astype(np.int64),A.imag.astype(np.int64),ph,pairs

def get_kernel(a,p):
    n=a.shape[1];piv=[]
    for col in range(n):
        h=len(piv);sel=np.flatnonzero(a[h:,col])
        if not len(sel):continue
        j=h+int(sel[0]);a[[h,j]]=a[[j,h]];iv=pow(int(a[h,col]),-1,p)
        a[h,col:]=a[h,col:]*iv%p
        sub=a[h+1:,col:];v=sub[:,0].copy()
        if len(v):sub[:]=(sub-v[:,None]*a[h,col:])%p
        piv.append(col)
    free=np.array([j for j in range(n) if j not in piv],int)
    N=np.zeros((len(free),n),dtype=np.int64)
    N[np.arange(len(free)),free]=1
    for k in range(len(piv)-1,-1,-1):
        j=piv[k]
        # Accumulate in blocks to keep large modular fields inside signed int64.
        terms=(N[:,j+1:]*a[k,j+1:])%p
        N[:,j]=-terms.sum(1)%p
    return free,N

def sqrt_i(p):
    return next(v for a in range(2,100) for v in [pow(a,(p-1)//4,p)] if v*v%p==p-1)

@lru_cache(maxsize=65536)
def fraction(v,m):
    if v==0:return Fraction(0)
    bound=isqrt(m//2);u0,u1=m,v;v0,v1=0,1
    while u1>bound:
        k=u0//u1;u0,u1=u1,u0-k*u1;v0,v1=v1,v0-k*v1
    if abs(v1)>bound or gcd(u1,v1)!=1:return None
    return Fraction(u1,v1)

def lift(A,B,primes):
    residues=None;mod=1;oldfree=None
    for p in primes:
        r=sqrt_i(p);ka,na=get_kernel((A+r*B)%p,p);kb,nb=get_kernel((A-r*B)%p,p)
        if not np.array_equal(ka,kb) or oldfree is not None and not np.array_equal(ka,oldfree):continue
        oldfree=ka
        rr=(na+nb)*pow(2,-1,p)%p;ii=(na-nb)*pow(2*r%p,-1,p)%p
        cur=[(int(x),int(y)) for x,y in zip(rr.flat,ii.flat)]
        if residues is None:residues=cur
        else:
            u=pow(mod,-1,p)
            residues=[(a+mod*((x-a)*u%p),b+mod*((y-b)*u%p)) for (a,b),(x,y) in zip(residues,cur)]
        mod*=p
        z=[(fraction(a,mod),fraction(b,mod)) for a,b in residues]
        if any(a is None or b is None for a,b in z):continue
        exact=[];cols=A.shape[1]
        for j in range(len(ka)):
            row=z[j*cols:(j+1)*cols]
            d=lcm(*(q.denominator for x in row for q in x))
            exact.append([(int(a*d),int(b*d)) for a,b in row])
        good=True
        for k,row in enumerate(exact):
            if not good:break
            for i in range(len(A)):
                idx=np.flatnonzero(A[i]|B[i]);v=w=0
                for c in idx:
                    a,b=row[c];u,j=int(A[i,c]),int(B[i,c]);v+=a*u-b*j;w+=b*u+a*j
                if v or w:good=False;break
        if good:
            assert all(row[c] == (0,0) if j != k else row[c][0] != 0 or row[c][1] != 0
                       for j,row in enumerate(exact) for k,c in enumerate(ka))
            return exact,ka,p
    return None

# Contraction of the homogeneous dual and multiplication matrices


def mat(a):
    return np.array([[v[0] for v in row] for row in a],dtype=object),np.array([[v[1] for v in row] for row in a],dtype=object)

def mul(a,b):
    ar,ai=a;br,bi=b
    return ar@br-ai@bi,ar@bi+ai@br

def scale(c,a):
    r,i=c;x,y=a
    return r*x-i*y,r*y+i*x

def nonzero(a):
    return bool(np.any(a[0]) or np.any(a[1]))

def normalize(a):
    x,y=a;d=reduce(gcd,(v for m in a for v in m.flat),0)
    if d>1:return x//d,y//d
    return a

def add_many(terms):
    r0,i0=terms[0]
    return sum((r for r,i in terms[1:]),r0.copy()),sum((i for r,i in terms[1:]),i0.copy())

def adjugate(U):
    r,q=U;n=len(r);a=[[(int(x),int(y)) for x,y in zip(rr,qq)]+[(int(j==k),0) for k in range(n)] for j,(rr,qq) in enumerate(zip(r,q))]
    old=(1,0)
    for k in range(n):
        u=next(i for i in range(k,n) if a[i][k]!=(0,0));a[k],a[u]=a[u],a[k]
        piv=a[k][k]
        for i,row in enumerate(a):
            if i==k:continue
            f=row[k]
            for j in range(2*n):
                if j!=k:
                    x,y=gmul(piv,row[j]);z,w=gmul(f,a[k][j]);row[j]=gmdiv((x-z,y-w),old)
            row[k]=(0,0)
        old=piv
    return old,mat([row[n:] for row in a])

@lru_cache(None)
def contractions(n,d):
    es,ix=monomials(n,d);ess,_=monomials(n,d-1)
    return [[ix[tuple(m[k]+int(j==k) for k in range(n))]for m in ess]for j in range(n)]

def multiplication(E,n,d):
    er,ei=mat(E);s=len(E)
    if not s:return [],None
    ar=[(er[:,idx],ei[:,idx]) for idx in contractions(n,d)]
    root=sqrt_i(PIVOT)
    for seed in range(1,12):
        forms=[seed**i for i in range(n)]
        U=add_many([scale((k,0),a) for k,a in zip(forms,ar)])
        pivmat=(U[0]+root*U[1])%PIVOT
        _,piv,_=rref(pivmat.tolist(),pivmat.shape[1],PIVOT)
        if len(piv)!=s:continue
        det,adj=adjugate((U[0][:,piv],U[1][:,piv]))
        mats=[]
        for a in ar:
            g=mul((a[0][:,piv],a[1][:,piv]),adj)
            b=mul(g,U);c=scale(det,a)
            if not (np.array_equal(b[0],c[0]) and np.array_equal(b[1],c[1])):return None,'unstable'
            mats.append(g)
        # A common scalar is free for homogeneous tests. Remove the determinant
        # phase as well as a scalar common to all numerators.
        mats=[scale((det[0],-det[1]),m) for m in mats]
        div=reduce(gcd,(v for a in mats for m in a for v in m.flat),0)
        if div>1:mats=[(a//div,b//div)for a,b in mats]
        return mats,forms
    return None,'positive'

def vanish_on_open(mats,shape,ph,pairs):
    n=len(shape);t=len(pairs);s=len(mats[0][0])
    rows=[add_many([scale(((1,0),(0,1),(-1,0),(0,-1))[c],m)for c,m in zip(row,mats)]) for row in ph]
    genuine={(i,k) for i,k,_,_ in pairs}
    factors=rows.copy()
    factors.extend(m for j,m in enumerate(mats) if shape[j][1]==1)
    for i in range(4):
        for k in range(i):
            if (i,k) not in genuine:
                factors.extend((add_many([rows[i],rows[k]]),add_many([rows[i],scale((-1,0),rows[k])])))
    H=(np.eye(s,dtype=object),np.zeros((s,s),dtype=object))
    for h in factors:
        H=normalize(mul(H,h))
        if not nonzero(H):return True,None
    power=H
    for i in range(s.bit_length()):
        power=normalize(mul(power,power))
        if not nonzero(power):return True,None
    return False,H

def compressed(M,H):
    d=len(H[0]);power=H
    for k in range(d.bit_length()):power=normalize(mul(power,power))
    root=sqrt_i(PIVOT)
    P=(power[0]+root*power[1])%PIVOT
    rows,cols,_=rref(P.tolist(),d,PIVOT)
    U=power[0][rows,:],power[1][rows,:]
    det,adj=adjugate((U[0][:,cols],U[1][:,cols]))
    def coordinates(a):
        v=mul((a[0][:,cols],a[1][:,cols]),adj)
        b=mul(v,U);c=scale(det,a)
        if np.array_equal(b[0],c[0]) and np.array_equal(b[1],c[1]):return v
        return None
    if coordinates(power) is None:return None
    maps=[]
    for m in M:
        a=coordinates(mul(U,m))
        if a is None:return None
        maps.append(scale((det[0],-det[1]),a))
    divisor=reduce(gcd,(v for z in maps for m in z for v in m.flat),0)
    return [(a//divisor,b//divisor) for a,b in maps]

def forbidden(shape,ph,pairs):
    n=len(shape);units=((1,0),(0,1),(-1,0),(0,-1))
    sig=[[units[t] for t in row] for row in ph];out=sig.copy()
    for j in range(n):
        if shape[j][1]==1:out.append([(int(i==j),0) for i in range(n)])
    genuine={(i,k) for i,k,_,_ in pairs}
    for i in range(4):
        for k in range(i):
            if (i,k) not in genuine:
                for sg in (1,-1):
                    out.append([(a+sg*c,b+sg*d) for (a,b),(c,d) in zip(sig[i],sig[k])])
    return out

def shrink(E,n,d,forms):
    er,ei=mat(E);mats=[(er[:,idx],ei[:,idx]) for idx in contractions(n,d)]
    vals=[];root=sqrt_i(PIVOT)
    for k,c in enumerate(forms):
        T=add_many([scale(a,m) for a,m in zip(c,mats)])
        rr,cc,_=rref(((T[0]+root*T[1])%PIVOT).tolist(),T[0].shape[1],PIVOT)
        vals.append((len(rr),k,rr,cc,T))
    for rank,k,rr,cc,T in sorted(vals,key=lambda u:u[0]):
        if not rank:
            if not nonzero(T):return [],k
            continue
        U=T[0][rr,:],T[1][rr,:]
        if rank<len(E):
            det,adj=adjugate((U[0][:,cc],U[1][:,cc]))
            coords=mul((T[0][:,cc],T[1][:,cc]),adj)
            a=mul(coords,U);b=scale(det,T)
            if not (np.array_equal(a[0],b[0]) and np.array_equal(a[1],b[1])):continue
        out=[]
        for a,b in zip(*U):
            dv=reduce(gcd,(*a,*b),0) or 1;out.append(list(zip(a//dv,b//dv)))
        return out,k
    return None,-1

# The quadratic rank test in a finite coordinate algebra


def gram(ph,pairs,orient,M,p):
    n=len(ph[0]);assert n==5
    d=len(M[0][0]);r=sqrt_i(p);roots=[1,r,p-1,p-r]
    W=np.array([np.array((a+r*b)%p,dtype=np.int64) for a,b in M])
    epsilon=np.array([[roots[t] for t in row] for row in ph],dtype=np.int64)
    weights=epsilon[:,:,None,None]*W[None,:,:,:]%p
    sums=weights.sum(1)%p
    F=np.zeros((11,4,5,d,d),dtype=np.int64)
    for i in range(4):F[i,i]=weights[i]
    rel={(i,k):(idx,b,c) for idx,(i,k,b,c) in enumerate(pairs)}
    gate=4
    for i in range(4):
        for k in range(i):
            if (i,k) in rel:
                idx,b,c=rel[i,k]
                for j in range(5):
                    if b[j]>=0:F[gate,i,j]=sums[k]@weights[i,j]%p
                    if c[j]>=0:F[gate,k,j]=sums[i]@weights[k,j]%p
            else:
                phi=(ph[i][0]-ph[k][0])%4
                for j in range(5):
                    F[gate,i,j]=-roots[2*phi%4]*(sums[k]@weights[k,j]%p)%p
                    F[gate,k,j]=sums[i]@weights[i,j]%p
            gate+=1
    F[10]=np.eye(d,dtype=np.int64)[None,None,:,:]
    K=np.kron(3*np.eye(4,dtype=np.int64)-1,4*np.eye(5,dtype=np.int64)-1)
    F=F.reshape(11,20,d,d);Fdual=np.einsum('xy,ayij->axij',K,F)%p
    return np.einsum('axij,bxjk->abik',F,Fdual)%p

def full_rank(a,p):
    n=len(a);a=a.copy()
    for k in range(n):
        nonzero=np.flatnonzero(a[k:,k])
        if not len(nonzero):return False
        j=k+int(nonzero[0]);a[[j,k]]=a[[k,j]];inv=pow(int(a[k,k]),-1,p)
        v=a[k+1:,k]*inv%p
        if len(v):a[k+1:,k+1:]=(a[k+1:,k+1:]-v[:,None]*a[k,k+1:])%p
    return True

def certificate(ph,pairs,orient,M):
    d=len(M[0][0])
    for p in (65521,1009,257):
        G=gram(ph,pairs,orient,M,p)
        for seed in range(8):
            rng=Random(seed)
            A=np.array([[rng.randrange(-7,8) for _ in range(11)] for u in range(7)],dtype=np.int64)
            B=np.einsum('ia,abuv,jb->iujv',A,G,A)%p
            if full_rank(B.reshape(7*d,7*d),p):return (p,seed)
    return None

def determinant(a,p):
    a=a.copy();d=1
    for j in range(len(a)):
        ks=np.flatnonzero(a[j:,j])
        if not len(ks):return 0
        k=j+int(ks[0])
        if k!=j:a[[j,k]]=a[[k,j]];d=-d
        piv=int(a[j,j]);d=d*piv%p
        f=a[j+1:,j]*pow(piv,-1,p)%p
        if len(f):a[j+1:,j+1:]=(a[j+1:,j+1:]-f[:,None]*a[j,j+1:])%p
    return d

def trim(a):
    while a and not a[-1]:a.pop()
    return a

def poly_gcd(f,g,p):
    a=f.copy();b=g.copy()
    while b:
        iv=pow(b[-1],-1,p)
        while len(a)>=len(b):
            k=a[-1]*iv%p;h=len(a)-len(b)
            for j,v in enumerate(b):a[h+j]=(a[h+j]-k*v)%p
            trim(a)
        a,b=b,a
    if a:
        v=pow(a[-1],-1,p);return [t*v%p for t in a]
    return []

def interpolate(vals,p):
    f=[0]*len(vals);v=list(vals);step=[1];fac=1
    for j in range(len(vals)):
        c=v[0]*pow(fac,-1,p)%p
        for k,x in enumerate(step):f[k]=(f[k]+c*x)%p
        v=[(y-x)%p for x,y in zip(v,v[1:])]
        nstep=[0]*(len(step)+1)
        for k,x in enumerate(step):nstep[k]=(nstep[k]-j*x)%p;nstep[k+1]=(nstep[k+1]+x)%p
        step=nstep;fac=fac*(j+1)%p
    return trim(f)

def split_certificate(shape,orient,M):
    ph,pairs=relations(tuple(v for v,k in shape for _ in range(k)),orient)
    d=len(M[0][0]);deg=4*d;ident=np.eye(d,dtype=object);zero=np.zeros((d,d),dtype=object)
    def full(t):
        m=[]
        for (v,count),a in zip(shape,M):
            if count==1:m.append(scale((2,0),a))
            else:m.extend([add_many([a,(t*ident,zero)]),add_many([a,(-t*ident,zero)])])
        return m
    for p in (65521,1009):
        G0=gram(ph,pairs,orient,full(0),p);inc=(gram(ph,pairs,orient,full(1),p)-G0)%p
        assert np.array_equal((G0+4*inc)%p,gram(ph,pairs,orient,full(2),p))
        common=[];maxdegree=False
        for seed in range(12):
            rng=Random(seed);A=np.array([[rng.randrange(-7,8) for _ in range(11)] for k in range(7)],dtype=np.int64)
            AA=np.einsum('ia,abuv,jb->iujv',A,G0,A).reshape(7*d,7*d)%p
            BB=np.einsum('ia,abuv,jb->iujv',A,inc,A).reshape(7*d,7*d)%p
            vals=[determinant((AA+k*BB)%p,p) for k in range(deg+1)]
            f=interpolate(vals,p)
            if len(f)==deg+1:maxdegree=True
            if f:common=poly_gcd(common,f,p)
            if maxdegree and len(common)==1:return (p,seed)
    return None

def check(row,d0):
    shape=tuple((v,row[:5].count(v)) for v in dict.fromkeys(row[:5]));n=len(shape);orient=row[5]
    A,B,ph,pairs=ideal_matrix(tuple(v for v,k in shape),orient,d0)
    result=lift(A,B,EXTENDED)
    if result is None:return ('no_lift',0,[])
    E,_,_=result;forms=forbidden(shape,ph,pairs);path=[]
    for d in range(d0,0,-1):
        if not E:return ('excluded',0,path)
        if d>=2:
            M,why=multiplication(E,n,d)
        else:M=None
        if M is not None:
            zero,H=vanish_on_open(M,shape,ph,pairs)
            if zero:return ('excluded',0,path)
            N=compressed(M,H)
            if N is None:return ('compression',len(E),path)
            if n==5:cert=certificate(ph,pairs,orient,N)
            else:cert=split_certificate(shape,orient,N)
            return ('gram' if cert else 'unresolved',len(N[0][0]),path+[cert])
        if d==1:break
        E,idx=shrink(E,n,d,forms);path.append(idx)
        if E is None:return ('compression',0,path)
    return ('positive',len(E),path)

# The three-edge parameter curves


def curve(shape,orient):
    ph,pairs=relations(shape,orient)
    g=next(a for a in range(4) if all(a in (i,k) for i,k,b,c in pairs))
    info=[]
    for i0,(i,k,b,c) in enumerate(pairs):
        B=tuple(j for j,t in enumerate(b) if t!=-1);C=tuple(j for j,t in enumerate(c) if t!=-1)
        if g==i:B,C=C,B
        center=tuple(j for j in range(5) if j not in B+C)
        info.append((center,B,C,-1 if orient>>i0&1 else 1))
    P=info[0][0];Q=tuple(j for j in range(5) if j not in P)
    shapes=[(int(k not in P),sig) for a,b,c,sig in info for k in [a[0]]]
    assert all(a in (P,Q) for a,b,c,s in info)
    T=[[int(j in P) for j in range(5)],[int(j in Q) for j in range(5)]]
    T.extend([int(j in b)-int(j in c) for j in range(5)] for a,b,c,s in info)
    return ph,pairs,g,info,shapes,T

def model(shape,orient):
    ph,pairs,g,info,ty,T=curve(shape,orient)
    dd=det(T)
    if not dd:return []
    n=5
    adj=np.array([[(-1)**(i+j)*det([[T[a][b] for b in range(n) if b!=i] for a in range(n) if a!=j]) for j in range(n)] for i in range(n)],dtype=np.int64)
    assert np.array_equal(adj@np.array(T),int(dd)*np.eye(5,dtype=np.int64))
    types=list(dict.fromkeys(ty));kt=len(types);models=[]
    for choices in product((-1,1),repeat=3-kt):
        used=set();ix=0;R=np.zeros((5,2+kt),dtype=np.complex128);R[0,0]=2;R[1,1]=2
        for i,key in enumerate(ty):
            center,sign=key;v=1
            if key in used:v=choices[ix];ix+=1
            used.add(key)
            R[i+2,1-center]=1-sign*1j;R[i+2,2+types.index(key)]=v
        W=(adj@R)*np.array([G[-e%4]for e in ph[g]])[:,None]
        # Each row is a scaled affine-normalized scalar weight polynomial in A,B,U_types.
        S=np.array([[G[e]for e in row] for row in ph])@W
        forbc=[*W,*S];genuine={(i,k)for i,k,_,_ in pairs}
        for i in range(4):
            for k in range(i):
                if (i,k) not in genuine:forbc.extend((S[i]+S[k],S[i]-S[k]))
        if any(np.all(v==0) for v in forbc):models.append(None)
        else:models.append((ph,pairs,types,W))
    return models

@lru_cache(None)
def field(p):
    I=sqrt_i(p);sq=np.zeros(p,dtype=np.int64);has=np.zeros(p,dtype=bool);x=np.arange(p,dtype=np.int64);sq[x*x%p]=x;has[x*x%p]=True
    v=next(i for i in range(2,p) if not has[i]);iv=pow(v,-1,p);inv=np.array([0]+[pow(x,-1,p) for x in range(1,p)],dtype=np.int64)
    return I,sq,has,v,iv,inv

def mult(a,b,p,v):
    x,y=a;z,w=b;return (x*z+v*((y*w)%p))%p,(x*w+y*z)%p

def arraydet(R,I,p,v,iv):
    R=R.copy();I=I.copy();N,k,_=R.shape;batch=np.arange(N);dr=np.ones(N,dtype=np.int64);di=np.zeros(N,dtype=np.int64)
    for j in range(k):
        nz=(R[:,j:,j]!=0)|(I[:,j:,j]!=0)
        ix=j+np.argmax(nz,axis=1)
        rr=R[batch,ix].copy();ii=I[batch,ix].copy()
        R[batch,ix]=R[:,j].copy();I[batch,ix]=I[:,j].copy();R[:,j]=rr;I[:,j]=ii
        sign=1-2*(ix!=j)
        pr=R[:,j,j];pi=I[:,j,j]
        dr,di=mult((dr*sign,di*sign),(pr,pi),p,v)
        if j==k-1:break
        nrm=(pr*pr-v*(pi*pi%p))%p
        ir=pr*iv[nrm]%p;ii=-pi*iv[nrm]%p
        fr,fi=mult((R[:,j+1:,j],I[:,j+1:,j]),(ir[:,None],ii[:,None]),p,v)
        zr,zi=mult((fr[:,:,None],fi[:,:,None]),(R[:,None,j,j+1:],I[:,None,j,j+1:]),p,v)
        R[:,j+1:,j+1:]=(R[:,j+1:,j+1:]-zr)%p;I[:,j+1:,j+1:]=(I[:,j+1:,j+1:]-zi)%p
    return dr,di

def build(model,orient,lam,p,deg):
    ph,pairs,types,W=model;I,sq,has,v,vi,inv=field(p);sheets=2**len(types)
    ts=np.arange(deg+1,dtype=np.int64);A=ts;B=(1-lam*ts)%p
    vals=[A,B];rs=[];ims=[]
    for fixed,sign in types:
        gamma=sign*I%p;a=vals[fixed];t=vals[1-fixed]
        disc=((4-2*gamma)*(t*t%p)-4*(1-gamma)*(a*a%p))%p
        rs.append(np.where(has[disc],sq[disc],0));ims.append(np.where(has[disc],0,sq[disc*vi%p]))
    signs=np.array(list(product((-1,1),repeat=len(types))),dtype=np.int64)
    E=np.zeros((deg+1,sheets,2+len(types)),dtype=np.int64);EE=E.copy()
    E[:,:,0]=A[:,None];E[:,:,1]=B[:,None];E[:,:,2:]=np.array(rs).T[:,None,:]*signs[None,:,:]
    EE[:,:,2:]=np.array(ims).T[:,None,:]*signs[None,:,:]
    coef=(W.real.astype(np.int64)+I*W.imag.astype(np.int64))%p
    wr=(E@coef.T).reshape(-1,5)%p;wi=(EE@coef.T).reshape(-1,5)%p
    roots=[1,I,p-1,p-I];ep=np.array([[roots[c] for c in q] for q in ph],dtype=np.int64)
    R=ep[None,:,:]*wr[:,None,:]%p;J=ep[None,:,:]*wi[:,None,:]%p
    sr=R.sum(2)%p;si=J.sum(2)%p
    N=len(wr);F=np.zeros((N,11,4,5),dtype=np.int64);Fi=F.copy()
    for i in range(4):F[:,i,i]=R[:,i];Fi[:,i,i]=J[:,i]
    rel={(i,k):(b,c) for i,k,b,c in pairs};z=4
    for i in range(4):
        for k in range(i):
            if (i,k) in rel:
                b,c=rel[i,k]
                for j in range(5):
                    if b[j]>=0:F[:,z,i,j],Fi[:,z,i,j]=mult((sr[:,k],si[:,k]),(R[:,i,j],J[:,i,j]),p,v)
                    if c[j]>=0:F[:,z,k,j],Fi[:,z,k,j]=mult((sr[:,i],si[:,i]),(R[:,k,j],J[:,k,j]),p,v)
            else:
                for j in range(5):
                    rr,ii=mult((sr[:,k],si[:,k]),(R[:,k,j],J[:,k,j]),p,v)
                    F[:,z,i,j]=-rr%p;Fi[:,z,i,j]=-ii%p
                    F[:,z,k,j],Fi[:,z,k,j]=mult((sr[:,i],si[:,i]),(R[:,i,j],J[:,i,j]),p,v)
            z+=1
    F[:,10]=1
    F=F.reshape(N,11,20);Fi=Fi.reshape(N,11,20)
    K=np.kron(3*np.eye(4,dtype=np.int64)-1,4*np.eye(5,dtype=np.int64)-1)
    KFr=F@K%p;KFi=Fi@K%p
    Gr=(F@KFr.transpose(0,2,1)-v*((Fi@KFi.transpose(0,2,1))%p))%p
    Gi=(F@KFi.transpose(0,2,1)+Fi@KFr.transpose(0,2,1))%p
    return Gr,Gi

def trial(model,orient,p,lam):
    sheets=2**len(model[2]);Dmax=26*sheets;Gr,Gi=build(model,orient,lam,p,Dmax)
    _,_,_,v,_,inv=field(p);common=[];full=False
    for test in range(len(PROFILES)*2):
        n0,n1,n2=PROFILES[test%len(PROFILES)];degree=2*(n1+2*n2)*sheets
        rng=Random(test+103);A=np.zeros((7,11),dtype=np.int64)
        if n0:A[0,10]=1
        A[n0:n0+n1,:4]=np.array([[rng.randrange(-7,8) for _ in range(4)] for k in range(n1)],dtype=np.int64).reshape(n1,4)
        A[n0+n1:,4:10]=np.array([[rng.randrange(-7,8) for _ in range(6)] for k in range(n2)])
        last=(degree+1)*sheets
        rr=(A@Gr[:last]@A.T)%p;ii=(A@Gi[:last]@A.T)%p
        dr,di=arraydet(rr,ii,p,v,inv);dr=dr.reshape(-1,sheets);di=di.reshape(-1,sheets);nr=np.ones(len(dr),dtype=np.int64);ni=np.zeros(len(dr),dtype=np.int64)
        for k in range(sheets):nr,ni=mult((nr,ni),(dr[:,k],di[:,k]),p,v)
        assert not np.any(ni)
        f=interpolate(nr.tolist(),p)
        if len(f)==degree+1:full=True
        if f:common=poly_gcd(common,f,p)
        if full and len(common)==1:return ('excluded',p,lam,test+1,common)
    return ('rest',p,lam,len(PROFILES)*2,common,full)

def exact_gram(ph,pairs,w):
    e=np.array([[G[t] for t in row] for row in ph])
    weights=e*w[None,:];s=weights.sum(1);F=np.zeros((11,4,5),dtype=np.complex128)
    for i in range(4):F[i,i]=weights[i]
    rel={(i,k):(b,c) for i,k,b,c in pairs};z=4
    for i in range(4):
        for k in range(i):
            if (i,k) in rel:
                b,c=rel[i,k]
                for j in range(5):
                    if b[j]!=-1:F[z,i,j]=s[k]*weights[i,j]
                    if c[j]!=-1:F[z,k,j]=s[i]*weights[k,j]
            else:
                F[z,i]=-s[k]*weights[k];F[z,k]=s[i]*weights[i]
            z+=1
    F[10]=1
    K=np.kron(3*np.eye(4,dtype=np.int64)-1,4*np.eye(5,dtype=np.int64)-1)
    X=F.reshape(11,20)
    assert 2 * 20**2 * 6 * max(abs(v) for v in X.flat)**2 < 2**51
    return (X@K@X.T).tolist()

def endpoint(m):
    ph,pairs,types,W=m
    grams=[]
    for sig in product((-1,1),repeat=len(types)):
        u=[v*(1+sign*1j) for v,(fixed,sign) in zip(sig,types)]
        w=W@np.array([1,-1,*u]);gr=exact_gram(ph,pairs,w)
        rank=exact_rank(gr,11)
        if rank<=6:return rank,sig
        grams.append(np.array(gr))
    witnesses=[]
    for test in range(2*len(PROFILES)):
        n0,n1,n2=PROFILES[test%len(PROFILES)];rng=Random(test+103);A=np.zeros((7,11),dtype=np.int64)
        if n0:A[0,10]=1
        A[n0:n0+n1,:4]=np.array([[rng.randrange(-7,8) for _ in range(4)] for k in range(n1)],dtype=np.int64).reshape(n1,4)
        A[n0+n1:,4:10]=np.array([[rng.randrange(-7,8) for _ in range(6)] for k in range(n2)])
        yes=None
        for j,gr in enumerate(grams):
            assert 11**2 * 7**2 * max(abs(z) for z in gr.flat) < 2**52
            small=A@gr@A.T
            assert max(abs(v) for v in small.flat)<2**50
            if exact_rank(small.tolist(),7)<7:yes=j;break
        if yes is None:return None
        witnesses.append(yes)
    return 7,witnesses

def solve(shape,orient):
    ph,pairs,g,info,types,T=curve(shape,orient)
    assert np.array_equal(np.array(T[2]),-np.array(T[3])) and types[0]==types[1]
    assert set(x[0] for x in types)=={0}
    U=[T[0],T[1],T[2],T[4]]
    for j in range(5):
        aug=U+[[int(j==i) for i in range(5)]]
        dd=det(aug)
        if dd:break
    assert dd
    adj=np.array([[(-1)**(i+j)*det([[aug[a][b] for b in range(5) if b!=i] for a in range(5) if a!=j]) for j in range(5)] for i in range(5)],dtype=np.int64)
    assert np.array_equal(adj@np.array(aug),dd*np.eye(5,dtype=np.int64))
    for p in (65521,):
        I,sq,has,v,vi,inv=field(p);a0=(-1+types[0][1]*I)%p;a1=(-1+types[2][1]*I)%p
        if not has[a0] or not has[a1]:continue
        roots=np.array([1,I,p-1,p-I],dtype=np.int64)
        proof=[]
        for e,f in product((-1,1),repeat=2):
            y0=e*sq[a0]%p;y1=f*sq[a1]%p
            zs=[(adj@np.array([1,0,y0,y1,j])%p)*roots[(-np.array(ph[g]))%4]%p for j in range(15)]
            gr=[]
            for z in zs:
                M=[(np.array([[x]],dtype=object),np.zeros((1,1),dtype=object)) for x in z]
                gr.append(gram(ph,pairs,orient,M,p)[:,:,0,0])
            full=False;common=[]
            for seed in range(20):
                r=Random(seed);A=np.array([[r.randrange(-5,6) for _ in range(11)]for k in range(7)],dtype=np.int64)
                vals=[determinant((A@G@A.T)%p,p) for G in gr]
                poly=interpolate(vals,p)
                if len(poly)==15:full=True
                if poly:common=poly_gcd(common,poly,p)
                if full and len(common)==1:break
            proof.append((e,f,full,common,seed))
        if all(full and len(gc)==1 for _,_,full,gc,_ in proof):return p,proof
    return p,proof

def prime_rank(a, modulus):
    """Row rank over a prime field. The matrices here are at most 10 by 20."""
    a=[list(row) for row in a if any(row)]
    if not a:return 0
    rank=0
    for col in range(len(a[0])):
        pivot=next((k for k in range(rank,len(a)) if a[k][col]),None)
        if pivot is None:continue
        a[rank],a[pivot]=a[pivot],a[rank]
        inv=pow(a[rank][col],-1,modulus)
        for k in range(rank+1,len(a)):
            x=a[k][col]*inv%modulus
            if x:a[k][col:]=[(y-x*z)%modulus for y,z in zip(a[k][col:],a[rank][col:])]
        rank+=1
        if rank==len(a):break
    return rank

def phase_constraint_matrix(phase, pairs, root, modulus):
    roots=(1,root,modulus-1,modulus-root)
    E=[[roots[v] for v in row]for row in phase]
    matrix=[]
    for i in range(4):
        a=[0]*20;a[5*i:5*i+5]=E[i];matrix.append(a)
    oriented={(i,k):(b,c) for i,k,b,c in pairs}
    for i in range(4):
        for k in range(i):
            a=[0]*20
            if (i,k) in oriented:
                b,c=oriented[i,k]
                for j in range(5):
                    if b[j]!=-1:a[5*i+j]=E[i][j]
                    if c[j]!=-1:a[5*k+j]=E[k][j]
            else:
                phase_square=roots[2*(phase[i][0]-phase[k][0])%4]
                for j in range(5):
                    a[5*i+j]=phase_square*E[k][j]%modulus
                    a[5*k+j]=-E[i][j]%modulus
            matrix.append(a)
    return matrix

def candidate_profiles():
    """Enumerate all row-permutation and column-permutation orbits in fourth-root phases."""
    raw=set(relative_rows());seen=set();reps=[]
    for v in sorted(raw):
        if v in seen:continue
        group=set(orbit(v));seen.update(group);reps.append(min(group))
    assert len(raw)==34209 and len(reps)==656
    root=sqrt_i(PIVOT)
    all_masks=[list(range(20))]+[[j for j in range(20) if j//5 in (i,k)]
                                   for i in range(4) for k in range(i)]
    candidates=[];total=0
    for shape in sorted(reps):
        kinds=edges(shape);assert kinds is not None
        number=kinds.count(3)
        for oriented in range(2**number):
            total+=1
            phase,pairs=relations(shape,oriented)
            mats=[phase_constraint_matrix(phase,pairs,v,PIVOT) for v in (root,PIVOT-root)]
            ranks=[]
            for columns in all_masks:
                ranks.append(max(prime_rank([[row[j] for j in columns] for row in a],PIVOT) for a in mats))
            # The Gaussian integer minors have absolute value at most 10^5 by
            # Hadamard. Vanishing under both embeddings proves exact vanishing.
            if all(ranks[0]-u==3 for u in ranks[1:]):
                candidates.append((*shape,oriented,number,20-ranks[0]))
    assert total==29808 and len(candidates)==12185
    return candidates

def check_curve_case(row):
    shape=tuple(row[:5]);orient=row[5];charts=model(shape,orient)
    if not charts:
        field_prime,witnesses=solve(shape,orient)
        assert field_prime==65521 and all(full and gcdpoly==[1] for _,_,full,gcdpoly,_ in witnesses)
        return Counter({'dependent coordinates':1})
    result=Counter()
    for chart in charts:
        if chart is None:result['zero required factor']+=1;continue
        findings=trial(chart,orient,65521,2)
        if findings[0]=='excluded':result['coprime minor norms']+=1;continue
        assert findings[-1] and findings[-2]==[65520,1]
        assert endpoint(chart) is not None
        result['zero row sum at the only common root']+=1
    return result

def main():
    parser=argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--part',choices=['all','profiles','curves','finite'],default='all')
    parser.add_argument('--shard',nargs=2,type=int,default=(0,1),metavar=('INDEX','COUNT'))
    args=parser.parse_args()
    offset,number=args.shard
    if number<=0 or not 0<=offset<number:parser.error('shard INDEX must lie between zero and COUNT−1')
    start=monotonic()
    cases=candidate_profiles()
    counts=Counter(row[6] for row in cases)
    print('29,808 oriented phase profiles; 12,185 pass the pair projection test.',flush=True)
    print('Cases by number of genuine pairs',dict(sorted(counts.items())),flush=True)
    if args.part=='profiles':return
    curves=Counter();finite=Counter();seen=0
    for index,row in enumerate(cases):
        if index%number!=offset or row[6]==0:continue
        n=len(set(row[:5]));is_curve=row[6]==3 and n==5
        if is_curve and args.part in ('all','curves'):
            curves.update(check_curve_case(row));seen+=1
        if not is_curve and args.part in ('all','finite'):
            tag,dimension,path=check(row,n+1)
            if tag not in ('excluded','gram'):
                raise RuntimeError((row,tag,dimension,path))
            finite[tag]+=1;seen+=1
        if seen and seen%500==0:print('Verified',seen,'cases in',round(monotonic()-start),'seconds',flush=True)
    if number==1 and args.part in ('all','curves'):
        assert curves==Counter({'zero required factor':236,'coprime minor norms':64,
                                'zero row sum at the only common root':56,'dependent coordinates':4})
    if number==1 and args.part in ('all','finite'):assert sum(finite.values())==12023
    print('Curve branches',dict(curves))
    print('Finite cases',dict(finite))
    print('Completed in',round(monotonic()-start),'seconds.')

if __name__=='__main__':
    main()

