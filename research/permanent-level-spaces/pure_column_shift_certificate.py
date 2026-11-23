"""Univariate modular arithmetic and small finite extensions for the radical certificate."""
P=241
def trim(f):
    f=list(f)
    while f and not f[-1]: f.pop()
    return f
def padd(a,b):
    return trim([((a[i]if i<len(a) else 0)+(b[i]if i<len(b)else 0))%P for i in range(max(len(a),len(b)))])
def pscale(a,c):return trim([x*c%P for x in a])
def pmul(a,b):
    if not(a and b):return []
    f=[0]*(len(a)+len(b)-1)
    for i,x in enumerate(a):
        for j,y in enumerate(b):f[i+j]+=x*y
    return trim([x%P for x in f])
def pdiv(a,b):
    a=a[:];q=[0]*max(0,len(a)-len(b)+1);t=pow(b[-1],-1,P)
    while len(a)>=len(b):
        j=len(a)-len(b);z=q[j]=a[-1]*t%P
        for i,x in enumerate(b):a[j+i]=(a[j+i]-z*x)%P
        a=trim(a)
    return trim(q),a
def pgcd(a,b):
    while b:a,b=b,pdiv(a,b)[1]
    return pscale(a,pow(a[-1],-1,P))if a else []
def ppow(a,n,f):
    o=[1]
    while n:
        if n&1:o=pdiv(pmul(o,a),f)[1]
        a=pdiv(pmul(a,a),f)[1];n//=2
    return o
def peval(f,t):
    o=0
    for x in reversed(f):o=(o*t+x)%P
    return o
def interp(xs,ys):
    v=ys[:];a=[]
    for j in range(len(xs)):
        a.append(v[0]);v=[(v[i+1]-v[i])*pow((xs[i+j+1]-xs[i])%P,-1,P)%P for i in range(len(v)-1)]
    o=[a[-1]]
    for i in reversed(range(len(xs)-1)):
        o=padd(pmul(o,[-xs[i]%P,1]),[a[i]])
    return o
def factor(f):
    from random import Random
    rng=Random(179)
    deriv=[i*f[i]%P for i in range(1,len(f))]
    f=pdiv(f,pgcd(f,trim(deriv)))[0]
    answer=[]
    def equal(g,d):
        if len(g)==d+1:answer.append(g);return
        while True:
            h=[rng.randrange(P)for _ in range(len(g)-1)]
            z=pgcd(g,padd(ppow(h,(P**d-1)//2,g),[-1%P]))
            if 1<len(z)<len(g):
                equal(z,d);equal(pdiv(g,z)[0],d);return
    x=[0,1];xp=x[:];d=1
    while 2*d<=len(f)-1:
        xp=ppow(xp,P,f);g=pgcd(f,padd(xp,[0,-1%P]))
        if len(g)>1:
            equal(g,d);f=pdiv(f,g)[0]
            if len(f)==1:break
            xp=pdiv(xp,f)[1]
        d+=1
    if len(f)>1:answer.append(f)
    return sorted(answer,key=lambda z:(len(z),z))
class Field:
    def __init__(self,f):self.f=f;self.n=len(f)-1
    def val(self,v):
        if isinstance(v,E):return v
        return E(self,pdiv(trim(v if isinstance(v,(list,tuple))else [int(v)%P]),self.f)[1])
class E:
    __slots__='F','v'
    def __init__(self,F,v):self.F=F;self.v=v
    def __bool__(self):return bool(self.v)
    def __repr__(self):return repr(self.v)
    def __add__(self,b):return E(self.F,padd(self.v,self.F.val(b).v))
    __radd__=__add__
    def __neg__(self):return E(self.F,pscale(self.v,-1))
    def __sub__(self,b):return self+-self.F.val(b)
    def __rsub__(self,b):return self.F.val(b)-self
    def __mul__(self,b):
        b=self.F.val(b);return E(self.F,pdiv(pmul(self.v,b.v),self.F.f)[1])
    __rmul__=__mul__
    def __pow__(self,n):
        if n<0:return (self**(-n)).inverse()
        return E(self.F,ppow(self.v,n,self.F.f))
    def __eq__(self,b):return self.v==self.F.val(b).v
    def inverse(self):
        assert self
        a,b=self.F.f[:],self.v[:];x,y=[],[1]
        while b:
            q,r=pdiv(a,b);a,b=b,r;x,y=y,padd(x,pscale(pmul(q,y),-1))
        assert len(a)==1
        return self.F.val(pscale(x,pow(a[0],-1,P)))
    def __truediv__(self,b):return self*self.F.val(b).inverse()
def ydiv(a,b):
    a=trim(a);q=[0]*max(0,len(a)-len(b)+1);t=b[-1].inverse()
    while len(a)>=len(b):
        i=len(a)-len(b);q[i]=x=a[-1]*t
        for j,z in enumerate(b):a[i+j]=a[i+j]-x*z
        a=trim(a)
    return trim(q),a
def ygcd(a,b):
    while b:a,b=b,ydiv(a,b)[1]
    return [x/a[-1]for x in a]if a else []
def yeval(f,t):
    a=t.F.val(0)
    for z in reversed(f):a=a*t+z
    return a
def yinterp(values):
    # Interpolate over points 0,...,degree using divided differences in the given field.
    F=values[0].F;v=values[:];c=[]
    for d in range(len(v)):
        c.append(v[0]);v=[(b-a)*pow(d+1,-1,P)for a,b in zip(v,v[1:])]
    a=[c[-1]]
    for i in reversed(range(len(c)-1)):
        a=[a[0]*(-i)+c[i]]+[a[j-1]-i*a[j]for j in range(1,len(a))]+[a[-1]]
    return trim(a)

"""Projective elimination of the scalar discriminant points necessary for a pure column shift."""
from itertools import combinations, permutations, product
from functools import lru_cache
from math import prod

omega=next(w for w in range(2,P)if pow(w,5,P)==1)
roots=[pow(omega,i,P)for i in range(5)]
fourth=next(v for v in range(2,P)if v*v%P==P-1)
slant=3
def mod(v):return v if isinstance(v,E)else v%P
def small_det(mat):
    n=len(mat)
    if n<2:return mat[0][0]if n else 1
    return mod(sum((-1)**i*mat[0][i]*small_det([r[:i]+r[i+1:]for r in mat[1:]])for i in range(n)))
def gmat(x,y,z):
    return [[0 if i==j else mod(x+y*(a+b)+z*(a*a+a*b+b*b))for j,b in enumerate(roots)]for i,a in enumerate(roots)]
def cof(g,col=0):
    return [mod((-1)**(i+col)*small_det([r[:i]+r[i+1:]for k,r in enumerate(g)if k!=col]))for i in range(5)]
def det5(x,y,z):return mod(4*x**5-72*y**5+72*z**5+220*x*y**3*z-140*x*x*y*z*z)
def elementary(v,k):return mod(sum(prod(q)for q in combinations(v,k)))
def mixed(c):return mod(sum(c[i]*c[j]*c[k]*(sum(roots)-roots[i]-roots[j]-roots[k])for i,j,k in combinations(range(5),3)))
def econd(c,kind):
    if kind=='quartic':return elementary(c,4)
    if kind=='cubic':return elementary(c,3)
    return mixed(c)
def resultant(d,f):
    n=len(d)-1
    mat=[]
    for i in range(n):
        r=pdiv([0]*i+f,d)[1]
        mat.append(r+[0]*(n-len(r)))
    return small_det(mat)
def primary(kind):
    bound=80 if kind=='quartic'else 60;ey=16 if kind=='quartic'else 12
    xs=list(range(bound+4));ys=[]
    for u in xs:
        d=interp(list(range(6)),[det5(1,u-slant*y,y)for y in range(6)])
        f=interp(list(range(ey+1)),[econd(cof(gmat(1,u-slant*y,y)),kind)for y in range(ey+1)])
        ys.append(resultant(d,f))
    r=interp(xs[:bound+1],ys[:bound+1])
    assert all(peval(r,x)==y for x,y in zip(xs,ys))
    return r
def genuine_points(u,kind):
    F=u.F
    d=yinterp([F.val(det5(F.val(1),u-slant*y,F.val(y)))for y in range(6)])
    common=d
    for typ in ([kind]if kind=='quartic'else ['cubic','mixed']):
        ey=16 if typ=='quartic'else 12
        for j in range(5):
            f=yinterp([F.val(econd(cof(gmat(F.val(1),u-slant*y,F.val(y)),j),typ))for y in range(ey+1)])
            common=ygcd(common,f)
            if len(common)<=1:return []
    deriv=[i*v for i,v in enumerate(common)if i]
    common=ydiv(common,ygcd(common,trim(deriv)))[0]
    if len(common)==2: roots_y=[-common[0]/common[1]]
    elif F.n==1:
        roots_y=[F.val(i)for i in range(P)if not yeval(common,F.val(i))]
        if len(roots_y)!=len(common)-1:raise ValueError(('nonseparating chart',u,common))
    else:raise ValueError(('nonseparating chart',u,common))
    out=[]
    for y in roots_y:
        x=u-slant*y
        assert not det5(F.val(1),x,y)
        g=gmat(F.val(1),x,y)
        c=next(vec for j in range(5)if any(vec:=cof(g,j)))
        out.append((x,y,c))
    return out
def rank(mat):
    m=[r[:]for r in mat];d=0
    for j in range(len(m[0])):
        i=next((i for i in range(d,len(m))if m[i][j]),None)
        if i is None:continue
        m[i],m[d]=m[d],m[i]
        z=m[d][j].inverse();m[d]=[a*z for a in m[d]]
        for i in range(d+1,len(m)):
            if m[i][j]:
                c=m[i][j];m[i]=[x-c*y for x,y in zip(m[i],m[d])]
        d+=1
        if d==len(m):break
    return d
@lru_cache(None)
def row_factor(exps):
    return sum(pow(fourth,sum(i*k for i,k in zip(ix,exps)),P)for ix in permutations(range(4),len(exps)))%P
def bordered(c):
    F=next(v.F for v in c if isinstance(v,E));zero=F.val(0)
    labels=[(k,j)for k in (1,2,3)for j in range(5)]
    @lru_cache(None)
    def column_factor(omit,a,b):
        allowed=[j for j in range(5)if j not in omit]
        return F.val(sum(prod(c[i]for i in ix[:a])*prod(roots[i]for i in ix[a:])for ix in permutations(allowed,a+b)))
    linear=[]
    for d in range(2,5):
        for a in range(1,d):
            b=d-1-a
            linear.append([row_factor((k,)+(1,)*a+(0,)*b)*column_factor((j,),a,b)for k,j in labels])
    hess=[]
    for d in range(2,5):
        for a in range(d-1):
            b=d-2-a
            hess.append([[zero if i==j else row_factor((k,l)+(1,)*a+(0,)*b)*column_factor(tuple(sorted((i,j))),a,b)
                          for l,j in labels] for k,i in labels])
    for coeff in [[0,1,0,0,0,0],[0,0,0,1,0,0],[1]*6,[1,2,3,5,7,11],[1,3,2,9,11,7]]:
        q=[[sum(t*h[i][j]for t,h in zip(coeff,hess))+zero for j in range(15)]for i in range(15)]
        bmat=[q[i]+[l[i]for l in linear]for i in range(15)]+[l+[zero]*len(linear)for l in linear]
        rk=rank(bmat)
        if rk>=19:return coeff,rk
    return None,rk
def check_infinity(kind):
    F=Field([0,1]);hits=[]
    for t in roots:
        g=gmat(F.val(0),F.val(1),F.val(t));assert not det5(0,1,t)
        c=next(vec for j in range(5)if any(vec:=cof(g,j)))
        if not econd(c,kind) and (kind=='quartic'or not mixed(c)):hits.append((t,c))
    return hits
def verify_discriminant():
    from math import isqrt
    assert all(P%d for d in range(2,isqrt(P)+1))
    # Homogeneous determinant degree five; a six-value grid suffices.
    for x,y,z in product(range(6),repeat=3):
        assert small_det(gmat(x,y,z))==det5(x,y,z)
    # On x=1, y!=0 put s=z/y² and t=y⁵. The two partials yield M*t=N.
    N=[-220%P,280%P];M=[0,0,0,0,360%P]
    cleared=padd(pscale(pmul(M,M),4),pmul(pmul([-72%P,220%P,-140%P],N),M))
    cleared=padd(cleared,pmul([0,0,0,0,0,72%P],pmul(N,N)))
    assert pgcd(cleared,[-360%P,660%P,-140%P])==[1]
    print('Smooth discriminant quintic verified over the algebraic closure of F_241.')

def main():
    verify_discriminant()
    for kind in ('cubic','quartic'):
        r=primary(kind);fs=factor(r)
        # Check each factor is irreducible and that their product contains every root.
        rem=r[:]
        for f in fs:
            n=len(f)-1
            assert not pdiv(padd(ppow([0,1],P**n,f),[0,-1%P]),f)[1]
            for j in range(1,n//2+1):
                assert len(pgcd(f,padd(ppow([0,1],P**j,f),[0,-1%P])))==1
            while not pdiv(rem,f)[1]:rem=pdiv(rem,f)[0]
        assert len(rem)==1
        counts={};maximum=0
        for f in fs:
            F=Field(f);u=F.val([0,1]);pts=genuine_points(u,kind)
            for _,_,c in pts:
                assert kind=='quartic'
                coeff,rk=bordered(c);assert rk>=19
                key=(F.n,sum(bool(z)for z in c));counts[key]=counts.get(key,0)+1;maximum=max(maximum,rk)
        for _,c in check_infinity(kind):
            assert kind=='quartic'
            _,rk=bordered(c);assert rk>=19
            key=(1,sum(bool(z)for z in c));counts[key]=counts.get(key,0)+1;maximum=max(maximum,rk)
        print(kind,'resultant degree',len(r)-1,'distinct factor degrees',[len(f)-1 for f in fs],
              'candidate orbits by (degree,support)',counts,'maximum bordered rank',maximum)
        if kind=='cubic':assert not counts
        else:assert counts=={(1,3):10,(10,5):3}
    print('All 40 radical candidates violate the necessary rank cap of 18.')

if __name__=='__main__': main()
