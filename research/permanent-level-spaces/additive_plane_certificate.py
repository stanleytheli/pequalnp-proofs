"""Exact modular trace constraints for additive 4 x 5 level pencils, over the algebraic closure."""
from itertools import permutations,product
from math import comb
from math import isqrt

P=65521
def inv(x):return pow(int(x)%P,-1,P)
def add(p,q):return [(x+y)%P for x,y in zip(p,q)]
def mul(p,q):
    a=[0]*(len(p)+len(q)-1)
    for i,x in enumerate(p):
        for j,y in enumerate(q):a[i+j]+=x*y
    return [k%P for k in a]
def scale(p,k):return [x*k%P for x in p]
def plus(*args):return [sum(x)%P for x in zip(*args)]
def pw(a,n):
    b=[1]
    for _ in range(n):b=mul(b,a)
    return b

# Coordinates x,y,z on the centered row tetrahedron; packed coefficients encode moments of s and t.
def moment_quadrics(rows2,xyz):
    m2=scale(plus(*rows2),-20*inv(3))
    m3=scale(xyz,-60)
    m4=add(scale(plus(*(mul(x,x)for x in rows2)),260*inv(9)),
           scale(plus(*(mul(rows2[i],rows2[j])for i,j in ((0,1),(1,2),(0,2)))),-200*inv(9)))
    return {(d-j,j): x*inv(comb(d,j))%P for d,m in enumerate([[5],[0,0],m2,m3,m4])for j,x in enumerate(m)}

def moment_roots(a,b,c):
    return moment_quadrics([scale([1,0,0],b*c),scale([0,0,1],a*c),scale([1,2,1],a*b)],
                           scale([0,-1,-1,0],a*b*c))

def determinant(A):
    n=len(A);m=[r[:]for r in A];d=1
    for i in range(n):
        j=next((j for j in range(i,n)if m[j][i]%P),None)
        if j is None:return 0
        if i!=j:m[i],m[j]=m[j],m[i];d=-d
        t=m[i][i]%P;d=d*t%P;r=inv(t)
        for j in range(i+1,n):
            x=m[j][i]*r%P
            for k in range(i+1,n):m[j][k]=(m[j][k]-x*m[i][k])%P
    return d%P

def adj(A):
    return [[(-1)**(i+j)*determinant([r[:i]+r[i+1:]for k,r in enumerate(A)if k!=j])%P
             for j in range(len(A))]for i in range(len(A))]
def times(A,B):
    return [[sum(x*y for x,y in zip(a,b))%P for b in zip(*B)]for a in A]
def tr(A,B):return sum(x*y for a,b in zip(A,zip(*B))for x,y in zip(a,b))%P

mons=[(0,0),(1,0),(0,1),(2,0),(1,1),(0,2)]

def conditions(m,omit,detail=False):
    bas=mons[:omit]+mons[omit+1:];saved=mons[omit]
    keys=lambda a,b:(a[0]+b[0],a[1]+b[1])
    G=[[m[keys(a,b)] for b in bas]for a in bas]
    d=determinant(G);A=adj(G)
    v=[[m[keys(a,saved)]]for a in bas];cv=times(A,v)
    conic={saved:d,**{z:-r[0]%P for z,r in zip(bas,cv)}}
    system=[];rhs=[]
    def equation(weights):
        system.append([weights.get((5-i,i),0)%P for i in range(6)])
        rhs.append(-sum(co*m[a]for a,co in weights.items()if sum(a)<=4)%P)
    for j in range(4):
        equation({(x+3-j,y+j):co for (x,y),co in conic.items()})
    mats=[]
    for xy in [(1,0),(0,1)]:
        w={}
        ids=[[keys(keys(a,b),xy)for b in bas]for a in bas];mats.append(ids)
        for i in range(5):
            for j in range(5):
                k=ids[i][j];w[k]=(w.get(k,0)+A[j][i])%P
        equation(w)
    den=determinant(system)
    full={k:den*x%P for k,x in m.items()}
    for i in range(6):full[5-i,i]=determinant([r[:i]+[v]+r[i+1:]for r,v in zip(system,rhs)])
    if detail:return [den]+[full[5-i,i]for i in range(6)]
    N=[times(A,[[full[k]for k in row]for row in mat])for mat in mats]
    p0=(den*d)**2%P
    return [(tr(N[0],N[0])-p0*m[2,0])%P,(tr(N[0],N[1])-p0*m[1,1])%P,
            (tr(N[1],N[1])-p0*m[0,2])%P]

def trim(f):
    while f and not(f[-1]%P):f.pop()
    return f
def divrem(f,g):
    f=f[:];b=inv(g[-1]);n=len(g)
    while len(f)>=n:
        j=len(f)-n;t=f[-1]*b%P
        for i,x in enumerate(g):f[j+i]=(f[j+i]-t*x)%P
        trim(f)
    return f
def gcd(f,g):
    f=trim(f[:]);g=trim(g[:])
    while g:f,g=g,divrem(f,g)
    return scale(f,inv(f[-1])) if f else []
def interp(xs,ys):
    # Newton divided differences converted to the monomial basis.
    v=ys[:];a=[]
    for n in range(len(xs)):
        a.append(v[0]);v=[(v[j+1]-v[j])*inv(xs[j+n+1]-xs[j])%P for j in range(len(v)-1)]
    f=[a[-1]]
    for i in reversed(range(len(xs)-1)):
        f=mul(f,[-xs[i],1]);f[0]=(f[0]+a[i])%P
    return trim(f)

C=[-2200*inv(249318)%P,39285*inv(249318)%P,-59049*inv(249318)%P]
def cval(t):return (C[0]+C[1]*t+C[2]*t*t)%P

def table(n,detail=False):
    sq={x*x%P:x for x in range(P)}
    roots={}
    for x in range(P):
        aa=C[2];bb=(C[1]-x)%P;cc=(C[0]-x**3+x*x)%P
        disc=(bb*bb-4*aa*cc)%P
        if disc not in sq:continue
        for t in {(-bb+s*sq[disc])*inv(2*aa)%P for s in (-1,1)}:
            roots.setdefault(t,[]).append(x)
    chosen=sorted(t for t,r in roots.items()if len(r)==3 and cval(t))[:n]
    assert len(chosen)==n
    for t in chosen:
        rows=[]
        for a,b,c in permutations(roots[t]):
            m=moment_roots(a,b,c)
            H=[[m[x+u,y+v]for u,v in mons]for x,y in mons]
            assert determinant(H)==0
            vals=sum([conditions(m,omit,detail) for omit in (3,4,5)],[])
            rows.append([v*w%P for w in (1,a,b,a*b,a*a,a*a*b)for v in vals])
        yield t,[sum(g)%P for g in zip(*rows)]

def ev(f,x):
    out=0
    for v in reversed(f):out=(out*x+v)%P
    return out
def split(f):
    roots=[]
    while len(f)>1:
        z=next((i for i in range(P)if ev(f,i)==0),None)
        assert z is not None
        g=[f[-1]]
        for a in reversed(f[1:-1]):g.insert(0,(a+z*g[0])%P)
        roots.append(z);f=g
    return Counter(roots)
from collections import Counter
# A direct 17-by-17-by-17 polynomial identity proves the determinant restriction.
def check_catalecticant():
    for a,b,c in product(range(17),repeat=3):
        forms=[[c,0],[0,c],[-a,-b]]
        m=moment_quadrics([mul(f,f)for f in forms],mul(mul(forms[0],forms[1]),forms[2]))
        H=[[m[x+u,y+v]for u,v in mons]for x,y in mons]
        x,y,z=a*a,b*b,c*c;A=x+y+z;B=x*y+y*z+z*x;C=x*y*z
        rhs=16000000*inv(177147)*c**8*(-2200*A**4+39285*A*A*B-59049*B*B-249318*A*C)
        assert (determinant(H)-rhs)%P==0
def c_zero(t):
    # x=n2*n3 X, y=n3 Y, z=-n2 Y; all required sums symmetric in n2^2,n3^2.
    m2=scale([t,0,1],-20*inv(3))
    m3=scale([0,0,-t,0],-60)
    q4=[t*t,0,0,0,1-2*t]
    products=[0,0,t,0,t]
    m4=add(scale(q4,260*inv(9)),scale(products,-200*inv(9)))
    return {(d-j,j): x*inv(comb(d,j))%P for d,m in enumerate([[5],[0,0],m2,m3,m4])for j,x in enumerate(m)}
def inconsistent(m):
    for o in (3,4,5):
        r=conditions(m,o);h=conditions(m,o,True)
        if any(r) or (not h[0] and any(h[1:])):return True
    return False

def interpolate_columns(data, count):
    xs=[x for x,_ in data];ys=[y for _,y in data]
    polynomials=[]
    for k in range(len(ys[0])):
        f=interp(xs[:count],[row[k]for row in ys[:count]])
        assert all(ev(f,t)==row[k]for t,row in data[count:])
        polynomials.append(f)
    return polynomials

def verify_isotropic_normal():
    m={(d-j,j):v for d,row in enumerate([[5],[0,0],[-20,0,0],[-60,0,0,-60],[20,0,0,120,0]])
        for j,v in enumerate(row)}
    h=[[m[x+i,y+j]for i,j in mons]for x,y in mons]
    assert determinant([r[:4]+r[5:]for k,r in enumerate(h)if k!=4])==21661
    assert all((2*row[2]+row[4])%P==0 for row in h)
    derivative=5*(-2)**4+30*(-2)**2+40*(-2)+45
    assert derivative==165 and derivative%P
    print('Isotropic normal excluded by the conic t(s+2)=0 and the simple root test.')

def main():
    assert all(P%d for d in range(2,isqrt(P)+1))
    check_catalecticant()
    print('Homogeneous catalecticant identity verified on a degree-16 interpolation grid.')
    polys=interpolate_columns(list(table(162)),158)
    common=[]
    for f in polys:common=gcd(common,f)
    roots=split(common)
    assert roots==Counter({12224:28,25076:38,45496:1,57004:1})
    print('The common degree-68 polynomial has roots and multiplicities',sorted(roots.items()))
    zeroroots=split(C)
    assert set(zeroroots)=={12224,25076}
    for t in zeroroots:
        assert inconsistent(c_zero(t))
    print('Both zero-coordinate branches excluded by direct moments.')
    polys=interpolate_columns(list(table(75,True)),73)
    for t in set(roots)-set(zeroroots):
        disc=(t*t-4*t**3-4*cval(t)-27*cval(t)**2+18*t*cval(t))%P
        assert disc
        traces=[ev(f,t)for f in polys]
        for o in range(3):
            den=[traces[k*21+o*7]for k in range(6)]
            num=[traces[k*21+o*7+j]for k in range(6)for j in range(1,7)]
            if not any(den) and any(num):
                print('Inconsistent degree-five system at',t,'with numerator trace',next(x for x in num if x))
                break
        else:raise AssertionError(('uncertified normal',t))
    verify_isotropic_normal()
    print('All projective row-plane normals excluded over the algebraic closure of F_65521.')

if __name__=='__main__':
    main()
