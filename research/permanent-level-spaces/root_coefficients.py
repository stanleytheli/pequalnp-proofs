"""Exact mixed coefficient at the highest Fourier frequency of a second additive direction."""
from math import comb
from fractions import Fraction
from sys import argv

def coefficient(n,t,b):
    a=2*n-t*b
    k=a+b
    if a<0 or not 1<=k<=n:return None
    def h(x,y):
        return Fraction(n*comb(x+y,y),x+y)
    base=-2*h(a,b)
    for x in range(b+1):
        p=n-t*x
        q=a-p
        if min(p,q)<0:continue
        r=p+x;s=q+b-x
        c=Fraction(comb(n-r,s),comb(n,s))
        base+=(1-c)*h(p,x)*h(q,b-x)
    return (-1)**k*base

def scan(maximum):
    zeros=[];missing=[];negative=0
    for n in range(2,maximum+1):
        for t in range(2,n):
            b=(n+t-2)//(t-1)
            v=coefficient(n,t,b)
            if not v:
                alt=next(((j,k) for j in range(b+1,2*n//t+1) if (k:=coefficient(n,t,j))),None)
                zeros.append((n,t,b,alt))
                if not alt:missing.append((n,t))
            elif ((-1)**(2*n-t*b+b))*v<0:negative+=1
    print('first coefficient zero',len(zeros),'missing',len(missing),'negative unsigned',negative)
    print('first exceptions',zeros[:20])
if __name__=='__main__':scan(int(argv[1]) if len(argv)>1 else 50)
