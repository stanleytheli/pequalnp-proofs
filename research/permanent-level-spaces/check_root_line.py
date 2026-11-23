"""Compare the coefficient formula to the permanent definition over small prime fields."""
from itertools import count
from math import factorial,isqrt
from root_coefficients import coefficient

def prime(p):
    return p>=2 and all(p%d for d in range(2,isqrt(p)+1))

def root(n):
    p=next(2*n*k+1 for k in count(1) if 2*n*k+1>500 and prime(2*n*k+1))
    divisors=[j for j in range(1,2*n) if (2*n)%j==0]
    c=next(v for v in range(1,p) if pow(v,2*n,p)==1 and all(pow(v,j,p)!=1 for j in divisors))
    return p,c

def permanent_coefficient(n,t,a,b,p,c):
    vals=[pow(c,2*i,p) for i in range(n)]
    other=[v*c%p for v in vals]
    states={0:{(0,0):1}}
    for i in range(n):
        nxt={}
        for mask,coeffs in states.items():
            for j in range(n):
                if mask>>j&1:continue
                target=nxt.setdefault(mask|1<<j,{})
                d=(vals[i]+other[j])%p
                x=(pow(vals[i],t,p)+pow(other[j],t,p))%p
                for (h,k),v in coeffs.items():
                    target[h,k]=(target.get((h,k),0)+v)%p
                    if h<a:target[h+1,k]=(target.get((h+1,k),0)+d*v)%p
                    if k<b:target[h,k+1]=(target.get((h,k+1),0)+x*v)%p
        states=nxt
    return states[(1<<n)-1].get((a,b),0)*pow(factorial(n),-1,p)%p

def main():
    tests=0
    for n in range(3,12):
        p,c=root(n)
        for t in range(2,n):
            b=2*n//t;a=2*n-t*b
            formula=coefficient(n,t,b)
            assert formula and (a+b)<=n
            predicted=formula.numerator*pow(formula.denominator,-1,p)%p
            result=permanent_coefficient(n,t,a,b,p,c)
            assert predicted==result,(n,t,p,a,b,result,predicted)
            tests+=1
    print('Checked',tests,'coefficients directly from the square permanent for n=3 through 11.')

if __name__=='__main__':main()
