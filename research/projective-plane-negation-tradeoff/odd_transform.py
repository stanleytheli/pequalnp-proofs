"""Exact Fourier-slice controls for odd prime powers, with a bit-gate realization at q=3."""
from itertools import product
from math import isqrt
from random import Random
from fourier_circuit import Circuit, Dual


def prime(n):
    return n>=2 and all(n%d for d in range(2,isqrt(n)+1))


def factors(n):
    return [p for p in range(2,n+1) if n%p==0 and prime(p)]


class Field:
    def __init__(self,p,lower):
        self.p=p
        self.mod=lower
        self.a=len(lower)
        self.q=p**self.a

    def digits(self,x):
        return [(x//self.p**i)%self.p for i in range(self.a)]

    def pack(self,d):
        return sum((v%self.p)*self.p**i for i,v in enumerate(d))

    def add(self,u,v):
        return self.pack([a+b for a,b in zip(self.digits(u),self.digits(v))])

    def mul(self,u,v):
        out=[0]*(2*self.a-1)
        for i,a in enumerate(self.digits(u)):
            for j,b in enumerate(self.digits(v)):
                out[i+j]+=a*b
        for k in reversed(range(self.a,len(out))):
            for i in range(self.a):
                out[k-self.a+i]-=out[k]*self.mod[i]
        return self.pack(out[:self.a])

    def dual_negative(self,slope,v):
        v_digits=self.digits(v)
        return self.pack([-sum(a*b for a,b in zip(v_digits,self.digits(self.mul(slope,self.p**i)))) for i in range(self.a)])


class Scalar:
    def __init__(self,ell):
        self.ell=ell
        self.zero=0
    def add(self,a,b): return (a+b)%self.ell
    def mul(self,k,a): return (k*a)%self.ell


class Gates:
    def __init__(self,g,ell):
        self.ar=Dual(g)
        self.ell=ell
        self.size=ell.bit_length()
        self.zero=self.const(0)

    def const(self,c):
        return [self.ar.one if (c>>i)&1 else self.ar.zero for i in range(self.size)]

    def add(self,a,b):
        # x=a+b<2ℓ. Subtract ℓ in one extra bit; its sign bit selects x or x−ℓ.
        ar=self.ar
        x=ar.add(a+[ar.zero],b+[ar.zero])
        diff=ar.add(x,self.const(self.ell)+[ar.zero],True)
        sign=diff[-1]
        return [ar.either(ar.both(sign,v),ar.both(sign[::-1],w)) for v,w in zip(x[:-1],diff[:-1])]

    def mul(self,k,a):
        k%=self.ell
        if k==1: return a
        acc=self.zero
        while k:
            if k&1: acc=self.add(acc,a)
            k//=2
            if k: a=self.add(a,a)
        return acc


class Fourier:
    def __init__(self,field):
        self.field=field
        q,p=field.q,field.p
        multiple=q*(1<<(2*q-1).bit_length())
        ell=1+multiple
        while not prime(ell): ell+=multiple
        self.ell=ell
        self.scalar=Scalar(ell)
        fs=factors(ell-1)
        generator=next(a for a in range(2,ell) if all(pow(a,(ell-1)//f,ell)!=1 for f in fs))
        self.omega=pow(generator,(ell-1)//p,ell)
        n=1<<(2*p-2).bit_length()
        self.radix=pow(generator,(ell-1)//n,ell)
        self.n=n

    def fft(self,values,root,op):
        n=len(values)
        if n==1: return values
        er=self.fft(values[::2],root*root%self.ell,op)
        oi=self.fft(values[1::2],root*root%self.ell,op)
        t=1
        high=[]; low=[]
        for a,b in zip(er,oi):
            low.append(op.add(a,op.mul(t,b)))
            high.append(op.add(a,op.mul(-t,b)))
            t=t*root%self.ell
        return low+high

    def digit(self,v,inverse,op):
        p=self.field.p; ell=self.ell
        w=pow(self.omega,-1,ell) if inverse else self.omega
        if p<=3:
            # A fixed-size base case, including the bit-gate control.
            out=[]
            for k in range(p):
                a=op.zero
                for j,x in enumerate(v): a=op.add(a,op.mul(pow(w,j*k,ell),x))
                out.append(a)
            return out
        half=pow(2,-1,p)
        chirp=lambda i: pow(w,(i*i*half)%p,ell)
        n=self.n
        signal=[op.mul(chirp(j),v[j]) for j in range(p)]+[op.zero]*(n-p)
        kernel=[0]*n
        for i in range(1-p,p): kernel[i%n]=pow(chirp(i),-1,ell)
        ks=self.fft(kernel,self.radix,self.scalar)
        fs=self.fft(signal,self.radix,op)
        prod=[op.mul(k,x) for k,x in zip(ks,fs)]
        conv=self.fft(prod,pow(self.radix,-1,ell),op)
        return [op.mul(chirp(j)*pow(n,-1,ell),conv[j]) for j in range(p)]

    def transform(self,v,inverse,op):
        p=self.field.p
        stride=1; out=list(v)
        while stride<len(out):
            for start in range(0,len(out),stride*p):
                for offset in range(stride):
                    idx=[start+offset+i*stride for i in range(p)]
                    block=self.digit([out[i] for i in idx],inverse,op)
                    for i,x in zip(idx,block): out[i]=x
            stride*=p
        if inverse: return [op.mul(pow(len(out),-1,self.ell),x) for x in out]
        return out

    def line_counts(self,v,op):
        q=self.field.q
        spectrum=self.transform(v,False,op)
        output=[]
        for a in range(q+1):
            if a==q: sliced=[spectrum[x*q] for x in range(q)]
            else: sliced=[spectrum[self.field.dual_negative(a,x)*q+x] for x in range(q)]
            output+=self.transform(sliced,True,op)
        return output


def direct(field,pins):
    q=field.q
    rows=[]
    for a,z in product(range(q+1),range(q)):
        if a==q: rows.append(sum(pins[z*q:z*q+q]))
        else: rows.append(sum(pins[x*q+field.add(field.mul(a,x),z)] for x in range(q)))
    return rows


def run():
    rng=Random(314)
    for p,mod in [(3,[0]),(5,[0]),(7,[0]),(3,[1,0]),(11,[0]),(5,[2,0])]:
        f=Field(p,mod); q=f.q; calc=Fourier(f)
        for j in range(6):
            inp=[int(j==0 or (j>1 and rng.randrange(2))) for _ in range(q*q)]
            assert calc.line_counts(inp,calc.scalar)==direct(f,inp)
        print(f'q={q}, modular field={calc.ell}, every affine line matched direct counts in six controls')
    f=Field(3,[0]); q=3; n=13; calc=Fourier(f)
    g=Circuit(n); rails=g.inverter(); op=Gates(g,calc.ell)
    words=[[r]+[op.ar.zero]*(op.size-1) for r in rails[:q*q]]
    counts=calc.line_counts(words,op)
    outs=[g.disj(g.reduce_or([b[0] for b in word]),rails[q*q+i//q][0]) for i,word in enumerate(counts)]
    outs.append(g.reduce_or([r[0] for r in rails[q*q:]]))
    # Distribute cases into machine-word batches to bound netlist evaluation memory.
    batch=128
    for start in range(0,2**n,batch):
        raw=[sum(((x>>i)&1)<<(x-start) for x in range(start,start+batch)) for i in range(n)]
        got=g.packed(raw,batch,outs)
        for k in range(batch):
            bits=[(start+k)>>i&1 for i in range(n)]
            expect=[int(v>0 or bits[q*q+j//q]) for j,v in enumerate(direct(f,bits))]+[int(any(bits[q*q:]))]
            assert expect==[(v>>k)&1 for v in got]
    print(f'q=3 actual netlist: {len(g.gates)} gates, {sum(k=="not" for k,_ in g.gates)} NOTs, all 8192 inputs and 13 outputs')

if __name__=='__main__': run()
