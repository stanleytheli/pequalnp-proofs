"""Emit/evaluate an explicit near-linear, logarithmic-NOT finite-plane OR circuit.

All emitted gates have fan-in at most two. The monolithic inverter supplies the
dual rails for the later Walsh butterflies. No numerical approximation is used.
"""
from itertools import product
from random import Random
from argparse import ArgumentParser


class Circuit:
    def __init__(self,n):
        self.n = n
        self.gates = []
        self.cache = {}
        self.zero = self.add('false')
        self.one = self.add('true')

    def add(self,op,*args):
        wire = self.n + len(self.gates)
        self.gates.append((op,args))
        return wire

    def positive(self,op,a,b):
        if a == b:
            return a
        if op=='and':
            if self.zero in (a,b): return self.zero
            if a==self.one: return b
            if b==self.one: return a
        else:
            if self.one in (a,b): return self.one
            if a==self.zero: return b
            if b==self.zero: return a
        key = (op,*sorted((a,b)))
        if key not in self.cache:
            self.cache[key] = self.add(*key)
        return self.cache[key]

    def conj(self,a,b): return self.positive('and',a,b)
    def disj(self,a,b): return self.positive('or',a,b)

    def reduce_or(self,wires):
        value = self.zero
        for w in wires: value = self.disj(value,w)
        return value

    def inverter(self):
        size = 1
        while size<self.n: size *= 2
        rows = list(range(self.n)) + [self.zero]*(size-self.n)
        comparators = []
        block = 2
        while block<=size:
            stride = block//2
            while stride:
                for i in range(size):
                    j = i^stride
                    if j<=i: continue
                    a,b = rows[i],rows[j]
                    high,low = self.disj(a,b),self.conj(a,b)
                    descending = (i&block)==0
                    rows[i],rows[j] = (high,low) if descending else (low,high)
                    comparators.append((i,j,a,b,descending))
                stride //= 2
            block *= 2
        active = [self.one]
        for k in reversed(range(self.n.bit_length())):
            wires = []
            for prefix,enable in enumerate(active):
                threshold = ((2*prefix+1)<<k)
                if threshold<=self.n:
                    wires.append(self.conj(enable,rows[threshold-1]))
            bit = self.reduce_or(wires)
            opposite = self.add('not',bit)
            active = [self.conj(enable,choice) for enable in active for choice in (opposite,bit)]
        sorted_neg = []
        below = self.zero
        for j in range(size):
            if j<=self.n: below = self.disj(below,active[j])
            sorted_neg.append(below)
        for i,j,a,b,descending in reversed(comparators):
            not_or,not_and = (sorted_neg[i],sorted_neg[j]) if descending else (sorted_neg[j],sorted_neg[i])
            sorted_neg[i] = self.disj(not_or,self.conj(not_and,b))
            sorted_neg[j] = self.disj(not_or,self.conj(not_and,a))
        return [(j,sorted_neg[j]) for j in range(self.n)]

    def packed(self,inputs,count,wires):
        allbits = (1<<count)-1
        vals = inputs.copy()
        for op,ids in self.gates:
            if op=='and': value = vals[ids[0]] & vals[ids[1]]
            elif op=='or': value = vals[ids[0]] | vals[ids[1]]
            elif op=='not': value = allbits ^ vals[ids[0]]
            else: value = allbits if op=='true' else 0
            vals.append(value)
        return [vals[w] for w in wires]


class Dual:
    def __init__(self,circuit):
        self.g = circuit
        self.zero = (circuit.zero,circuit.one)
        self.one = self.zero[::-1]

    def both(self,a,b): return self.g.conj(a[0],b[0]),self.g.disj(a[1],b[1])
    def either(self,a,b): return self.g.disj(a[0],b[0]),self.g.conj(a[1],b[1])
    def xor(self,a,b):
        return (self.g.disj(self.g.conj(a[0],b[1]),self.g.conj(a[1],b[0])),
                self.g.disj(self.g.conj(a[0],b[0]),self.g.conj(a[1],b[1])))

    def add(self,a,b,subtract=False):
        carry = self.one if subtract else self.zero
        out = []
        for x,y in zip(a,b):
            if subtract: y = y[::-1]
            z = self.xor(x,y)
            out.append(self.xor(z,carry))
            carry = self.either(self.both(x,y),self.both(z,carry))
        return out

    def walsh(self,words):
        w = words.copy()
        stride=1
        while stride < len(w):
            for i in range(len(w)):
                if not i&stride:
                    j=i+stride
                    a,b=w[i],w[j]
                    w[i],w[j]=self.add(a,b),self.add(a,b,True)
            stride *= 2
        return w


def gf_mul(a,b,q,poly):
    result=0
    while b:
        if b&1: result ^= a
        a <<= 1
        if a&q: a ^= poly
        b >>= 1
    return result


def dual_image(a,v,b,poly):
    """M_a transpose times v in the polynomial basis."""
    return sum(((bin(gf_mul(a,1<<i,1<<b,poly)&v).count('1')%2)<<i) for i in range(b))


def plane_circuit(b,poly):
    q = 1<<b
    g = Circuit(q*q+q+1)
    rails = g.inverter()
    ar = Dual(g)
    width = 2*b+1
    plane = [[bit]+[ar.zero]*(width-1) for bit in rails[:q*q]]
    spectrum = ar.walsh(plane)
    outputs=[]
    for a in range(q+1):
        if a==q:
            trace=[spectrum[v*q] for v in range(q)]
        else:
            trace=[spectrum[dual_image(a,v,b,poly)*q+v] for v in range(q)]
        counts = ar.walsh(trace)
        for word in counts:
            nonzero = g.reduce_or(bit[0] for bit in word)
            outputs.append(g.disj(nonzero,rails[q*q+a][0]))
    outputs.append(g.reduce_or(bit[0] for bit in rails[q*q:]))
    return g,outputs


def direct(pins,b,poly):
    q = 1<<b
    out=[]
    for a,z in product(range(q+1),range(q)):
        v = pins[q*q+a]
        for x in range(q):
            pos = z*q+x if a==q else x*q+(gf_mul(a,x,q,poly)^z)
            v |= pins[pos]
        out.append(v)
    v=0
    for val in pins[q*q:]: v |= val
    return out+[v]


def check(b,poly,seed=191):
    q=1<<b
    n=q*q+q+1
    g,outputs=plane_circuit(b,poly)
    rng=Random(seed)
    masks = list(range(1<<n)) if n<=8 else [0,(1<<n)-1]+[1<<i for i in range(n)]
    if n>8:
        masks.extend(rng.getrandbits(n) for _ in range(50))
        masks.extend(sum(1<<i for i in rng.sample(range(n),k)) for k in range(2,q+2) for _ in range(15))
    packed = [sum(((m>>i)&1)<<j for j,m in enumerate(masks)) for i in range(n)]
    assert g.packed(packed,len(masks),outputs)==direct(packed,b,poly)
    neg=sum(op=='not' for op,args in g.gates)
    assert neg==n.bit_length()
    print(f'q={q}, n={n}, gates={len(g.gates)}, NOT={neg}, cases={len(masks)}, all {n} outputs verified',flush=True)


if __name__=='__main__':
    p=ArgumentParser(description=__doc__)
    p.add_argument('--bits',type=int,nargs='+',default=[1,2,3])
    args=p.parse_args()
    polys={1:0b11,2:0b111,3:0b1011,4:0b10011,5:0b100101,6:0b1000011}
    for b in args.bits: check(b,polys[b])
