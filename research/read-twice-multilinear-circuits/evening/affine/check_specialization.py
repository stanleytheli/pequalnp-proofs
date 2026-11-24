"""Check normalized path weights directly and the complete HC specialization.

No symbolic algebra packages are needed. The large graph contraction accepts only
a physical edge list and explicit unary weights. Run with --physical to include
that separate cross-check, using the companion graph-transfer programs.
"""
from functools import lru_cache
from itertools import product
from pathlib import Path
import argparse
import sys


class Field:
    """Fp or F2[X]/modulus, packed in the low bits."""
    def __init__(self, order, modulus=None):
        self.order = order
        self.modulus = modulus

    def add(self, a, b):
        return (a ^ b) if self.modulus else (a + b) % self.order

    def neg(self, a):
        return a if self.modulus else -a % self.order

    def sub(self, a, b):
        return self.add(a, self.neg(b))

    @lru_cache(maxsize=None)
    def mul(self, a, b):
        if not self.modulus:
            return a * b % self.order
        result = 0
        while b:
            if b & 1:
                result ^= a
            b >>= 1
            a <<= 1
            if a & self.order:
                a ^= self.modulus
        return result

    def prod(self, values):
        y = 1
        for x in values:
            y = self.mul(y, x)
        return y

    def power(self, x, n):
        return self.prod([x]*n)

    def div(self, a, b):
        if b == 0:
            raise ZeroDivisionError
        inverse = self.power(b, self.order - 2)
        assert self.mul(inverse, b) == 1
        return self.mul(a, inverse)


class Quadratic(Field):
    """Fp[w]/(w²-nonsquare); a+b*w is stored as a+p*b."""
    def __init__(self, p, nonsquare):
        super().__init__(p*p)
        assert nonsquare not in {i*i % p for i in range(p)}
        self.p = p
        self.nonsquare = nonsquare

    def add(self, a, b):
        p = self.p
        return (a%p+b%p)%p + p*((a//p+b//p)%p)

    def neg(self,a):
        p = self.p
        return (-a%p) + p*((-(a//p))%p)

    @lru_cache(maxsize=None)
    def mul(self,a,b):
        p = self.p
        a1,a0 = divmod(a,p)
        b1,b0 = divmod(b,p)
        return (a0*b0+self.nonsquare*a1*b1)%p + p*((a0*b1+a1*b0)%p)


def gadget(f, t, u, data):
    continuants = [1, f.add(1,t)]
    for _ in range(2,7):
        continuants.append(f.add(continuants[-1], f.mul(t,continuants[-2])))
    C, B = continuants[5:7]
    A = f.div(f.power(t,6),C)
    r, s = u, 1 if data else u
    delta = f.sub(f.sub(1,r),s)
    a = f.div(f.mul(delta,B), f.mul(r,C))
    b = f.div(f.mul(delta,A), f.mul(s,C))
    inside = [a] + [t]*6 + [f.div(f.neg(B),C), b]
    p = [f.div(z,f.add(1,z)) for z in inside]
    scalar = f.div(f.prod((delta,A,B)), f.prod((r,s,C)))
    scalar = f.mul(scalar, f.prod(f.sub(1,v) for v in p))
    if scalar == 0:
        raise ZeroDivisionError
    return p, scalar


def find(f):
    for t,u in product(range(1,f.order),repeat=2):
        try:
            gadgets = [gadget(f,t,u,data) for data in (False,True)]
            for c,d in product((0,1,f.neg(1)),(1,2,3)):
                f.div(1,f.add(f.power(u,d),c))
        except ZeroDivisionError:
            continue
        return t,u,gadgets
    return None


def exhaustive(f,p,left,right):
    value = 0
    for bits in product((0,1),repeat=len(p)):
        states = (left,) + bits + (right,)
        if any(a and b for a,b in zip(states,states[1:])):
            continue
        term = f.prod(pi if bit else f.sub(1,pi) for pi,bit in zip(p,bits))
        value = f.add(value,term)
    return value


def check_paths():
    fields = [Field(2),Field(3),Field(4,0b111),Field(5),Field(7),Field(8,0b1011),
              Field(11),Field(13),Field(16,0b10011),Field(17),Field(19),Field(23),
              Field(29),Field(31),Field(32,0b100101),Field(37),Field(67),Field(101),Field(167),
              Quadratic(3,2),Quadratic(5,2),Quadratic(7,3)]
    for f in fields:
        found = find(f)
        if not found:
            print(f'q={f.order}: no compatible pair for both signatures and all degrees 1..3')
            continue
        t,u,gadgets = found
        for data,(ps,scalar) in enumerate(gadgets):
            target = [1,1 if data else u,u,0]
            for left,right in product((0,1),repeat=2):
                assert exhaustive(f,ps,left,right) == f.mul(scalar,target[2*left+right])
        print(f'q={f.order} t={t} u={u}: all 8 path entries verified by spin enumeration')


def check_physical(orders,prime,quadratic=False,expand=False):
    sys.path.insert(0,str(Path(__file__).resolve().parents[2]/'graph-transfer'))
    from hamiltonian_seed import WeightedGraph, hc_seed, split_degree
    from check_contraction import contract, cycles
    if quadratic:
        from quadratic_seed import seed as hc_seed
    f = Field(prime)
    t,u,gadgets = find(f)
    for n in orders:
        source = hc_seed(n,probability_leaves=True)
        initial_parity = 0
        if expand:
            from expander_overlay import overlay
            initial_parity = 2*len(source.edges)-len(source.labels)
            source = overlay(split_degree(source))
        base = split_degree(source)
        tensor = WeightedGraph()
        matrix = [[(7*i+11*j+3*i*j+13)**2+3 for j in range(n)] for i in range(n)]
        physical_inputs = []
        def add_vertex(p):
            vertex = tensor.vertex(('prob',0,len(physical_inputs)))
            physical_inputs.append(f.sub(1,p))
            return vertex
        parity = initial_parity + 2*len(source.edges)-len(source.labels)
        scalar = f.power(f.neg(1), parity%2)
        degrees = base.degrees()
        leaves = set()
        for i,(c,d) in enumerate(zip(base.labels,degrees)):
            if isinstance(c,tuple):
                kind,row,col = c
                assert kind == 'prob' and d == 1
                leaves.add(i)
                add_vertex(f.sub(1,matrix[row][col] % prime))
            else:
                p = f.div(c % prime,f.add(f.power(u,d),c % prime))
                add_vertex(p)
                scalar = f.mul(scalar,f.sub(1,p))
        for a,b in base.edges:
            if a in leaves:
                a,b = b,a
            ps,kappa = gadgets[b in leaves]
            scalar = f.mul(scalar,kappa)
            prev = a
            for p in ps:
                w = add_vertex(p)
                tensor.edge(prev,w)
                prev = w
            tensor.edge(prev,b)
        obtained,width = contract(tensor,[physical_inputs],prime)
        assert scalar != 0
        got = f.div(obtained,scalar)
        expected = cycles(matrix,prime)
        assert got == expected,(got,expected)
        print(f'n={n}, F_{prime}, t={t}, u={u}, variables={len(tensor.labels)}, '
              f'edges={len(tensor.edges)}, width={width}, Q={obtained}, scalar={scalar}, HC={expected}',flush=True)


if __name__ == '__main__':
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--physical', nargs='+', type=int)
    parser.add_argument('--prime',type=int,default=101)
    parser.add_argument('--quadratic',action='store_true')
    parser.add_argument('--expand',action='store_true')
    args = parser.parse_args()
    if args.physical:
        check_physical(args.physical,args.prime,args.quadratic,args.expand)
    else:
        check_paths()
