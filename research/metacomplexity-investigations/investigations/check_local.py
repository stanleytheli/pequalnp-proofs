"""Build the actual fan-in-two threshold DAG and audit the three-symbol encoding."""
from itertools import combinations, product
from math import comb


class Gates:
    def __init__(self, n):
        self.n = n
        self.operations = []

    def gate(self, op, *parents):
        v = self.n+len(self.operations)
        self.operations.append((op,parents))
        return v

    def xor_and(self, a,b):
        shared = self.gate("and",a,b)
        union = self.gate("or",a,b)
        complementary = self.gate("not",shared)
        return self.gate("and",union,complementary), shared

    def add(self,a,b,c):
        half,ab = self.xor_and(a,b)
        total,hc = self.xor_and(half,c)
        return total,self.gate("or",ab,hc)

    def evaluate(self,x,out):
        trace = [(x >> i)&1 for i in range(self.n)]
        for op,parents in self.operations:
            if op == "and":
                v = all(trace[i] for i in parents)
            elif op == "or":
                v = any(trace[i] for i in parents)
            else:
                v = not trace[parents[0]]
            trace.append(int(v))
        return trace[out]


def threshold(n,t):
    assert 1 <= t <= n
    net = Gates(n)
    zero = net.gate("or")
    one = net.gate("and")
    width = n.bit_length()
    columns = [list(range(n))]+[[] for _ in range(width)]
    for i,col in enumerate(columns[:-1]):
        while len(col) >= 3:
            low,carry = net.add(col.pop(),col.pop(),col.pop())
            col.append(low)
            columns[i+1].append(carry)
    assert not columns[-1]
    carry = zero
    accept = one
    for i,col in enumerate(columns[:-1]):
        col = col+[zero]*(2-len(col))
        total,carry = net.add(*col,carry)
        accept = net.gate("and" if (t >> i)&1 else "or",total,accept)
    assert len(net.operations) <= 9*n+10*width+10
    return net,accept


def gadget(q):
    def row(x):
        u = [(x >> i)&1 for i in range(q)]
        v = [(x >> (i+q))&1 for i in range(q)]
        star = any(u[i] and all(not v[j] for j in range(q) if i!=j) for i in range(q))
        val = any(v[j] and not u[j] for j in range(q))
        assert not (star and val)
        return 0 if star else (2 if val else 1)
    vals = [row(x) for x in range(1 << (2*q))]
    assert vals[0] == 1 and all(vals[1 << i] == (0 if i<q else 2) for i in range(2*q))
    # Exhaust every input and find a literal certificate for each encoded bit.
    for transform in (lambda s:s!=0, lambda s:s==2):
        bits = list(map(transform,vals))
        masks = [sum(1 << i for i in coords) for coords in combinations(range(2*q),q)]
        for x,v in enumerate(bits):
            assert any(all(bits[y]==v for y in range(len(bits)) if (x&mask)==(y&mask)) for mask in masks)


def valid_word(word):
    length = len(word)
    for a in range(length.bit_length()):
        s = length-1-2*(2**a)
        if s < 0:
            continue
        if word[:s] == (1,)*s and word[s] == 0:
            suffix = word[s+1:]
            if all(suffix[i] or not suffix[i+1] for i in range(0,len(suffix),2)):
                return s,a
    return None


def format_checks():
    count = 0
    for size in range(10):
        words = list(product((0,1),repeat=size))
        valid = {v:valid_word(v) for v in words if valid_word(v) is not None}
        candidates = sorted({s for s,a in valid.values()})
        for v in words:
            fmt = valid.get(v)
            if fmt is None:
                banned = set()
                for s in candidates:
                    if 0 in v[:s]:
                        banned.add(v.index(0))
                    elif v[s] == 1:
                        banned.add(s)
                    else:
                        j = next(j for j in range(s+1,size,2) if v[j:j+2]==(0,1))
                        banned.update((j,j+1))
                assert len(banned) <= 2*len(candidates)
                assert all(any(w[i]!=v[i] for i in banned) for w in valid)
            else:
                pins = [s for s in candidates if s<=fmt[0]]
                assert all(fmt==other or any(w[i]!=v[i] for i in pins) for w,other in valid.items())
            count += 1
    return count


def sample_count():
    # Exact, independent multisample enumeration for the sufficient counting bound.
    n,k,t = 7,3,2
    positive = [{0},{1}]
    negative = [{0,1},{2,3}]
    total = n**k
    missed = sum(any(sum(j in s for j in sample) >= k-t+1 for s in positive)
                 or any(sum(j in s for j in sample) >= t for s in negative)
                 for sample in product(range(n),repeat=k))
    upper = sum(comb(k,k-t+1)*len(s)**(k-t+1)*n**(t-1) for s in positive)
    upper += sum(comb(k,t)*len(s)**t*n**(k-t) for s in negative)
    assert missed <= upper < total
    return total-missed


def cyclic_sat_checks():
    cases = 0
    for n in range(3,9):
        for z in product((0,1),repeat=n):
            clauses = []
            for i,bit in enumerate(z):
                a,b = i+1,(i+1)%n+1
                if i == 0:
                    bit ^= 1
                clauses.extend([(-a,-b if bit else b),(a,b if bit else -b)])
            count = 0
            for x in range(1 << n):
                def literal(v):
                    return bool(x & (1 << (abs(v)-1))) == (v > 0)
                count += all(literal(a) or literal(b) for a,b in clauses)
            assert count == (2 if sum(z)%2 else 0)
            cases += 1
    return cases


if __name__ == "__main__":
    assignments = 0
    for n in range(1,11):
        for t in range(1,n+1):
            net,out = threshold(n,t)
            for x in range(1 << n):
                assert net.evaluate(x,out) == (bin(x).count("1")>=t)
                assignments += 1
    for q in (2,3,4):
        gadget(q)
    print(f"{assignments} actual threshold circuit evaluations; sharp legal-code rows certified for q=2,3,4")
    print(f"{format_checks()} public binary strings checked for validity obstructions and format freezing")
    print(f"{sample_count()} simultaneous witness samples passed the independently enumerated sparsification example")
    print(f"{cyclic_sat_checks()} bounded-occurrence 2-CNF sign patterns checked for parity and exact model counts")
