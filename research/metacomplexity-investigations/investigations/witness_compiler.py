"""Boolean NAND programs and parsimonious positive exact-one encodings."""
from itertools import product


class Nand:
    def __init__(self, inputs):
        if inputs < 1:
            raise ValueError("at least one witness bit is required")
        self.inputs = inputs
        self.gates = []
        self.cached = {}
        self.one = self.nand(0, self.neg(0))
        self.zero = self.neg(self.one)

    def nand(self, a, b):
        key = tuple(sorted((a,b)))
        if key not in self.cached:
            self.cached[key] = self.inputs+len(self.gates)
            self.gates.append(key)
        return self.cached[key]

    def neg(self, a):
        return self.nand(a,a)

    def both(self, a, b):
        return self.neg(self.nand(a,b))

    def either(self, a, b):
        return self.nand(self.neg(a),self.neg(b))

    def xor(self, a, b):
        ab = self.nand(a,b)
        return self.nand(self.nand(a,ab),self.nand(b,ab))

    def select(self, flag, yes, no):
        return self.nand(self.nand(flag,yes), self.nand(self.neg(flag),no))

    def all(self, signals):
        v = self.one
        for b in signals:
            v = self.both(v,b)
        return v

    def any(self, signals):
        v = self.zero
        for b in signals:
            v = self.either(v,b)
        return v

    def equals(self, bits, value):
        return self.all(b if (value >> i) & 1 else self.neg(b) for i,b in enumerate(bits))

    def run(self, values):
        if len(values) != self.inputs:
            raise ValueError("wrong witness length")
        trace = list(values)
        for i,j in self.gates:
            trace.append(1-(trace[i] & trace[j]))
        return trace


def balanced_verifier(m, t, witness_width, predicate_a, predicate_b, comparator=False):
    """Return a verifier, output wire and positive-wire data labels.

    The two verifiers passed in must use the same witness width. Inputs
    encode rows least-significant bit first, followed by the selector,
    one branch bit and the common witness. The branch bit doubles only
    the count on selected maps.
    """
    width = (m-1).bit_length()
    k = m*width
    payload = tuple(range(k+t+1,k+t+1+witness_width))
    net = Nand(k+t+1+witness_width)
    choose = [[net.equals(range(i*width,(i+1)*width),j) for j in range(m)] for i in range(m)]
    valid = net.all(net.any(row) for row in choose)
    if comparator:
        selected = net.all(net.any(row[:max(1,i)]) for i,row in enumerate(choose))
    else:
        one_per_column = net.all(net.any(row[j] for row in choose) for j in range(m))
        at = [net.one]+[net.zero]*(m-1)
        visited = list(at)
        for _ in range(m):
            at = [net.any(net.both(at[i],choose[i][j]) for i in range(m)) for j in range(m)]
            visited = [net.either(a,b) for a,b in zip(visited,at)]
        selected = net.all([one_per_column,at[0],*visited])
    parity = net.zero
    for w in range(k,k+t):
        parity = net.xor(parity,w)
    use_b = net.select(selected,parity,k+t)
    accepted = net.both(valid,net.select(use_b,predicate_b(net,payload),predicate_a(net,payload)))
    # Different emitted flags can have the same deterministic wire, e.g.
    # complementary row choices on m=2. Keep occurrences individually.
    labels = [(choose[i][j],f"x{i}.{j}") for i,j in product(range(m),repeat=2)]
    labels += [(k+h,f"y{h}.1") for h in range(t)]
    labels += [(net.neg(k+h),f"y{h}.0") for h in range(t)]
    return net, accepted, labels


class ExactOne:
    def __init__(self, net, accepted, labels):
        self.net = net
        self.accepted = accepted
        self.labels = {}
        self.bits = 5
        self.clauses = [(0,1,2),(0,1,3),(2,3,4),(4,0,2)]

        def fresh(count):
            start = self.bits
            self.bits += count
            return tuple(range(start,start+count))

        self.wires = [fresh(2) for _ in range(net.inputs+len(net.gates))]
        self.clauses += [(a,b,2) for a,b in self.wires]
        self.selectors = []
        for i,(a,b) in enumerate(net.gates):
            a0,a1 = self.wires[a]
            b0,b1 = self.wires[b]
            z0,z1 = self.wires[net.inputs+i]
            t00,t01,t10,t11 = fresh(4)
            self.selectors.append((t00,t01,t10,t11))
            self.clauses.extend(((a0,t10,t11),(a1,t00,t01),(b0,t01,t11),(b1,t00,t10),(z1,t11,2)))
        self.clauses.append((4,self.wires[accepted][0],2))
        self.emit = []
        for wire,label in labels:
            # One fresh true flag per output label, including coincidences.
            flag, = fresh(1)
            self.clauses.append((self.wires[wire][0],flag,2))
            self.emit.append((wire,flag))
            self.labels[flag,1] = (label,)

    def extend(self, trace):
        flags = [0]*self.bits
        flags[1] = flags[4] = 1
        for pair,b in zip(self.wires,trace):
            flags[pair[b]] = 1
        for group,(i,j) in zip(self.selectors,self.net.gates):
            flags[group[2*trace[i]+trace[j]]] = 1
        for wire,flag in self.emit:
            flags[flag] = trace[wire]
        return flags
