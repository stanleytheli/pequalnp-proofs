"""Gate-array reproduction of a linear threshold on independently supplied circuits."""
from dataclasses import dataclass
from itertools import product
from random import Random


@dataclass
class Circuit:
    arity: int
    gates: list
    output: int

    def append(self, op, *args):
        assert op in ("and", "or", "not") and len(args) <= 2
        new = self.arity + len(self.gates)
        assert all(0 <= a < new for a in args)
        self.gates.append((op, args))
        return new

    def run(self, inputs, mask):
        assert len(inputs) == self.arity
        wires = list(inputs)
        def read(i):
            return wires[i] if 0 <= i < len(wires) else 0
        for op, operands in self.gates:
            bits = [read(i) for i in operands]
            if op == "and":
                b = mask
                for x in bits: b &= x
            elif op == "or":
                b = 0
                for x in bits: b |= x
            else:
                assert op == "not"
                b = mask ^ (bits[0] if bits else 0)
            wires.append(b)
        return read(self.output)


def join(net, piece, zero):
    assert net.arity == piece.arity
    m = net.arity
    offset = len(net.gates)
    def relabel(i, bound):
        if 0 <= i < m:
            return i
        return offset + i if m <= i < bound else zero
    for j, (op, args) in enumerate(piece.gates):
        net.append(op, *(relabel(i, m + j) for i in args))
    return relabel(piece.output, m + len(piece.gates))


def half(net, a, b):
    ab = net.append("and", a, b)
    union = net.append("or", a, b)
    not_ab = net.append("not", ab)
    return net.append("and", union, not_ab), ab


def full(net, a, b, c):
    parity, pair = half(net, a, b)
    low, extra = half(net, parity, c)
    return low, net.append("or", pair, extra)


def weight_bits(net, votes):
    k = len(votes)
    assert k > 0
    current = list(votes)
    bits = []
    full_count = half_count = 0
    while current:
        assert len(current) == k >> len(bits)
        carries = []
        while len(current) >= 3:
            low, high = full(net, current.pop(), current.pop(), current.pop())
            current.append(low)
            carries.append(high)
            full_count += 1
        if len(current) == 2:
            low, high = half(net, *current)
            current = [low]
            carries.append(high)
            half_count += 1
        bits.append(current[0])
        current = carries
    assert full_count == k - k.bit_length()
    assert half_count == k.bit_length() - bin(k).count("1")
    return bits


def compare(net, bits, threshold):
    assert 1 <= threshold < 2**len(bits)
    first = (threshold & -threshold).bit_length()-1
    result = bits[first]
    for j in range(first+1, len(bits)):
        result = net.append("and" if threshold & (1<<j) else "or", bits[j], result)
    return result


def combine(parts, threshold):
    k = len(parts)
    assert 1 <= threshold <= k
    net = Circuit(parts[0].arity, [], 0)
    zero = net.append("or")
    votes = [join(net, piece, zero) for piece in parts]
    bits = weight_bits(net, votes)
    net.output = compare(net, bits, threshold)
    overhead = len(net.gates) - sum(len(piece.gates) for piece in parts)
    v = (threshold & -threshold).bit_length()-1
    exact = 9*k - 4*k.bit_length() - 4*bin(k).count("1") - v
    assert overhead == exact <= 9*k - 8
    return net


def packed_inputs(rows, m):
    return [sum(row[j]<<i for i,row in enumerate(rows)) for j in range(m)]


def run():
    trials = 0
    for k in range(1,16):
        rows = list(product((0,1), repeat=k))
        inputs = packed_inputs(rows,k)
        mask = (1<<len(rows))-1
        parts = [Circuit(k,[],j) for j in range(k)]
        for t in range(1,k+1):
            net = combine(parts,t)
            expect = sum((sum(row)>=t)<<p for p,row in enumerate(rows))
            assert net.run(inputs,mask) == expect
            trials += len(rows)
    print(f"All {trials} threshold/row pairs passed for 1..15 independent inputs.")
    rng = Random(10030)
    n = 11
    rows = list(product((0,1),repeat=n))
    inp = packed_inputs(rows,n)
    mask=(1<<len(rows))-1
    cases=0
    for k in [1,2,3,4,7,8,10,15,16,31,32,63,64,90,127,128,257,513]:
        parts=[]
        for p in range(k):
            gates=[]
            for j in range(rng.randrange(0,8)):
                op=rng.choice(["and","or","not"])
                args=tuple(rng.randrange(0,n+j+4) for _ in range(rng.randrange(0,3)))
                gates.append((op,args))
            parts.append(Circuit(n,gates,rng.randrange(0,n+len(gates)+4)))
        values=[piece.run(inp,mask) for piece in parts]
        sums=[sum((v>>i)&1 for v in values) for i in range(len(rows))]
        for t in sorted({1, (k+1)//2, k, 2*k//3+1}):
            expect=sum((x>=t)<<i for i,x in enumerate(sums))
            assert combine(parts,t).run(inp,mask)==expect
            cases+=len(rows)
    print(f"All {cases} gate-array/row pairs passed through k=513, including absent output/forward reads and fan-in zero or two.")
    for k in [800,1024,2047,4096,10001]:
        parts=[Circuit(k,[],j) for j in range(k)]
        for t in [1,k//2,k]:
            combine(parts,t)
    print("Five additional large column/gate-count certificates passed through k=10001.")


if __name__ == "__main__": run()
