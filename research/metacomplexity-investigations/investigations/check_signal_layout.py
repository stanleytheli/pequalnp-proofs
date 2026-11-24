"""Independent truth-table tests of shared-signal interpolation and layout ranks."""
from itertools import product
import random


def rank_gf2(rows):
    pivots = {}
    for row in rows:
        while row:
            col = row.bit_length()-1
            if col not in pivots:
                pivots[col] = row
                break
            row ^= pivots[col]
    return len(pivots)


def circuit_data(n, gates):
    last = n+len(gates)-1
    live = {last}
    uses = [0]*(last+1)
    for v in range(last,n-1,-1):
        if v in live:
            _,a,b = gates[v-n]
            uses[a] += 1
            uses[b] += 1
            live.update((a,b))
    shared = sorted(v for v in live if uses[v] >= 2)
    return live, shared, last


def truth(n,gates):
    vals = []
    for assignment in range(1 << n):
        trace = [(assignment >> i)&1 for i in range(n)]
        for h,a,b in gates:
            trace.append((h >> (2*trace[a]+trace[b]))&1)
        vals.append(trace[-1])
    return vals


def conditioned(n,gates,x,prime):
    live,shared,last = circuit_data(n,gates)
    total = 0
    for bits in product((0,1),repeat=len(shared)):
        guesses = dict(zip(shared,bits))
        prob = dict(enumerate(x))
        for v in range(n,last+1):
            if v not in live:
                continue
            h,a,b = gates[v-n]
            u,w = guesses.get(a,prob[a]),guesses.get(b,prob[b])
            child_weights = ((1-u)*(1-w),(1-u)*w,u*(1-w),u*w)
            prob[v] = sum(weight for idx,weight in enumerate(child_weights) if (h >> idx)&1)%prime
        score = prob[last]
        for j,bit in guesses.items():
            score = (score*(prob[j] if bit else 1-prob[j]))%prime
        total += score
    return total%prime


def layout(n,gates):
    live,shared,last = circuit_data(n,gates)
    shared_set = set(shared)
    data = {i:1 << i for i in range(n)}
    cuts = set(data[i] for i in range(n) if i in live)
    for v in range(n,last+1):
        if v not in live:
            continue
        _,a,b = gates[v-n]
        left = 0 if a in shared_set else data[a]
        right = 0 if b in shared_set else data[b]
        assert (left & right) == 0
        data[v] = left | right
        if data[v]:
            cuts.add(data[v])
    joined = 0
    for root in shared+[last]:
        assert (joined & data[root]) == 0
        joined |= data[root]
        cuts.add(joined)
    assert joined == sum(1 << i for i in range(n) if i in live)
    return cuts,shared


def test_circuits():
    rng = random.Random(117)
    counts = [0,0,0]
    for n in range(2,8):
        for _ in range(50):
            gates = []
            wires = list(range(n))
            rng.shuffle(wires)
            # A read-once core, followed by optional signals with arbitrary sharing.
            while len(wires)>1:
                a,b = wires.pop(),wires.pop()
                gates.append((rng.randrange(16),a,b))
                wires.insert(rng.randrange(len(wires)+1),n+len(gates)-1)
            for j in range(rng.randrange(5)):
                top = n+len(gates)-1
                gates.append((rng.randrange(16),top,rng.randrange(top+1)))
            table = truth(n,gates)
            cuts,shared = layout(n,gates)
            for cut in cuts:
                left = [v for v in range(1 << n) if not (v & ~cut)]
                right = [v for v in range(1 << n) if not (v & cut)]
                rows = [sum(table[a|b] << i for i,b in enumerate(right)) for a in left]
                assert rank_gf2(rows) <= 2**(len(shared)+1)
                counts[1] += 1
            for p in (2,3,11,101):
                x = [rng.randrange(p) for _ in range(n)]
                expected = 0
                for a,y in enumerate(table):
                    weight = y
                    for i,v in enumerate(x):
                        weight = weight*(v if (a >> i)&1 else 1-v)%p
                    expected += weight
                assert conditioned(n,gates,x,p) == expected%p
                counts[2] += 1
            counts[0] += 1
    return counts


if __name__ == "__main__":
    circuits,cuts,values = test_circuits()
    print(f"{circuits} arbitrary-basis circuits: {cuts} cut ranks and {values} multilinear evaluations over four prime fields checked")
