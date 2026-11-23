"""Independently replay explicit L648 witnesses against their 256 Boolean assignments."""
import json
from collections import Counter
from pathlib import Path

ROOT = Path(__file__).resolve().parent
EDGES = {(0,1), (1,2), (2,3), (3,4), (0,4), (3,5), (4,6), (0,7)}
ASSIGNMENTS = tuple(tuple(bool(mask & 2**v) for v in range(8)) for mask in range(256))
GOAL = tuple(any(x[i] and x[j] for i,j in EDGES) for x in ASSIGNMENTS)
PAIRS = tuple(mask for mask in range(256) if bin(mask).count("1") == 2)
columns = tuple(tuple(row[i] for row in ASSIGNMENTS) for i in range(8))

def truth(gates):
    cache = list(columns)
    for op, a, b in gates:
        assert op in (0,1) and 0 <= a < len(cache) and 0 <= b < len(cache)
        cache.append(tuple(min(x,y) if op else max(x,y) for x,y in zip(cache[a],cache[b])))
    return cache

def simple(gates):
    for root, (op, a, b) in enumerate(gates):
        if op != 1:
            continue
        stack = [a,b]
        while stack:
            wire = stack.pop()
            if wire >= 8:
                k, left, right = gates[wire - 8]
                if k == 1:
                    return False
                stack.extend((left,right))
    return True

def replay(gates, tokens):
    kind, j, first, second = tokens
    assert 0 <= j < len(gates)
    o,a,b = gates[j]
    if kind == "junk":
        assert o == 1 and first in (0,1)
        child = [a,b][first]
        assert child >= 8
        op,q,r = gates[child-8]
        assert op == 0 and second in (q,r)
        dest = [a,b]
        dest[first] = second
        return gates[:j]+[(1,*dest)]+gates[j+1:]
    assert kind == "lift" and o == 0 and sorted([first,second]) == sorted([a,b])
    p,h = first,second
    dead = 8+j
    assert 8 <= h < dead and j < len(gates)-1
    # Wire labels in the shortened prefix are assigned consecutively; substitute the
    # kept input for the erased OR node, and recompute every remaining reference.
    alias = dict(enumerate(range(8)))
    next_gates = []
    for k,(op,left,right) in enumerate(gates):
        if k == j:
            alias[k+8] = alias[p]
        else:
            alias[k+8] = 8+len(next_gates)
            next_gates.append((op,alias[left],alias[right]))
    values = truth(gates)
    assert all(not u or v for u,v in zip(values[h], values[-1]))
    next_gates.append((0,alias[7+len(gates)],alias[h]))
    return next_gates

def main():
    certs = json.loads((ROOT/"certificates.json").read_text())
    raw = (ROOT/"pair-candidates.txt").read_text().splitlines()
    assert len(certs) == len(raw) == 3658
    counts = Counter()
    lengths = Counter()
    move_counts = Counter()
    for row,(tag,moves) in zip(raw,certs):
        data = tuple(map(int,row.split()))
        assert len(data) == 33
        gates = [data[k:k+3] for k in range(0,len(data),3)]
        result = truth(gates)[-1]
        assert all(result[m] == GOAL[m] for m in PAIRS)
        if result != GOAL:
            assert (tag,moves) == ("wrong",[])
        elif simple(gates):
            assert (tag,moves) == ("flat",[])
        else:
            assert tag == "flattened" and moves
            for move in moves:
                gates = replay(gates,move)
                assert truth(gates)[-1] == GOAL
                move_counts[move[0]] += 1
            assert simple(gates)
            lengths[len(moves)] += 1
        counts[tag] += 1
    print("Independent 256-assignment replay:",len(certs),dict(counts),dict(lengths),dict(move_counts))
if __name__ == "__main__":
    main()
