from collections import Counter
from itertools import product
from layered import paired_layers


def accepted(clauses, data):
    return all(any(data[abs(l)] == (l>0) for l in cl) for cl in clauses)


def shape(out):
    for layer in out.layers:
        positions = [abs(v) for cl in layer for v in cl]
        assert sorted(positions) == list(range(1, out.variable_count+1))
        assert all(len(set(map(abs,cl))) == len(cl) and 2 <= len(cl) <= 3 for cl in layer)
    assert all(len(cl) == 2 for layer in out.layers[:2] for cl in layer)
    assert all(out.owner[i] == -out.owner[i+1] for i in range(1, out.variable_count, 2))
    signs = Counter(v for layer in out.layers for cl in layer for v in cl)
    assert all(sorted([signs[j],signs[-j]]) == [1,2] for j in range(1,out.variable_count+1))


def extend_unique(out, assignment):
    physical = out.extend(assignment)
    assert sum(physical) == out.variable_count//2
    assert all(physical[i] != physical[i+1] for i in range(1,len(physical),2))
    return physical


def check_small():
    cases = [([(1,)],1), ([(1,-2)],2), ([(1,1)],1), ([(1,)],2), ([(1,),(-1,)],1)]
    for clauses, n in cases:
        out = paired_layers(clauses, n)
        shape(out)
        legitimate = set()
        for a in product((False,True), repeat=n):
            assignment = [False,*a]
            phys = extend_unique(out, assignment)
            assert accepted(clauses,assignment) == out.accepts(phys)
            if accepted(clauses,assignment):
                legitimate.add(tuple(phys[1:]))
        # Complete enumeration includes invalid and inconsistent auxiliaries.
        actual = set(p for p in product((False,True),repeat=out.variable_count) if out.accepts([False,*p]))
        assert actual == legitimate
        print(f"exact physical truth table N={out.variable_count} rows={2**out.variable_count} models={len(actual)}")


def check_planted():
    from succinct_gap import planted
    from check_gap import all_bits, sat, tours
    for formula, n, m in [([(1,),(-1,)],1,2), ([(1,-2)],2,2), ([],0,3)]:
        net, _, rails, edges, z = planted(formula,n,m)
        layered = paired_layers(net.clauses(z),net.primary_count+len(net.gates))
        shape(layered)
        counts = {a:Counter() for a in all_bits(n) if sat(formula,a)}
        bases = 0
        for assignment in all_bits(net.primary_count):
            wires = net.evaluate(assignment)
            physical = extend_unique(layered,wires)
            assert layered.accepts(physical) == wires[z]
            if not wires[z]: continue
            if physical[layered.first[1]]:
                bases += 1
                continue
            for witness, target in counts.items():
                if any(physical[layered.first[r[not val]]] for r,val in zip(rails,witness)):
                    continue
                exponent = tuple(i for i,v in enumerate(sum(edges,[])) if physical[layered.first[v]])
                target[exponent] += 1
        expected = Counter({e:1 for e in tours(m)})
        assert bases == 1 and all(c == expected for c in counts.values())
        print(f"planted order={m} sat_count={len(counts)} N={layered.variable_count} "
              f"degree={layered.variable_count//2} exact occurrence=3, decomposition and HC coefficients checked")


if __name__ == "__main__":
    check_small()
    check_planted()
