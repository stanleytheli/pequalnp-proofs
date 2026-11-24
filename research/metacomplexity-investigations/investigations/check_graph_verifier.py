"""Check the general witness compiler and actual labelled directed tours."""
from collections import Counter
from itertools import product
from pathlib import Path
import sys

here = Path(__file__).resolve().parent
if not (here/"marked_hamiltonian.py").exists():
    sys.path.insert(0,str(here.parent/"positive-hamiltonian"))
from marked_hamiltonian import Digraph, compile_positive_exact_one
from witness_compiler import ExactOne, balanced_verifier


class TraceGraph:
    """Retain the physical arc history, so a witness gives a verifiable tour."""
    def __init__(self, encoding):
        n = encoding.bits
        clauses = encoding.clauses
        groups = n+len(clauses)
        self.graph = g = Digraph(groups)
        self.options = [[g.arc(i,(i+1)%groups,encoding.labels.get((i,b),())) for b in (0,1)]
                        for i in range(n)]
        self.occurrences = [[g.arc(n+j,(n+j+1)%groups) for _ in clause] for j,clause in enumerate(clauses)]
        false_marks = [row[0] for row in self.options]
        self.events = []
        for j,clause in enumerate(clauses):
            for col,idx in enumerate(clause):
                a,b = false_marks[idx], self.occurrences[j][col]
                start = g.next_id
                false_marks[idx],_ = g.xor(a,b)
                self.events.append((a,b,start))

    def certified_tour(self, flags, clauses):
        g = self.graph
        selected = {row[b] for row,b in zip(self.options,flags)}
        for row,clause in zip(self.occurrences,clauses):
            picks = [edge for edge,bit in zip(row,clause) if flags[bit]]
            assert len(picks) == 1
            selected.add(picks[0])
        for a,b,start in self.events:
            assert (a in selected) != (b in selected)
            if a in selected:
                selected.remove(a)
                selected.update(start+j for j in (6,0,2,4))
            else:
                selected.remove(b)
                selected.update(start+j for j in (7,3,1,5))
        assert len(selected) == g.vertices
        nxt = {}
        for edge in selected:
            u,v,_ = g.arcs[edge]
            assert u not in nxt
            nxt[u] = v
        v = 0
        seen = set()
        while v not in seen:
            seen.add(v)
            v = nxt[v]
        assert v == 0 and len(seen) == g.vertices
        return g.monomial(selected)


def count_a(net,wires):
    return net.nand(*wires)


def count_b(net,wires):
    return net.equals(wires,3)


def check(m,t,comparator,physical):
    net,accepted,labels = balanced_verifier(m,t,2,count_a,count_b,comparator)
    encoding = ExactOne(net,accepted,labels)
    width = (m-1).bit_length()
    k = m*width
    counts = Counter()
    physical_tours = 0
    tg = TraceGraph(encoding) if physical else None
    if tg is not None:
        ref = compile_positive_exact_one(encoding.bits,encoding.clauses,encoding.labels)
        assert ref.arcs == tg.graph.arcs
        assert len({(u,v) for u,v,_ in ref.arcs.values()}) == len(ref.arcs)
        indeg = Counter(v for u,v,_ in ref.arcs.values())
        outdeg = Counter(u for u,v,_ in ref.arcs.values())
        assert max(indeg.values()) <= 3 and max(outdeg.values()) <= 3
    for i_witness,witness in enumerate(product((0,1),repeat=net.inputs)):
        trace = net.run(witness)
        if physical or i_witness%53 == 0:
            flags = encoding.extend(trace)
            assert all(sum(flags[i] for i in c) == 1 for c in encoding.clauses) == bool(trace[accepted])
        if not trace[accepted]:
            continue
        row = tuple(sum(witness[i*width+j] << j for j in range(width)) for i in range(m))
        assert all(j < m for j in row)
        w = witness[k:k+t]
        mon = tuple(sorted([f"x{i}.{j}" for i,j in enumerate(row)]+[f"y{h}.{b}" for h,b in enumerate(w)]))
        assert tuple(sorted(label for wire,label in labels if trace[wire])) == mon
        counts[row,w] += 1
        if tg is not None:
            assert tg.certified_tour(flags,encoding.clauses) == mon
            physical_tours += 1
    assert len(counts) == (m**m)*(2**t)
    for (row,w),value in counts.items():
        if comparator:
            inside = all(j < max(1,i) for i,j in enumerate(row))
        else:
            v = 0
            order = []
            while v not in order:
                order.append(v)
                v = row[v]
            inside = v == 0 and len(order) == m
        assert value == (2*(1 if sum(w)%2 else 3) if inside else 4)
    print(f"m={m} selectors={t} comparator={int(comparator)}: {2**net.inputs} raw witnesses, "
          f"{len(counts)} coefficient counts, {physical_tours} spanning tours checked")
    if physical:
        print(f"physical graph: {tg.graph.vertices} vertices, {len(tg.graph.arcs)} simple arcs, max indegree/outdegree 3")


if __name__ == "__main__":
    for comparator in (False,True):
        check(2,1,comparator,True)
        check(3,2,comparator,False)
