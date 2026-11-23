"""Directly contract the same unsigned graph with different free input subcubes."""
from universal_fair import build
from hamiltonian_seed import WeightedGraph
from check_contraction import contract
from check_metric import truths


def check(unit,n,clauses):
    pins=unit.zero_pins(n,clauses)
    weights=[int(i not in pins) for i in range(len(unit.graph.labels))]
    physical=WeightedGraph(weights,unit.graph.edges)
    q=unit.decoder.modulus
    residue,width=contract(physical,[],q)
    want=truths(n,clauses)
    assert unit.decoder.independent_count(residue)==want
    free=len(weights)-len(pins)
    accepted=(pow(2,free,q)-residue)%q
    assert unit.decoder.accepted_count(accepted,free)==want
    assert accepted%2==want%2
    return width


if __name__=='__main__':
    for m,cases in [
        (1,[(0,[]),(0,[()]),(1,[]),(1,[(1,)]),(1,[(-1,)]),(1,[(1,-1)])]),
        (2,[(0,[]),(1,[(1,),(-1,)]),(2,[]),(2,[(1,-2)]),(2,[(1,2),(-1,-2)]),(2,[()])]),
        (3,[(2,[(1,-2)]),(3,[(1,2,3),(-1,2),(-3,)])])]:
        template=build(m)
        widths=[check(template,n,clauses) for n,clauses in cases]
        print(f"m={m}, fixed N={len(template.graph.labels)}, edges={len(template.graph.edges)}, Q={template.decoder.modulus}, checked subcubes={len(cases)}, max width={max(widths)}",flush=True)
