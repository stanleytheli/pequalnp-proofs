"""Validate both one-query reductions against brute Boolean truth tables."""
from itertools import product
from hamiltonian_seed import WeightedGraph
from check_contraction import contract
from fair_metric import counting_query, parity_query


def truths(n, clauses):
    return sum(all(any(assignment[abs(lit)-1] == (lit>0) for lit in c) for c in clauses)
               for assignment in product((False,True),repeat=n))


def sample_cases():
    # Some cases already have the required spare ports. The ternary clause,
    # repeated incidences and contradictory examples exercise degree-splitting.
    return [
        (1, []), (1, [(1,)]), (1, [(1,),(-1,)]),
        (2, [(1,2)]), (2, [(1,2),(1,-2),(-1,2)]),
        (3, [(1,2,3)]), (3, [(1,2,3),(1,-2,-3)]),
        (3, [(1,2,3),(-1,),(-2,),(-3,)]),
        (4, [(1,2),(-2,3),(-3,4),(-4,1)]),
        (6, [(1,2,3),(-2,4,5),(-5,6)]),
    ]


if __name__=='__main__':
    for n,clauses in sample_cases():
        want=truths(n,clauses)
        graph,decoder=counting_query(n,clauses)
        # The decoder needs the physical count only modulo F_D.
        residue,width=contract(graph,[],decoder.modulus)
        assert decoder.independent_count(residue)==want
        accepts=(pow(2,len(graph.labels),decoder.modulus)-residue)%decoder.modulus
        assert decoder.accepted_count(accepts,len(graph.labels))==want
        parity=parity_query(n,clauses)
        bit,_=contract(parity,[],2)
        assert bit==want%2
        print(n,len(clauses),len(graph.labels),decoder.modulus,want,bit,width,flush=True)
