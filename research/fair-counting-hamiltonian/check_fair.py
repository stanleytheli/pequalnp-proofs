"""Exact integer controls for the two interpolation levels."""
from itertools import combinations
from fair_counting import count_cnf, signed_count
from hamiltonian_seed import WeightedGraph
from check_contraction import contract


def independent_sum(graph):
    total=0
    for mask in range(1<<len(graph.labels)):
        if any(mask>>u&1 and mask>>v&1 for u,v in graph.edges):
            continue
        term=1
        for i,a in enumerate(graph.labels):
            if mask>>i&1:
                term*=a
        total+=term
    return total


class FairOracle:
    def __init__(self):
        self.calls=0
        self.largest=0
    def __call__(self,graph):
        assert all(a==1 for a in graph.labels)
        n=len(graph.labels)
        self.calls+=1
        self.largest=max(self.largest,n)
        # The exact nonnegative answer is at most 2^n. The contraction uses
        # only + and *, so reducing modulo 2^(n+1) gives that same integer.
        return contract(graph,[],1<<(n+1))[0]


if __name__=='__main__':
    import argparse
    parser=argparse.ArgumentParser()
    parser.add_argument('--cnf',action='store_true')
    args=parser.parse_args()
    oracle=FairOracle()
    for labels,edges in [([-1,1,1],[(0,1),(1,2),(2,0)]),
                         ([-1,-1,1],[(0,1),(1,2),(2,0)]),
                         ([1,-1,1,-1],[(0,1),(1,2),(2,3),(3,0)])]:
        graph=WeightedGraph(labels,edges)
        assert signed_count(graph,oracle)==independent_sum(graph)
    print("Signed controls: exact integer counts matched;",oracle.calls,"fair queries; largest",oracle.largest,flush=True)
    if args.cnf:
        for clauses,expected in [([(1,)],1),([(1,),(-1,)],0),([],2)]:
            oracle=FairOracle()
            assert count_cnf(1,clauses,oracle)==expected
            print("CNF",clauses,"=",expected,"from",oracle.calls,"fair queries; largest",oracle.largest,flush=True)
