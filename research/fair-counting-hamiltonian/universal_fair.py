"""One fixed optimum read-two formula per bound for exact and parity #CNF queries.

The instance selects only a set of physical input vertices to pin to zero.
The unsigned graph, its formula, the modulus and the normalization depend on m.
"""
from dataclasses import dataclass
from hamiltonian_seed import Formula, literal_graph, split_degree
from fair_counting import attach_tails, fibonacci, unweighted_subdivision
from fair_metric import Decoder


@dataclass
class Universal:
    m: int
    graph: object
    base: object
    length: int
    parameter: dict
    padding_bits: list
    representative: dict
    decoder: Decoder

    def zero_pins(self, n, clauses):
        if not 0<=n<=self.m or len(clauses)>self.m:
            raise ValueError("formula exceeds the universal family bound")
        if any(not l or abs(l)>n for c in clauses for l in c):
            raise ValueError("invalid literal index")
        # Additional tautological rows refer to witness bit 1. It may be
        # a pinned dummy; the row is still true under every assignment.
        rows = [set(c) for c in clauses]+[{1,-1} for _ in range(self.m-len(clauses))]
        pins = set()
        for (i, literal), parameter in self.parameter.items():
            required = literal in rows[i]
            opposite = -parameter if required else parameter
            pins.add(self.representative[opposite])
        for variable in self.padding_bits[n:]:
            pins.add(self.representative[variable])
        return pins


def build(m, padding_power=0):
    if not isinstance(m,int) or m<1 or not isinstance(padding_power,int) or padding_power<0:
        raise ValueError("m must be positive and the padding power nonnegative")
    f=Formula()
    witness=[f.variable() for _ in range(m)]
    parameters={}
    for i in range(m):
        outputs=[]
        for j,x in enumerate(witness,1):
            for signed,truth in ((j,x),(-j,-x)):
                a=f.variable()
                parameters[i,signed]=a
                outputs.append(f.conjunction(a,truth))
        f.clause(*outputs)
    seed,literals=literal_graph(f.variables,f.clauses)
    degree=seed.degrees()
    first=[]
    pos=0
    for d in degree:
        first.append(pos)
        pos+=3*d-2
    signed=split_degree(seed,sign_at_end=True)
    assert pos==len(signed.labels)
    reps={key:first[v] for key,v in literals.items()}
    assert all(signed.labels[v]==1 for v in reps.values())
    eta=(-1)**(2*len(seed.edges)-len(seed.labels))
    marked=signed.labels.count(-1)
    # Q is even as well as larger than the number of possible witnesses.
    d=9
    while fibonacci(d)<=1<<m:
        d+=30
    modulus,unit=fibonacci(d),fibonacci(d-1)
    base=attach_tails(signed,d-3)
    edges=len(base.edges)
    length=d+1
    target=(2*edges)**padding_power
    if length<target:
        length+=10*d*((target-length+10*d-1)//(10*d))
    assert length%2==0 and length%3==1 and (length-1)%d==0
    graph=unweighted_subdivision(base,length)
    factor=eta*pow(unit,-marked-edges*((length-1)//d),modulus)
    return Universal(m,graph,base,length,parameters,witness,reps,Decoder(modulus,factor%modulus))
