"""One-query metric reduction from #CNF to unweighted counts on long even subdivisions."""
from dataclasses import dataclass
from fair_counting import attach_tails, fibonacci, unweighted_subdivision
from hamiltonian_seed import literal_graph, split_degree


@dataclass(frozen=True)
class Decoder:
    modulus: int
    unit_inverse: int

    def independent_count(self, oracle_answer):
        return (self.unit_inverse*oracle_answer) % self.modulus

    def accepted_count(self, oracle_answer, vertex_count):
        rejection_residue = pow(2,vertex_count,self.modulus)-oracle_answer
        return self.independent_count(rejection_residue)


def signed_cnf(variables, clauses):
    if variables < 1 or any(not clause for clause in clauses):
        raise ValueError("trivial empty formulas and false clauses can be answered directly")
    if any(not lit or abs(lit)>variables for clause in clauses for lit in clause):
        raise ValueError("invalid literal")
    seed,_=literal_graph(variables,[tuple(dict.fromkeys(c)) for c in clauses])
    degree=seed.degrees()
    if max(degree)<=3 and all(d<=2 for a,d in zip(seed.labels,degree) if a==-1):
        return seed,1
    equality_count=2*len(seed.edges)-len(seed.labels)
    return split_degree(seed,sign_at_end=True),(-1)**equality_count


def counting_query(variables, clauses, padding_power=0):
    if not isinstance(padding_power,int) or padding_power<0:
        raise ValueError("padding_power must be a nonnegative integer")
    base,split_sign=signed_cnf(variables,clauses)
    marked=base.labels.count(-1)
    # D ≡ −1 modulo 10. F_D > 2^variables bounds the wanted #SAT answer.
    d=9
    while fibonacci(d)<=1<<variables:
        d+=10
    modulus, unit=fibonacci(d),fibonacci(d-1)
    raw=attach_tails(base,d-3)
    e=len(raw.edges)
    length=d+1
    target=(2*e)**padding_power
    if length<target:
        length+=10*d*((target-length+10*d-1)//(10*d))
    assert length%10==0 and (length-1)%d==0
    graph=unweighted_subdivision(raw,length)
    exponent=marked+e*((length-1)//d)
    inv=split_sign*pow(unit,-exponent,modulus)
    return graph,Decoder(modulus,inv%modulus)


def parity_query(variables, clauses, padding_power=0):
    base,_=signed_cnf(variables,clauses)
    e=len(base.edges)
    target=(2*e)**padding_power
    # L ≡ 1 (mod 3) and L ≡ 0 (mod 10).
    length=10+30*max(0,(target-10+29)//30)
    return unweighted_subdivision(base,length)
