"""Exact nonadaptive reduction from #CNF to fair edge-predicate counts.

The oracle receives an unweighted graph and returns its number of independent
sets. All its queries are ten-subdivisions of subcubic graphs; each has an
explicit optimal read-two edge formula.
"""
from fractions import Fraction
from hamiltonian_seed import WeightedGraph, literal_graph, split_degree


def fibonacci(n):
    a, b = 0, 1
    for _ in range(n):
        a, b = b, a + b
    return a


def interpolate_at(samples, at):
    """Lagrange evaluation over Q; no field-size assumption."""
    result = Fraction(0)
    for x, fx in samples:
        term = Fraction(fx)
        for u, _ in samples:
            if u != x:
                term *= (at-u) / (x-u)
        result += term
    return result


def attach_tails(base, length):
    result = WeightedGraph([1]*len(base.labels),base.edges.copy())
    for v, activity in enumerate(base.labels):
        if activity == -1:
            for _ in range(length):
                w = result.vertex(1)
                result.edge(v, w)
                v = w
        elif activity != 1:
            raise ValueError("the signed graph must have activities 1 and -1")
    return result


def unweighted_subdivision(base, length):
    result = WeightedGraph([1]*len(base.labels))
    for a, b in base.edges:
        v = a
        for _ in range(length-1):
            w = result.vertex(1)
            result.edge(v,w)
            v = w
        result.edge(v,b)
    return result


def lift_unsigned(base, oracle, padding_power):
    m = len(base.edges)
    # padding_power=0 retains girth at least 30. For q>=1 this also
    # enforces girth at least N**(q/(q+1)).
    first = max(1, ((2*m)**padding_power+9)//10)
    samples=[]
    for j in range(first,first+m+1):
        length = 10*j
        a, b = fibonacci(length), fibonacci(length-1)
        physical = unweighted_subdivision(base,length)
        count = oracle(physical)
        samples.append((Fraction(b,a),Fraction(count,a**m)))
    return interpolate_at(samples,Fraction(0))


def signed_count(base, oracle, padding_power=0):
    degree = base.degrees()
    if min(degree,default=0) == 0 or max(degree)>3:
        raise ValueError("subcubic graph without isolated vertices required")
    marked = [v for v,a in enumerate(base.labels) if a==-1]
    if any(degree[v]>2 for v in marked):
        raise ValueError("every marked vertex needs a spare degree")
    samples=[]
    for k in range(1,len(marked)+2):
        base_k=attach_tails(base,k)
        count=lift_unsigned(base_k,oracle,padding_power)
        a, b = fibonacci(k+2), fibonacci(k+1)
        samples.append((Fraction(b,a),count/a**len(marked)))
    result = interpolate_at(samples,Fraction(-1))
    if result.denominator != 1:
        raise ArithmeticError("a signed integer count is required")
    return result.numerator


def count_cnf(variables, clauses, oracle, padding_power=0):
    if any(not c for c in clauses):
        return 0
    if not variables:
        return 1
    if any(abs(lit)>variables or not lit for c in clauses for lit in c):
        raise ValueError("invalid CNF variable")
    clauses=[tuple(dict.fromkeys(c)) for c in clauses]
    seed,_=literal_graph(variables,clauses)
    degree=seed.degrees()
    if max(degree)<=3 and all(d<=2 for a,d in zip(seed.labels,degree) if a==-1):
        return signed_count(seed,oracle,padding_power)
    base=split_degree(seed,sign_at_end=True)
    equalities = 2*len(seed.edges)-len(seed.labels)
    return (-1)**equalities * signed_count(base,oracle,padding_power)
