"""Independent exact controls for the tight-cut compiler and Laurent normalization."""
from collections import Counter
from fractions import Fraction
from itertools import permutations, product
from math import prod
from random import Random
from matching_lift import Board, Lift, all_matchings, solve
from weighted_compiler import Circuit, compile_weighted, integer_assignment_dual, normalize
from purify_circuit import purify


def all_categories(board, ms):
    full = (1<<len(ms))-1
    reps = {0:frozenset()}
    for e in board.edges:
        mask = sum(1<<i for i,m in enumerate(ms) if e in m)
        for other, previous in list(reps.items()):
            reps.setdefault(other|mask,previous|{e})
    return [(a,reps[a],reps[full^a]) for a in sorted(reps) if full^a in reps]


def feature_at(lift, form, m):
    score = form.constant
    for leaf in lift.leaves:
        local = m & leaf.board.edges.keys()
        if leaf.kind=="small":
            assert local in leaf.matches
            score += form.terms.get((leaf.index,frozenset(local)),0)
        else:
            score += sum(form.terms.get((leaf.index,e),0) for e in local)
    return score


def board_controls():
    rng = Random(17383)
    data = []
    for n in range(2,6):
        data.append(Board.square(n,[(i,j) for i in range(n) for j in range(n)])) if n<=4 else None
        for _ in range(22):
            board = [(i,i) for i in range(n)]
            for i in range(n):
                for j in range(n):
                    if rng.random()<0.31:
                        board.append((i,j))
            data.append(Board.square(n,board))
    # The diagonal and adjacent transpositions on a path yield arbitrarily
    # many nested cut states, while still allowing independent enumeration.
    for n in [6,7,8]:
        data.append(Board.square(n,[(i,j) for i in range(n) for j in range(n) if abs(i-j)<=1]))
    tallies = Counter()
    for board in data:
        lift = Lift(board)
        ms = all_matchings(lift.board)
        n = len(board.left)
        if len(ms)<=12:
            choices = all_categories(lift.board,ms)
        else:
            # Single marker-vertex incidence always gives a pure observable.
            choices = []
            for e,(i,j) in lift.board.edges.items():
                x = {e}
                y = {f for f,(a,b) in lift.board.edges.items() if a==i and f!=e}
                choices.append((sum(1<<k for k,m in enumerate(ms) if e in m),x,y))
            if n==3 and len(lift.board.edges)==9:
                x,y={0,5},{2,3}
                choices.append((sum(1<<k for k,m in enumerate(ms) if m&x),x,y))
        forms = []
        for mask,x,y in choices:
            f = lift.observable(x,y)
            assert all(feature_at(lift,f,m)==((mask>>i)&1) for i,m in enumerate(ms))
            forms.append(f)
        sampled = list(range(len(forms)))
        if len(sampled)>3:
            sampled = rng.sample(sampled,3)
        chosen = [forms[i] for i in sampled]
        dim = len(chosen)
        raw = Circuit(dim)
        coefficients = {e:1+rng.randrange(5) for e in lift.board.edges}
        weights = {e:raw.scalar(c) for e,c in coefficients.items()}
        output = compile_weighted(lift,chosen,raw,weights)
        clean,root = normalize(raw,output)
        for probes in [tuple(Fraction(2+i,3) for i in range(dim)), tuple(i%2 for i in range(dim))]:
            expect = sum(prod(coefficients[e] for e in m)*prod(probes[j]**int(bool(m&choices[k][1]))
                            for j,k in enumerate(sampled)) for m in ms)
            assert clean.evaluate(root,probes)==expect
            if all(probes): assert raw.evaluate(output,probes)==expect
        tallies.update(boards=1,forms=len(forms),incidences=len(ms)*len(forms),links=len(lift.links))
    print('Tight-cut compilation:',dict(sorted(tallies.items())))


def assignment_controls():
    rng = Random(21454)
    ncase = 0
    for n in range(1,7):
        for _ in range(35):
            cost = [[rng.randrange(-11,12) if rng.random()<0.72 else None for j in range(n)] for i in range(n)]
            allcost = [sum(cost[i][p[i]] for i in range(n)) for p in permutations(range(n))
                       if all(cost[i][p[i]] is not None for i in range(n))]
            got = integer_assignment_dual(cost)
            assert ((got is None) and not allcost) or (got is not None and got[0]==min(allcost))
            ncase += 1
    print(f'{ncase} signed and masked assignment duals agree with exhaustive permutation minima.')


def nested_controls():
    rng = Random(74321)
    cases = 0
    for _ in range(30):
        c = Circuit(4)
        vars = [c.monomial(tuple(int(i==j) for j in range(4))) for i in range(4)]
        def make(a,b):
            left = c.times([a]*rng.randrange(1,5)+[c.scalar(rng.randrange(1,6))])
            right = c.times([b]*rng.randrange(1,5)+[c.scalar(rng.randrange(1,6))])
            first = c.perm([[left,c.one,right],[right,c.one,left],[c.one,c.one,c.one]])
            # Nested call shares first with its surrounding addition.
            return c.plus([first,c.perm([[first,right],[c.one,c.one]]),left])
        g,h = make(*vars[:2]),make(*vars[2:])
        weighted = c.times([g,h])
        leaves = c.times([vars[0]]*3+[vars[3]]*4)
        root = c.plus([weighted,leaves,weighted])
        readouts = [({0},{1}),({1},{0}),({2},{3}),({3},{2})]
        device,result = purify(c,root,readouts)
        assert all(op!='monomial' or sum(data)==1 and min(data)>=0 for op,data in device.nodes)
        cube = [(b,c.evaluate(root,b)) for b in product((0,1),repeat=4)]
        for z in product((Fraction(0),Fraction(1,3),Fraction(4,3)), repeat=4):
            expected = sum(value*prod(x if bit else 1-x for x,bit in zip(z,b)) for b,value in cube)
            assert device.evaluate(result,z)==expected
            cases+=1
    print(f'{cases} exact evaluations of purified shared, nested circuits agree with Boolean interpolation.')
    c = Circuit(2); x,y=c.monomial((1,0)),c.monomial((0,1))
    for bad in (c.plus([c.one,x,y]),c.times([x,y])):
        try:
            purify(c,bad,[({0},{1})])
        except ValueError:
            pass
        else:
            raise AssertionError("An impure source passed its categorical precondition")
    print('Rejected the conflicting-label and uncovered-label controls.')


if __name__=='__main__':
    board_controls()
    assignment_controls()
    nested_controls()
