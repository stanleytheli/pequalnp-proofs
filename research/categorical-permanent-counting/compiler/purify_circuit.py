"""Coefficient-preserving circuit compiler on promised binary categorical readouts.

For each output coordinate provide red and blue sets of original variables.
Every positive output parse must meet exactly one set (repeated hits allowed).
The produced ordinary circuit gives one copy of that coordinate for red,
zero copies for blue, and preserves every positive parse coefficient.
"""
from dataclasses import dataclass
from itertools import product
from matching_lift import Board, Form, Lift, solve
from weighted_compiler import Circuit, compile_weighted, normalize


@dataclass
class Gate:
    nonzero: bool
    choices: tuple = ()
    lift: Lift = None
    inputs: dict = None


def structure(source, root):
    gates = []
    for op,data in source.nodes[:root+1]:
        if op=="scalar":
            info = Gate(data>0)
        elif op=="monomial":
            if min(data,default=0)<0:
                raise ValueError("Categorical input leaves have ordinary exponents")
            info = Gate(True)
        elif op=="plus":
            choices = tuple((g,) for g in data if gates[g].nonzero)
            info = Gate(bool(choices),choices)
        elif op=="times":
            ok = all(gates[g].nonzero for g in data)
            info = Gate(ok,(data,) if ok else ())
        else:
            live = [(i,j) for i,row in enumerate(data) for j,g in enumerate(row) if gates[g].nonzero]
            board = Board.square(len(data),live)
            ok = solve(board)[0] is not None
            lift = Lift(board) if ok else None
            inputs = {e:data[i][j] for e,(i,j) in lift.board.edges.items()} if ok else {}
            info = Gate(ok,lift=lift,inputs=inputs)
        gates.append(info)
    needed = {root}
    for idx in reversed(range(root+1)):
        if idx not in needed or not gates[idx].nonzero:
            continue
        if gates[idx].lift is not None:
            needed.update(gates[idx].inputs.values())
        else:
            for q in gates[idx].choices:
                needed.update(q)
    return gates,needed


def or_sets(values):
    result = {0}
    for options in values:
        result = {a|b for a in result for b in options}
    return result


def oracle_colors(info, child_outcomes):
    """All unions of two possible hit flags, using at most two pinned slots."""
    results = set()
    for wanted in range(4):
        options = {e:{z for z in options if z|wanted==wanted}
                   for e,options in child_outcomes.items()}
        allowed = [e for e,opts in options.items() if opts]
        board = info.lift.board.keep(allowed)
        if wanted==0:
            if solve(board)[0] is not None:
                results.add(0)
            continue
        # Assign one witness slot for each bit set, allowing both to use one slot.
        bits = [b for b in (1,2) if b&wanted]
        carriers = [[e for e in allowed if any(x&b for x in options[e])] for b in bits]
        for pinned in product(*carriers):
            requirements = {}
            for bit,e in zip(bits,pinned):
                requirements[e] = requirements.get(e,0)|bit
            if any(not any(x&mask==mask for x in options[e]) for e,mask in requirements.items()):
                continue
            if solve(board,tuple(requirements))[0] is not None:
                results.add(wanted)
                break
    return results


def purify(source,root,readouts):
    gates,needed = structure(source,root)
    target = Circuit(len(readouts))
    if not gates[root].nonzero:
        return target,target.zero
    transformed, colors = {},{}
    for g,(op,data) in enumerate(source.nodes[:root+1]):
        if g not in needed or not gates[g].nonzero: continue
        info = gates[g]
        states = []
        for k,(red_vars,blue_vars) in enumerate(readouts):
            if op=="scalar":
                observed = {0}
            elif op=="monomial":
                support = {j for j,x in enumerate(data) if x}
                observed = {int(bool(support&red_vars))+2*int(bool(support&blue_vars))}
            elif op=="perm":
                observed = oracle_colors(info,{e:colors[h][k] for e,h in info.inputs.items()})
            else:
                observed = set().union(*(or_sets(colors[h][k] for h in choice) for choice in info.choices))
            if 3 in observed or {0,1,2}<=observed:
                raise ValueError("A live gate has a conflicting or omissible flexible readout")
            states.append(observed)
        colors[g] = states
        if op=="scalar":
            transformed[g] = target.scalar(data)
        elif op=="monomial":
            transformed[g] = target.one
        elif op=="perm":
            forms = []
            for k,state in enumerate(states):
                if state!={1,2}:
                    forms.append(Form())
                    continue
                x,y = set(),set()
                for e,h in info.inputs.items():
                    local = colors[h][k]
                    tag = 2 if local=={1,2} else min(local)
                    if tag==1: x.add(e)
                    if tag==2: y.add(e)
                forms.append(info.lift.observable(x,y))
            transformed[g] = compile_weighted(info.lift,forms,target,
                                              {e:transformed[h] for e,h in info.inputs.items()})
        else:
            terms = []
            for choice in info.choices:
                exp = []
                for k,state in enumerate(states):
                    mark = state=={1,2} and all(colors[h][k]!={1,2} for h in choice) and any(
                        min(colors[h][k])==1 for h in choice)
                    exp.append(int(mark))
                terms.append(target.times([target.monomial(exp)]+[transformed[h] for h in choice]))
            transformed[g] = target.plus(terms)
    if any(0 in state for state in colors[root]):
        raise ValueError("An output parse has no color for a requested readout")
    forced = target.monomial(tuple(int(state=={1}) for state in colors[root]))
    out = target.times((forced,transformed[root]))
    return normalize(target,out)
