"""Reduce width-at-most-three SAT to the OR of two read-once trees.

Run python3 pair_trees.py input.cnf output.json to export a DIMACS instance.
A tree is an integer variable index or [operation,left,right].
"""
import argparse
from collections import Counter
import json
from pathlib import Path


def join(op,trees):
    trees = list(trees)
    if not trees:
        raise ValueError("cannot combine an empty list")
    while len(trees)>1:
        trees = [[op,trees[i],trees[i+1]] if i+1<len(trees) else trees[i]
                 for i in range(0,len(trees),2)]
    return trees[0]


def compile_cnf(source, pad_copies=None):
    if any(len(c)>3 or 0 in c for c in source):
        raise ValueError("expected clauses of width at most three with nonzero signed integers")
    if any(not c for c in source):
        source = [(1,),(-1,)]
    if not source:
        source = [(1,-1)]
    triples = [tuple(c)+tuple(c[-1] for _ in range(3-len(c))) for c in source]
    uses = Counter(literal for c in triples for literal in c)
    for v in sorted({abs(literal) for literal in uses}):
        difference = uses[v]-uses[-v]
        sign = -v if difference>0 else v
        triples.extend([(sign,sign,-sign)]*abs(difference))
    K = 3*len(triples)
    if pad_copies is not None:
        if pad_copies<K or (pad_copies-K)%6:
            raise ValueError("padding length must be a sufficiently large multiple of six")
        v = max(abs(l) for c in triples for l in c)+1
        for _ in range((pad_copies-K)//6):
            triples.extend(((v,v,-v),(-v,-v,v)))
            v += 1
        K = pad_copies
    clones = {}
    copy_orig = []
    payload = []
    for clause in triples:
        row = []
        for l in clause:
            j = len(copy_orig)+1
            copy_orig.append(abs(l))
            clones.setdefault(abs(l),[]).append((j,l>0))
            row.append(j if l>0 else -j)
        payload.append(row)
    links = []
    for items in clones.values():
        ids = [j for j,_ in items]
        links += [(-j,next_j) for j,next_j in zip(ids,ids[1:]+ids[:1])]
        pos = [j for j,p in items if p]
        neg = [j for j,p in items if not p]
        assert len(pos)==len(neg)
        links += [(-p,n) for p,n in zip(pos,neg)]
    source_ports = []
    used = Counter()
    for row in payload+links:
        clause = []
        for literal in row:
            assert used[literal] < 2
            clause.append(4*(abs(literal)-1)+2*int(literal<0)+used[literal])
            used[literal] += 1
        source_ports.append(clause)
    assert len(used)==2*K and set(used.values())=={2}
    t = 2
    while 8*t*t < 4*K:
        t += 2
    def port(a,b,j):
        return 4*K+8*((a%t)*t+b%t)+j
    external,internal = [],[]
    for a in range(t):
        for b in range(t):
            for j,(c,d) in enumerate(((a+2*b,b),(a+2*b+1,b),(a,b+2*a),(a,b+2*a+1))):
                external.append(["and",port(a,b,j),port(c,d,j+4)])
            internal.append(["and",port(a,b,0),join("or",[port(a,b,j) for j in range(1,8)])])
    conflict = [["and",["or",4*i,4*i+1],["or",4*i+2,4*i+3]] for i in range(K)]
    A = ["or",join("or",conflict),join("or",external)]
    B = ["and",join("and",[join("or",clause) for clause in source_ports]),join("or",internal)]
    return {"input_count":4*K+8*t*t,"selector_copies":K,"first":A,"second":B}, copy_orig


def read_dimacs(path):
    clauses = []
    current = []
    header = None
    for line in Path(path).read_text().splitlines():
        words = line.split()
        if not words or words[0]=="c":
            continue
        if words[0]=="p":
            if words[:2]!=["p","cnf"] or len(words)!=4 or header is not None:
                raise ValueError("invalid or repeated DIMACS header")
            header = tuple(map(int,words[2:]))
            continue
        for literal in map(int,words):
            if literal:
                current.append(literal)
            else:
                clauses.append(tuple(current))
                current = []
    if current or header is None or header[1]!=len(clauses):
        raise ValueError("unterminated clause or inconsistent DIMACS header")
    if any(abs(l)>header[0] for c in clauses for l in c):
        raise ValueError("literal exceeds declared variable count")
    return clauses


if __name__ == "__main__":
    parser = argparse.ArgumentParser()
    parser.add_argument("cnf")
    parser.add_argument("output")
    args = parser.parse_args()
    data,_ = compile_cnf(read_dimacs(args.cnf))
    Path(args.output).write_text(json.dumps(data,indent=1)+"\n")
