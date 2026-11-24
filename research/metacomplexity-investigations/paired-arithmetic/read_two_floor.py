"""Recognize closure of a baseline-normalized read-two CNF in polynomial time."""
from collections import Counter
from itertools import product


def solve(clauses, pins):
    fixed={}
    for literal in pins:
        variable=abs(literal)
        if variable in fixed and fixed[variable] != (literal>0):
            return False
        fixed[variable]=(literal>0)
    rows=[]
    for clause in clauses:
        if any(abs(l) in fixed and fixed[abs(l)] == (l>0) for l in clause):
            continue
        row={l for l in clause if abs(l) not in fixed}
        if not any(-l in row for l in row):
            rows.append(row)
    assert max(Counter(abs(l) for row in rows for l in row).values(), default=0)<=2
    while rows:
        if any(not row for row in rows):
            return False
        v=abs(next(iter(rows[0])))
        pos=[row for row in rows if v in row]
        neg=[row for row in rows if -v in row]
        rows=[row for row in rows if v not in row and -v not in row]
        if pos and neg:
            combined=(pos[0]-{v}) | (neg[0]-{-v})
            if not any(-l in combined for l in combined):
                rows.append(combined)
    return True


def closed(clauses, n, baseline):
    """Return True iff the satisfying vectors XOR baseline form a Boolean subalgebra."""
    if len(baseline)!=n or not all(any(baseline[abs(l)-1] == (l>0) for l in cl) for cl in clauses):
        raise ValueError("expected a satisfying baseline of the stated length")
    if max(Counter(abs(l) for c in clauses for l in c).values(), default=0)>2:
        raise ValueError("expected at most two literal occurrences per variable")
    def copy_y(l):
        return (abs(l)+n)*(1 if l>0 else -1)
    for target,cl in enumerate(clauses):
        # An accepted x whose complement fails C has every literal of C true.
        if solve(clauses,cl):
            return False
        both=[c for j,c in enumerate(clauses) if j!=target]
        both += [[copy_y(l) for l in c] for c in list(both)]
        presets=[]
        for lit in cl:
            j=abs(lit)
            wanted=(lit<0)
            # XOR normalization makes the raw meet AND at zero baseline bits,
            # OR at one baseline bits. Forcing the output of AND/OR either
            # pins both inputs or imposes a single two-copy linking clause.
            if (not baseline[j-1] and wanted) or (baseline[j-1] and not wanted):
                sign=1 if wanted else -1
                presets += [sign*j,sign*(j+n)]
            else:
                sign=1 if wanted else -1
                both.append([sign*j,sign*(j+n)])
        for lx,ly in product(cl,repeat=2):
            if solve(both,[*presets,lx,copy_y(ly)]):
                return False
    return True
