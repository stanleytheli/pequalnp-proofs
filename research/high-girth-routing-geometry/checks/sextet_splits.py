"""Extract a sequence of input/output vertex splits from a concrete routing.

Every reverse elimination in this routine has a unit unique predecessor or a
unit unique successor. Its inverse is exactly the proved semiring vertex split.
A forward replay rebuilds the entire active graph starting from the dense pair
indices; checking only physical edge membership would already suffice.
"""
from sextet_eliminate import ONE,projection

def witness(p,m,generator=None):
    graph,matched,centers,matrix=projection(p,m,generator) if generator else projection(p,m)
    initial={(a,b):lab for a,row in matrix.items() for b,lab in row.items()}
    todo=set(matrix)-set(centers)
    undo=[]
    while todo:
        transposed={v:[] for v in matrix}
        for a,row in matrix.items():
            for b in row:
                if a!=b:
                    transposed[b].append(a)
        for v in sorted(todo):
            source=transposed[v]
            target=[w for w in matrix[v] if w!=v]
            if len(source)==1 and matrix[source[0]][v]==ONE and all(
                    w not in matrix[source[0]] for w in target):
                outgoing=True
                parent=source[0]
                moved=sorted(target)
                break
            if len(target)==1 and matrix[v][target[0]]==ONE and all(
                    target[0] not in matrix[u] for u in source):
                outgoing=False
                parent=target[0]
                moved=sorted(source)
                break
        else:
            raise AssertionError("No reversible split")
        assert matrix[v][v]==ONE
        if outgoing:
            for w in moved:
                matrix[parent][w]=matrix[v][w]
        else:
            for u in moved:
                matrix[u][parent]=matrix[u][v]
        for u in source:
            del matrix[u][v]
        del matrix[v]
        todo.remove(v)
        undo.append((outgoing,parent,v,moved))
    for i,a in enumerate(centers):
        assert set(matrix[a])==set(centers)
        for j,b in enumerate(centers):
            assert matrix[a][b]=={((i,j),):1}
    steps=list(reversed(undo))
    now={(a,b):{((i,j),):1} for i,a in enumerate(centers) for j,b in enumerate(centers)}
    for outgoing,v,z,chosen in steps:
        assert z!=v and (z,z) not in now
        updated={}
        for (a,b),lab in now.items():
            if outgoing and a==v and b in chosen:
                a=z
            elif not outgoing and b==v and a in chosen:
                b=z
            assert (a,b) not in updated
            updated[a,b]=lab
        updated[z,z]=ONE
        updated[(v,z) if outgoing else (z,v)]=ONE
        now=updated
    assert now==initial
    assert all(matched[b] in graph[a] for a,b in now)
    print(f'p={p} dimension={m} verified_reversible_splits={len(steps)} '
          f'rebuilt_entries={len(now)} checked_matched_pairs={len(matched)}')
    return graph,matched,centers,steps
if __name__=="__main__":
    witness(41,5)
    witness(73,7)
