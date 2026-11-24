"""Construct and validate a dense-permanent routing in a concrete sextet graph.

The record stores a fixed physical matching, disjoint branch trees, private
links for ordered demands, and the actual sparse physical edge labels. All
generation and verification use only the Python standard library.
"""
from collections import deque
from itertools import permutations
from random import Random
from sextet import sextet

def contract(graph):
    color = {0:0}
    queue = deque([0])
    while queue:
        x = queue.popleft()
        for y in graph[x]:
            if y not in color:
                color[y]=1-color[x]
                queue.append(y)
            assert color[y]!=color[x]
    left = sorted(x for x in color if color[x]==0)
    # Repeated alternating-path augmentation. Only one path, with no recursive
    # stack, is updated after each search.
    chosen={}
    partner={}
    for start in left:
        prev={start:None}
        queue=deque([start])
        last=None
        while queue and last is None:
            x=queue.popleft()
            for y in graph[x]:
                if y not in partner:
                    last=(x,y)
                    break
                t=partner[y]
                if t not in prev:
                    prev[t]=(x,y)
                    queue.append(t)
        assert last is not None
        while last:
            x,y=last
            chosen[x],partner[y]=y,x
            last=prev[x]
    assert len(set(chosen.values()))==len(left)==len(graph)//2
    forward={v:[partner[w] for w in graph[v] if w!=chosen[v]] for v in left}
    backward={v:[] for v in left}
    for x,ns in forward.items():
        for y in ns:
            backward[y].append(x)
    assert all(len(ns)==2 for ns in backward.values())
    return forward,backward,chosen

def branch(root,depth,adjacency,forbidden):
    seen={root}
    paths=[(root,)]
    for _ in range(depth):
        new=[]
        for word in paths:
            for v in adjacency[word[-1]]:
                if v in seen or v in forbidden:
                    return None
                seen.add(v)
                new.append((*word,v))
        paths=new
    return paths,seen

def connect(a,b,forward,blocked):
    prev={a:None}
    queue=deque([a])
    while queue:
        v=queue.popleft()
        if v==b:
            route=[]
            while v is not None:
                route.append(v)
                v=prev[v]
            return tuple(reversed(route))
        for w in forward[v]:
            if w not in prev and (w==b or w not in blocked):
                prev[w]=v
                queue.append(w)
    return None

def attempt(m,forward,backward,seed):
    rng=Random(seed)
    candidates=sorted(forward)
    rng.shuffle(candidates)
    depth=(m-2).bit_length()
    centers=[]
    trees=[]
    reserved=set()
    for c in candidates:
        if c in reserved:
            continue
        out=branch(c,depth,forward,reserved)
        if out is None:
            continue
        inc=branch(c,depth,backward,reserved | (out[1]-{c}))
        if inc is None:
            continue
        centers.append(c)
        trees.append((out[0],inc[0]))
        reserved.update(out[1] | inc[1])
        if len(centers)==m:
            break
    if len(centers)<m:
        return None
    demands=[(i,j) for i in range(m) for j in range(m) if i!=j]
    rng.shuffle(demands)
    paths={}
    links={}
    for i,j in demands:
        out=trees[i][0][j-(j>i)]
        inc=trees[j][1][i-(i>j)]
        link=connect(out[-1],inc[-1],forward,reserved)
        if not link:
            return None
        paths[i,j]=out+link[1:-1]+inc[::-1]
        links[i,j]=link
        reserved.update(link)
    return centers,paths,links

def verify_routes(graph,forward,chosen,centers,paths,links):
    m=len(centers)
    off={}
    labels={}
    centers_set=set(centers)
    for (i,j),word in paths.items():
        assert word[0]==centers[i] and word[-1]==centers[j]
        assert not (set(word[1:-1]) & centers_set)
        assert len(word)==len(set(word))
        for a,b in zip(word,word[1:]):
            assert b in forward[a] and chosen[b] in graph[a]
            off.setdefault(a,set()).add(b)
        arc=tuple(links[i,j][:2])
        assert arc not in labels
        labels[arc]=(i,j)

    # Re-enumerate every possible center-to-next-center walk in the actual
    # retained digraph, independently of the construction's intended paths.
    for i,center in enumerate(centers):
        actual=[]
        stack=[(center,)]
        while stack:
            path=stack.pop()
            for nxt in off.get(path[-1],()):
                assert nxt not in path
                child=path+(nxt,)
                if nxt in centers_set:
                    actual.append(child)
                else:
                    stack.append(child)
        expected=[paths[i,j] for j in range(m) if i!=j]
        assert set(actual)==set(expected) and len(actual)==len(expected)

    # Ruling out a cycle wholly outside the centers is essential for exclusion
    # of extra monomials, including disconnected unselected cycles.
    internals=set(off)-centers_set
    indeg={v:0 for v in internals}
    for a in internals:
        for b in off[a]:
            if b in indeg:
                indeg[b]+=1
    queue=deque(v for v,x in indeg.items() if x==0)
    removed=0
    while queue:
        v=queue.popleft()
        removed+=1
        for w in off[v]:
            if w in indeg:
                indeg[w]-=1
                if indeg[w]==0:
                    queue.append(w)
    assert removed==len(internals)

    # All possible choices in a perfect matching induce a dense permutation.
    # Check every dense permutation in these finite examples. Different
    # permutations have distinct monomials, each with exactly one extension
    # because its paths were enumerated uniquely above.
    total=0
    for pi in permutations(range(m)):
        used=set()
        monomial=[]
        for i,j in enumerate(pi):
            if i==j:
                monomial.append((i,i))
            else:
                p=paths[i,j]
                assert not (used & set(p[:-1]))
                used.update(p[:-1])
                monomial.extend(labels[a,b] for a,b in zip(p,p[1:]) if (a,b) in labels)
        assert sorted(monomial)==list(enumerate(pi))
        total+=1
    print(f'm={m} physical_vertices={len(graph)} matched_pairs={len(chosen)} used_directed_arcs={sum(map(len,off.values()))} verified_monomials={total}')
    return total

def run(p,m):
    graph=sextet(p)
    forward,backward,chosen=contract(graph)
    for seed in range(128):
        result=attempt(m,forward,backward,seed)
        if result:
            return verify_routes(graph,forward,chosen,*result)
    raise AssertionError('No routing under tested deterministic seeds')

if __name__=='__main__':
    run(41,5)
    run(73,7)
