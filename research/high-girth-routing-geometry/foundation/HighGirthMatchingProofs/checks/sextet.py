"""Generate Biggs–Hoare's bipartite sextet reservoir for primes p = 9 mod 16.

The graph is the connected projective-line sextet orbit of
{0,∞ | 1,-1 | i,-i}. Multiplication by a primitive eighth root gives the
neighbor that retains {0,∞}. The map (t+i)/(t-i) cycles the three duets.
Every projective transformation transports these three adjacencies.
"""
from collections import deque
from math import isqrt

def sextet(prime):
    if prime % 16 != 9 or any(prime % k == 0 for k in range(2,isqrt(prime)+1)):
        raise ValueError('Expected a prime congruent to 9 modulo 16')
    p = prime
    sigma = next(n for n in range(1,p) if pow(n,4,p)==p-1)
    i = sigma*sigma%p
    base = ((0,p),(1,p-1),(i,p-i))

    def multiply(m,n):
        a,b,c,d=m
        e,f,g,h=n
        return ((a*e+b*g)%p,(a*f+b*h)%p,(c*e+d*g)%p,(c*f+d*h)%p)

    inverses=[0]+[pow(k,-1,p) for k in range(1,p)]
    def key(m):
        a,b,c,d=m
        def image(t):
            n,den=(a,c) if t==p else (a*t+b,c*t+d)
            inv=inverses[den%p]
            return n*inv%p if inv else p
        return tuple(sorted(tuple(sorted((image(x),image(y)))) for x,y in base))

    identity=(1,0,0,1)
    rotate=(1,i,1,-i)
    scale=(sigma,0,0,1)
    operators=[scale,multiply(rotate,scale),multiply(multiply(rotate,rotate),scale)]
    assert key(rotate)==key(identity)
    initial=key(identity)
    indices={initial:0}
    queue=deque([identity])
    adjacency=[]
    while queue:
        matrix=queue.popleft()
        index=len(adjacency)
        assert indices[key(matrix)]==index
        neighbors=[]
        for operator in operators:
            next_matrix=multiply(matrix,operator)
            next_vertex=key(next_matrix)
            if next_vertex not in indices:
                indices[next_vertex]=len(indices)
                queue.append(next_matrix)
            neighbors.append(indices[next_vertex])
        adjacency.append(tuple(neighbors))
    return adjacency

def verify(prime):
    graph=sextet(prime)
    order=len(graph)
    assert order==prime*(prime**2-1)//24
    for v,neighbors in enumerate(graph):
        assert v not in neighbors and len(set(neighbors))==3
        assert all(v in graph[w] for w in neighbors)
    # The construction is vertex-transitive. Also check all roots for p=41.
    sources=range(order) if prime==41 else [0]
    best=order+1
    for source in sources:
        dist=[-1]*order
        parent=[-1]*order
        dist[source]=0
        todo=deque([source])
        while todo:
            a=todo.popleft()
            for b in graph[a]:
                if dist[b]<0:
                    parent[b]=a
                    dist[b]=dist[a]+1
                    todo.append(b)
                else:
                    assert (dist[b]-dist[a])%2==1
                    if parent[b]!=a and parent[a]!=b:
                        best=min(best,dist[a]+dist[b]+1)
        assert -1 not in dist
    assert 16*order**4<2**(3*best+10)
    print(f'p={prime} order={order} degree=3 connected bipartite girth={best} BFS-roots={len(sources)}')
if __name__=='__main__':
    verify(41)
    verify(73)
