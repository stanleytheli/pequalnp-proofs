"""Decide variable-occurrence bounds for edge formulas on simple graphs of girth at least five."""
from collections import deque

def star_orientation(n, edges, bounds):
    """Return an endpoint for every edge, or a Hall-deficient set of vertices."""
    if len(bounds)!=n or any(b<0 for b in bounds):
        raise ValueError("provide one nonnegative occurrence bound per vertex")
    incident=[[] for _ in range(n)]
    adjacent=[set() for _ in range(n)]
    for e,(u,v) in enumerate(edges):
        if not (0<=u<n and 0<=v<n) or u==v or v in adjacent[u]:
            raise ValueError("expected a simple graph on vertices 0 through n-1")
        adjacent[u].add(v)
        adjacent[v].add(u)
        incident[u].append(e)
        incident[v].append(e)
    for u in range(n):
        for v in range(u):
            common=adjacent[u]&adjacent[v]
            if len(common)>1 or (common and v in adjacent[u]):
                raise ValueError("expected no three- or four-cycles")
    demands=[len(inc)-b+1 if len(inc)>b else 0 for inc,b in zip(incident,bounds)]
    vertices=[v for v in range(n) for _ in range(demands[v])]
    match=[None]*len(edges)
    for new in range(len(vertices)):
        queue=deque([new])
        parent={new:None}
        found=None
        while queue and found is None:
            slot=queue.popleft()
            for e in incident[vertices[slot]]:
                occupant=match[e]
                if occupant is None:
                    found=(slot,e)
                    break
                if occupant not in parent:
                    parent[occupant]=(slot,e)
                    queue.append(occupant)
        if found is None:
            obstruction={vertices[i] for i in parent}
            available={e for v in obstruction for e in incident[v]}
            assert len(available)<sum(demands[v] for v in obstruction)
            return None,obstruction
        slot,e=found
        while True:
            match[e]=slot
            if parent[slot] is None:break
            slot,e=parent[slot]
    owner=[edges[i][0] if slot is None else vertices[slot] for i,slot in enumerate(match)]
    return owner,None

def formula_occurrences(n,edges,owner):
    """Group the edges into stars and return their exact variable-use counts."""
    groups=[[] for _ in range(n)]
    for (u,v),center in zip(edges,owner):
        if center not in (u,v):raise ValueError("edge owner must be an endpoint")
        groups[center].append(v if center==u else u)
    counts=[int(bool(neighbors)) for neighbors in groups]
    for neighbors in groups:
        for v in neighbors:counts[v]+=1
    return groups,counts

def readability(n,edges):
    low=0
    high=max((sum(v in e for e in edges) for v in range(n)),default=0)
    while low<high:
        mid=(low+high)//2
        owner,_=star_orientation(n,edges,[mid]*n)
        if owner is None:low=mid+1
        else:high=mid
    owner,_=star_orientation(n,edges,[low]*n)
    groups,counts=formula_occurrences(n,edges,owner)
    assert max(counts,default=0)==low
    return low,groups
