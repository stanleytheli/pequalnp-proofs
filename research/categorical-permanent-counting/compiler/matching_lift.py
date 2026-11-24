"""Tight-cut decomposition and integer affine readouts on its leaf matchings.

An edge is an individually numbered (left vertex, right vertex) pair. Parallel
edge IDs are distinct. Colors X and Y must be complementary hitting families
on the perfect matchings, and neutral edges are allowed. No nonstandard modules.
"""
from collections import Counter, defaultdict, deque
from dataclasses import dataclass, field
from itertools import combinations, permutations, product


@dataclass
class Board:
    left: frozenset
    right: frozenset
    edges: dict

    @classmethod
    def square(cls, n, endpoints):
        cells = dict(enumerate(endpoints))
        side = frozenset(range(n))
        if any(i not in side or j not in side for i,j in cells.values()):
            raise ValueError("An endpoint is outside the board")
        return cls(side, side, cells)

    def keep(self, ids):
        return Board(self.left, self.right, {e:self.edges[e] for e in ids})


def solve(board, fixed=(), omitted=()):
    """One perfect matching, or (None, Hall-deficient left set in the residual)."""
    used_l, used_r = set(), set()
    banned = set(omitted)
    for e in fixed:
        if e not in board.edges or e in banned:
            return None, None
        i,j = board.edges[e]
        if i in used_l or j in used_r:
            return None, None
        used_l.add(i)
        used_r.add(j)
    adj = defaultdict(list)
    for e,(i,j) in board.edges.items():
        if e not in banned and i not in used_l and j not in used_r:
            adj[i].append((j,e))
    by_l, by_r = {}, {}
    def augment(i, visited):
        for j,e in adj[i]:
            if j in visited:
                continue
            visited.add(j)
            if j not in by_r or augment(by_r[j], visited):
                by_r[j], by_l[i] = i,e
                return True
        return False
    residual = board.left-used_l
    for i in sorted(residual):
        augment(i, set())
    if len(by_l)==len(residual):
        return frozenset(fixed)|frozenset(by_l.values()), None
    queue = deque(residual-by_l.keys())
    reached = set(queue)
    while queue:
        i = queue.popleft()
        for j,_ in adj[i]:
            if j not in by_r:
                raise AssertionError("Maximum matching has an augmenting path")
            if by_r[j] not in reached:
                reached.add(by_r[j])
                queue.append(by_r[j])
    return None, frozenset(reached)


def all_matchings(board):
    """Finite control, and the enumerator for small terminal factors."""
    rows = sorted(board.left)
    by_cell = defaultdict(list)
    for e,ij in board.edges.items():
        by_cell[ij].append(e)
    return [frozenset(ms) for cols in permutations(sorted(board.right))
            for ms in product(*(by_cell[i,j] for i,j in zip(rows,cols)))]


def components(board):
    adj = defaultdict(set)
    for i,j in board.edges.values():
        adj[0,i].add((1,j))
        adj[1,j].add((0,i))
    unseen = {(0,i) for i in board.left}|{(1,j) for j in board.right}
    parts = []
    while unseen:
        start = min(unseen)
        todo, reached = [start], {start}
        while todo:
            more = adj[todo.pop()]-reached
            reached.update(more)
            todo.extend(more)
        unseen -= reached
        a = frozenset(i for side,i in reached if side==0)
        b = frozenset(j for side,j in reached if side==1)
        parts.append(Board(a,b,{e:(i,j) for e,(i,j) in board.edges.items() if i in a}))
    return parts


@dataclass
class Node:
    board: Board
    kind: str
    children: tuple = ()
    cut: tuple = ()
    refs: dict = field(default_factory=dict)
    marker: tuple = ()
    index: int = -1
    matches: tuple = ()


@dataclass
class Form:
    constant: int = 0
    terms: Counter = field(default_factory=Counter)

    def add(self, rhs, factor=1):
        self.constant += factor*rhs.constant
        for key, val in rhs.terms.items():
            self.terms[key] += factor*val
        return self


class Lift:
    def __init__(self, board):
        if len(board.left)!=len(board.right) or solve(board)[0] is None:
            raise ValueError("The square board must have a perfect matching")
        available = [e for e in board.edges if solve(board,[e])[0] is not None]
        self.board = board.keep(available)
        self.leaves = []
        self.links = []
        self.next_marker = max(board.left | board.right, default=-1)+1
        groups = components(self.board)
        # The empty board has one empty matching.
        self.roots = [self.decompose(g) for g in groups or [self.board]]
        self.edge_owner = {}
        for leaf in self.leaves:
            for e in leaf.board.edges:
                self.edge_owner.setdefault(e,leaf.index)

    def decompose(self, board):
        if len(board.left)<=3:
            node = Node(board, "small", index=len(self.leaves), matches=tuple(all_matchings(board)))
            self.leaves.append(node)
            return node
        for e,f in combinations(board.edges,2):
            i,j = board.edges[e]
            k,l = board.edges[f]
            if i==k or j==l:
                continue
            full, shore = solve(board, (e,f))
            if full is not None:
                continue
            neighbors = frozenset(j for i,j in board.edges.values() if i in shore)
            assert 1<=len(shore)<=len(board.left)-2 and len(neighbors)==len(shore)+1
            left_marker, right_marker = self.next_marker, self.next_marker+1
            self.next_marker += 2
            inner = Board(shore|{left_marker}, neighbors,
                          {p:(i if i in shore else left_marker,j) for p,(i,j) in board.edges.items()
                           if j in neighbors})
            outer = Board(board.left-shore, (board.right-neighbors)|{right_marker},
                          {p:(i,j if j not in neighbors else right_marker) for p,(i,j) in board.edges.items()
                           if i not in shore})
            cross = tuple(sorted(inner.edges.keys() & outer.edges.keys()))
            refs = {p:(solve(inner,[p])[0],solve(outer,[p])[0]) for p in cross}
            assert cross and all(x is not None and y is not None for x,y in refs.values())
            children = self.decompose(inner), self.decompose(outer)
            # Each marker is a unique vertex surviving at a terminal factor.
            li, = [l.index for l in self.leaves if left_marker in l.board.left]
            ri, = [l.index for l in self.leaves if right_marker in l.board.right]
            self.links.append((li,ri,cross))
            return Node(board,"cut",children,cross,refs,(left_marker,right_marker))
        node = Node(board, "brace", index=len(self.leaves))
        self.leaves.append(node)
        return node

    def edge_form(self, node, e):
        """Read an edge incidence on one terminal descendant."""
        while node.kind=="cut":
            node = next(child for child in node.children if e in child.board.edges)
        if node.kind=="brace":
            return Form(0,Counter({(node.index,e):1}))
        return Form(0,Counter({(node.index,m):1 for m in node.matches if e in m}))

    @staticmethod
    def flag(m, x, y):
        red, blue = bool(m & x), bool(m & y)
        if red and blue:
            raise ValueError("Conflicting colors in a reference completion")
        return int(red)-int(blue)

    def observable(self, x, y):
        x = frozenset(x)&self.board.edges.keys()
        y = frozenset(y)&self.board.edges.keys()
        if solve(self.board,omitted=x|y)[0] is not None:
            raise ValueError("Some perfect matching has no color")
        for e in x:
            for f in y:
                if solve(self.board,tuple({e,f}))[0] is not None:
                    raise ValueError("Some perfect matching has both colors")
        if len(self.roots)==1:
            return self.local_form(self.roots[0],x,y)
        choices = [solve(t.board)[0] for t in self.roots]
        whole = frozenset().union(*choices)
        base = int(bool(whole&x))
        result = Form((1-len(choices))*base)
        for t,m in zip(self.roots,choices):
            tag = self.flag(whole-m,x,y)
            if tag:
                result.add(Form(int(tag>0)))
            else:
                result.add(self.local_form(t,x&t.board.edges.keys(),y&t.board.edges.keys()))
        return result

    def local_form(self, node, x, y):
        if node.kind=="small":
            return Form(0,Counter({(node.index,m):1 for m in node.matches if m&x}))
        if node.kind=="brace":
            for family, sign in [(x,1),(y,-1)]:
                if all(node.board.edges[e][0]==node.board.edges[f][0] or
                       node.board.edges[e][1]==node.board.edges[f][1]
                       for e,f in combinations(family,2)):
                    return Form(int(sign<0), Counter({(node.index,e):sign for e in family}))
            raise AssertionError("A pure category on a large brace violated rectangle avoidance")
        result = Form()
        for side, child in enumerate(node.children):
            red, blue = set(x)&child.board.edges.keys(), set(y)&child.board.edges.keys()
            for p, pair in node.refs.items():
                tag = self.flag(pair[1-side],x,y)
                if tag>0: red.add(p)
                if tag<0: blue.add(p)
            result.add(self.local_form(child,red,blue))
        for p,(left,right) in node.refs.items():
            if (left|right)&x:
                result.add(self.edge_form(node,p),-1)
        return result
