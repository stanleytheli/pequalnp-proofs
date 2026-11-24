"""Direct perfect matchings versus the two-part record graph and critical zero rectangles."""
from itertools import combinations, permutations


def cells(m, rows, cols):
    return sum(1<<(r*m+c) for r in rows for c in cols)


def matches(mask, perms):
    return any(mask&p==p for p in perms)


def records(m):
    cut=m//2
    halves=(list(range(cut)),list(range(cut,m)))
    output=[]
    for k in range(1,m+1):
        for rows in combinations(range(m),k):
            sides = []
            for cols in halves:
                sides.append([(j,cells(m,rows,u)) for j in range(len(cols)+1) for u in combinations(cols,j)])
            output.extend((a,b) for j,a in sides[0] for h,b in sides[1] if j+h==m-k+1)
    return output


def verify(m):
    full=(1<<(m*m))-1
    perms=[sum(1<<(i*m+j) for i,j in enumerate(p)) for p in permutations(range(m))]
    rects=records(m)
    critical=0
    for a,b in rects:
        zero=full^(a|b)
        assert not matches(zero,perms)
        for cell in range(m*m):
            if not (zero>>cell&1):
                assert matches(zero|(1<<cell),perms)
                critical+=1
    # Check every Boolean adjacency matrix up to order four, using the actual record edge conditions.
    if m<=4:
        for x in range(1<<(m*m)):
            assert matches(x,perms)==all((x&a or x&b) for a,b in rects)
    return len(rects),critical


def check_rect_cover():
    m=3
    rects=[(set(r),set(t),cells(m,r,t)) for a in range(1,m+1) for b in range(1,m+1)
           for r in combinations(range(m),a) for t in combinations(range(m),b)]
    count=0
    for s,t,whole in rects:
        for a,b,first in rects:
            for c,d,second in rects:
                if first|second!=whole:
                    continue
                assert first==whole or second==whole or a==c==s or b==d==t
                count+=1
    return count


if __name__=='__main__':
    for m in range(1,7):
        print('order, distinct Hall obstructions, single-edge repairs',m,*verify(m))
    print('independent two-rectangle covers checked on 3×3 universe',check_rect_cover())
