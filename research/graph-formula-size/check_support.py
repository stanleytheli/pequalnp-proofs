"""Independent optimization of edges minus cover size over every support size."""
from pathlib import Path
from plane import SIDES,group
from itertools import combinations
def solve():
    # The collineations preserving the two parts act on 13 point bits. For each
    # point orbit compute the optimal line choice directly from the definition of a cover.
    maps=[p for p in group() if p[0]<13]
    columns=[sum(1<<i for i,row in enumerate(SIDES) if j in row) for j in range(13)]
    seen=set()
    score=[-100]*27
    for points in range(1<<13):
        if points in seen:continue
        indices=[i for i in range(13) if points>>i&1]
        seen.update(sum(1<<p[i] for i in indices) for p in maps)
        a=len(indices);U=points
        while True:
            weights=sorted(((points&neighbors).bit_count()-bool(U&neighbors) for neighbors in columns),reverse=True)
            # U consists of the selected points omitted from a proposed cover.
            total=-(a-U.bit_count())
            for b in range(14):
                if a+b:score[a+b]=max(score[a+b],total-(a+b-1))
                if b<13:total+=weights[b]
            if not U:break
            U=(U-1)&points
    return score
if __name__=='__main__':
    actual=solve()
    rows=Path(__file__).with_name('support.txt').read_text().splitlines()
    for line in rows:
        r,expected,p,l=map(int,line.split())
        assert actual[r]==expected
    print('Matched every maximum for 1 through 26 vertices. First positive support size:',next(r for r in range(1,27) if actual[r]>0))
