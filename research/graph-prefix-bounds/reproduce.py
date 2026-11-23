"""Rebuild the lower bounds and check the upper circuits and graph coverage."""
from pathlib import Path
import argparse,subprocess,tempfile
ROOT=Path(__file__).resolve().parent
def call(args,**kwargs):
    return subprocess.run([str(i) for i in args],check=True,**kwargs)
def rows(path):
    return [tuple(map(int,r.split())) for r in path.read_text().splitlines()]
def main():
    parser=argparse.ArgumentParser()
    parser.add_argument('size',type=int,choices=[9,10])
    parser.add_argument('--coverage-only',action='store_true')
    args=parser.parse_args()
    import sys
    call([sys.executable,ROOT/'verify_catalogue.py',args.size])
    if args.coverage_only:return
    with tempfile.TemporaryDirectory() as temp:
        d=Path(temp);nine=d/'nine'
        call(['c++','-std=c++17','-O3','-DVERTICES=9',ROOT/'nine.cpp','-o',nine])
        tab=call([nine,9,2,ROOT/'graphs-9.txt'],capture_output=True,text=True).stdout
        expected=dict(rows(ROOT/'graphs-9.txt'));got={}
        for row in tab.splitlines():
            m,lo,hi,vis=map(int,row.split());assert lo==hi==expected[m];got[m]=lo
        assert got==expected and len(got)==179
        print('Verified all 179 nine-vertex lower bounds starting from the two-vertex base.',flush=True)
        if args.size==9:return
        ten=d/'ten'
        call(['c++','-std=c++17','-O3','-DVERTICES=10',ROOT/'ten.cpp','-o',ten])
        target={m:(lo,hi) for m,lo,hi in rows(ROOT/'ten-results.txt')}
        result={m:0 for m in target}
        stronger=d/'ten-pareto'
        call(['c++','-std=c++17','-O3','-DVERTICES=10',ROOT/'ten_pareto.cpp','-o',stronger])
        for depth in (5,8,10,12):
            todo=[(m,hi) for m,(lo,hi) in target.items() if result[m]<lo]
            if not todo:break
            subset=d/'cases.txt';subset.write_text(''.join(f'{m} {hi}\n' for m,hi in todo))
            proc=subprocess.Popen([str(stronger if depth==12 else ten),str(depth),'9',str(subset)],stdout=subprocess.PIPE,text=True)
            for line in proc.stdout:
                m,lo,hi,vis=map(int,line.split());assert target[m][1]==hi and lo<=hi
                result[m]=max(result[m],lo)
            assert proc.wait()==0
            print('Depth',depth,'verified',sum(result[m]>=lo for m,(lo,_) in target.items()),'of',len(target),flush=True)
        assert all(result[m]>=lo for m,(lo,_) in target.items())
if __name__=='__main__':main()
