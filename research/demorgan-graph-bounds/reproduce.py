"""Reproduce graph coverage and the unrestricted circuit lower bounds."""
from argparse import ArgumentParser
from pathlib import Path
from subprocess import run
from tempfile import TemporaryDirectory
import sys

ROOT=Path(__file__).resolve().parent

def checked(args,**kwargs):
    return run([str(arg) for arg in args],check=True,**kwargs)

def main():
    parser=ArgumentParser()
    parser.add_argument('family',choices=('subcubic','girth5'))
    parser.add_argument('--coverage-only',action='store_true')
    args=parser.parse_args()
    narrow=args.family=='subcubic'
    end=12 if narrow else 9
    checked([sys.executable,ROOT/('coverage.py' if narrow else 'coverage_girth5.py'),end])
    if args.coverage_only:return
    with TemporaryDirectory() as tmp:
        d=Path(tmp)
        for n in range(3,end+1):
            exe=d/f'lower{n}'
            checked(['c++','-std=c++17','-O3',f'-DVERTICES={n}',ROOT/'larger.cpp','-o',exe])
            prefix='catalogue' if narrow else 'graphs'
            name=ROOT/f'{prefix}-{n}.txt'
            original=dict(tuple(map(int,x.split())) for x in name.read_text().splitlines())
            pending=dict(original)
            for depth in (6,8,10,11,12):
                if not pending:break
                todo=d/'pending.txt'
                todo.write_text(''.join(f'{m} {target}\n' for m,target in pending.items()))
                output=checked([exe,depth,n-1,todo],capture_output=True,text=True).stdout
                got={}
                for line in output.splitlines():
                    m,lower,upper,_=map(int,line.split())
                    assert m in pending and m not in got and lower<=upper==pending[m]
                    got[m]=lower
                assert got.keys()==pending.keys()
                pending={m:u for m,u in pending.items() if got[m]<u}
            assert not pending, f'Outstanding at {n}: {pending}'
            print(n,len(original),'unrestricted circuit minima verified',flush=True)
if __name__=='__main__':main()
