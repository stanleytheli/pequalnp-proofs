"""Check every grouped parity instance and its physical witness on small sizes."""
from itertools import product
from math import ceil


def parity(x):
    return bin(x).count('1')%2


def check(k,m):
    size = [m//k+(j<m%k) for j in range(k)]
    groups = []
    offsets = []
    offsets_bits = []
    a = 0
    consumed = 0
    for length in size:
        offsets.append(a)
        offsets_bits.append(consumed)
        g = [(w,p,p^parity(w)) for w,p in product(range(1 << length),range(2))]
        groups.append(g)
        a += len(g)
        consumed += length

    def row(j, test):
        return sum(1 << (offsets[j]+h) for h,(w,p,e) in enumerate(groups[j]) if test(w,p,e))

    forced = [row(j,lambda w,p,e:True) for j in range(k)]
    constraints = [row(0,lambda w,p,e:p==0),row(k-1,lambda w,p,e:e==1)]
    for j in range(k-1):
        constraints += [row(j,lambda w,p,e:e==0) | row(j+1,lambda w,p,e:p==1),
                        row(j,lambda w,p,e:e==1) | row(j+1,lambda w,p,e:p==0)]
    alternatives = [(row(j,lambda w,p,e,h=h:((w>>h)&1)==0),
                     row(j,lambda w,p,e,h=h:((w>>h)&1)==1))
                    for j in range(k) for h in range(size[j])]
    tag = len(constraints)+1
    fixed = forced+[v|((i+1)<<a) for i,v in enumerate(constraints)]
    options = [(l | ((tag+2*i)<<a), r | ((tag+2*i+1)<<a)) for i,(l,r) in enumerate(alternatives)]
    all_rows = [0]+fixed+[v for pair in options for v in pair]
    assert len(set(all_rows))==len(all_rows)
    assert max(all_rows).bit_length() <= 2*k*(1<<ceil(m/k))+(2*m+2*k).bit_length()

    selections = [sum(1<<(offsets[j]+h) for j,h in enumerate(v))
                  for v in product(*(range(len(g)) for g in groups))]
    count = 0
    for b in range(1<<m):
        positive = fixed+[options[i][(b>>i)&1] for i in range(m)]
        hits = [w for w in selections if all(w&v for v in positive)]
        assert len(hits)==parity(b)
        if hits:
            assert bin(hits[0]).count('1')==k
            # The actual k-input OR tree agrees with every prescribed row.
            bits = [i for i in range(a) if (hits[0]>>i)&1]
            for v in [0]+positive:
                out = bool((v>>bits[0])&1)
                for i in bits[1:]:
                    out = out or bool((v>>i)&1)
                assert out==bool(v)
        count += 1
    return count


if __name__=='__main__':
    total = sum(check(k,m) for k in range(1,5) for m in range(k,8))
    print(f'{total} parity labelings checked with one to four groups; all witnesses and tagged rows verified')
