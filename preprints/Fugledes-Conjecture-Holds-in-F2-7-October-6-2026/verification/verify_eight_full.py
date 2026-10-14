"""Independent standard-library verification of the complete 8-point theorem.
Reads only witness data. Checks all negative cases for both properties. Uses exact-cover recursion, not the generating program's
Cayley-graph maximum-clique routine, to verify all negative tiling cases.
"""
import itertools,json,collections,time
from pathlib import Path
P=Path(__file__).resolve().parent
if not __debug__: raise RuntimeError('Run without Python -O')

def exact_cover(T,r):
    n=1<<r;full=(1<<n)-1
    trans=[sum(1<<(x^t) for t in T) for x in range(n)]
    cover=[[m for m in trans if m>>i&1] for i in range(n)]
    seen=set()
    def rec(used):
        if used==full:return True
        if used in seen:return False
        unseen=full^used
        # All translations covering the first uncovered point must be tried
        bit=unseen&-unseen;i=bit.bit_length()-1
        for m in cover[i]:
            if not used&m and rec(used|m):return True
        seen.add(used);return False
    return rec(0)

def W(T,a):return sum(1 if (a&t).bit_count()%2==0 else -1 for t in T)

def has_spectrum(T,r):
    # Any spectrum can be translated to contain 0. Its remaining seven
    # elements form a clique in the Fourier-zero Cayley graph.
    n=1<<r
    zeros={a for a in range(1,n) if W(T,a)==0}
    adj={a:{b for b in zeros if a!=b and W(T,a^b)==0} for a in zeros}
    def rec(candidates,need):
        if need==0:return True
        if len(candidates)<need:return False
        candidates=set(candidates)
        # Every clique either includes the selected vertex or omits it.
        while len(candidates)>=need:
            a=min(candidates,key=lambda x:(len(adj[x]&candidates),x))
            candidates.remove(a)
            if rec(candidates & adj[a],need-1):return True
        return False
    return rec(zeros,7)

def main():
    data=json.loads((P/'eight_certificates.json').read_text());expected=set()
    for r in range(3,8):
        base=[0]+[1<<i for i in range(r)]
        for extra in itertools.combinations([i for i in range(1<<r) if i not in base],7-r):expected.add((r,tuple(base+list(extra))))
    assert len(data)==549 and {(d['r'],tuple(d['T'])) for d in data}==expected
    assert len(expected)==len(data)
    counts=collections.Counter();start=time.time()
    for d in data:
        r=d['r'];n=1<<r;T=d['T'];tile=d['tile'];spectrum=d['spectrum'];B=d['universal']
        assert len(T)==len(set(T))==8
        if tile:
            assert len(tile)==len(set(tile))==n//8
            assert len({a^b for a in T for b in tile})==n
            assert len(spectrum)==len(set(spectrum))==8
            assert all(W(T,a^b)==0 for a in spectrum for b in spectrum if a!=b)
            assert len(B)==len(set(B))==n//8
            assert all(W(T,a^b)!=0 for a in B for b in B if a!=b)
            counts['tile_and_universal']+=1
        else:
            assert not exact_cover(T,r), (r,T)
            assert not has_spectrum(T,r), ('SPECTRAL NON-TILE',r,T)
            counts['neither_tile_nor_spectral']+=1
    print('VERIFIED',dict(counts),'total',len(data),'seconds',round(time.time()-start,3))
if __name__=='__main__':main()
