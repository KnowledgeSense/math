"""Independent, standard-library audit of eight-point and order-16 certificates.
Does not import either author's checker. Enumeration and tiling decisions are
regenerated. Tiling solver uses frozensets, a minimum-candidates exact-cover
search, and deduplicates equal translates. All tests use explicit exceptions,
so python -O cannot silently disable verification.
"""
from pathlib import Path
from itertools import combinations
from collections import Counter, defaultdict
from math import comb
import json, hashlib, time
BASE=Path(__file__).resolve().parent.parent
OUT=Path(__file__).resolve().parent

def need(ok, msg):
    if not ok: raise ValueError(msg)

def dot(a,b):
    # Deliberately do not use the author's bit_count parity implementation.
    parity=0
    while a and b:
        parity ^= (a%2)*(b%2)
        a//=2; b//=2
    return parity

def walsh(T,a): return sum(1-2*dot(t,a) for t in T)

def valid_points(A,n,k,label):
    need(isinstance(A,list) and len(A)==k,label+' cardinality')
    need(all(type(x) is int and 0<=x<n for x in A),label+' ambient coordinates')
    need(len(set(A))==k,label+' distinctness')

def tiling_search(T,r):
    """Exact cover with actual subsets, independently from bit-mask algorithms."""
    U=frozenset(range(2**r))
    translate_to_shift={}
    for x in sorted(U,reverse=True):
        translate_to_shift[frozenset(t^x for t in T)]=x
    tiles=tuple(translate_to_shift)
    rejected=set()
    def search(uncovered):
        if not uncovered: return []
        if uncovered in rejected:return None
        live=[A for A in tiles if A<=uncovered]
        options={p:[] for p in uncovered}
        for A in live:
            for p in A:options[p].append(A)
        p=min(uncovered,key=lambda p:(len(options[p]),p))
        for A in options[p]:
            tail=search(uncovered-A)
            if tail is not None:return [translate_to_shift[A]]+tail
        rejected.add(uncovered)
        return None
    return search(U)

def verify_tiling(T,A,r):
    valid_points(A,2**r,(2**r)//len(T),'tiling witness')
    multiplicities=Counter(x^t for t in T for x in A)
    need(multiplicities==Counter({x:1 for x in range(2**r)}),'tiling multiplicities')

def verify_eight():
    raw=(BASE/'eight_certificates.json').read_bytes()
    data=json.loads(raw)
    index={}
    for d in data:
        key=(d['r'],tuple(sorted(d['T'])))
        need(key not in index,'duplicate record')
        index[key]=d
    expected=[]
    for r in range(3,8):
        basis=set([0]+[2**i for i in range(r)])
        for other in combinations(sorted(set(range(2**r))-basis),8-len(basis)):
            expected.append((r,tuple(sorted(basis|set(other)))))
    need(set(index)==set(expected),'enumeration mismatch')
    counts=defaultdict(Counter)
    regenerated=[]
    for r,T in expected:
        d=index[(r,T)]
        witness=tiling_search(T,r)
        is_tile=witness is not None
        need(is_tile==(d['tile'] is not None),'independent tiling classification mismatch')
        counts[r]['total']+=1
        counts[r]['tiles' if is_tile else 'non_tiles']+=1
        if is_tile:
            verify_tiling(T,witness,r)
            verify_tiling(T,d['tile'],r)
            valid_points(d['spectrum'],2**r,8,'spectrum')
            need(all(walsh(T,a^b)==0 for a,b in combinations(d['spectrum'],2)),'spectrum Gram matrix')
            valid_points(d['universal'],2**r,(2**r)//8,'universal spectrum')
            need(all(walsh(T,a^b)!=0 for a,b in combinations(d['universal'],2)),'universal nonzero differences')
        regenerated.append({'r':r,'T':T,'tile':witness})
    (OUT/'independent_eight_tilings.json').write_text(json.dumps(regenerated,indent=2)+'\n')
    return {'sha256':hashlib.sha256(raw).hexdigest(),'counts':dict(counts)}

def echelon_rows(rows):
    pivots={}
    for row in rows:
        v=row
        while v:
            p=v.bit_length()-1
            if p in pivots:v^=pivots[p]
            else:pivots[p]=v;break
    return list(pivots.values())

def hadamard_column_set(H):
    n=len(H)
    need(all(len(row)==n for row in H),'square Hadamard')
    need(all(sum(H[i][j]*H[k][j] for j in range(n))==(n if i==k else 0)
             for i in range(n) for k in range(n)),'Hadamard identity')
    L=[[int(H[i][j]*H[i][0]*H[0][j]*H[0][0]==-1) for j in range(n)] for i in range(n)]
    rowwords=[sum(v<<j for j,v in enumerate(row)) for row in L]
    basis=echelon_rows(rowwords)
    E=[sum(((row>>j)&1)<<i for i,row in enumerate(basis)) for j in range(n)]
    need(len(set(E))==n,'canonical columns distinct')
    return E,len(basis)

def verify_sixteen():
    out=[]
    for k in range(5):
        path=BASE/f'had.16.{k}.txt'; raw=path.read_bytes()
        H=[[1 if v=='+' else -1 for v in line.strip()] for line in raw.decode().splitlines()
           if len(line.strip())==16 and set(line.strip())<=set('+-')]
        need(len(H)==16,'matrix text shape')
        item={'class':k,'sha256':hashlib.sha256(raw).hexdigest()}
        for orientation,M in [('original',H),('transpose',list(map(list,zip(*H))))]:
            E,r=hadamard_column_set(M)
            T=tiling_search(E,r)
            need(T is not None,'order-16 canonical set does not tile')
            verify_tiling(E,T,r)
            item[orientation]={'r':r,'E':E,'T':T}
        out.append(item)
    (OUT/'independent_sixteen_tilings.json').write_text(json.dumps(out,indent=2)+'\n')
    return [{'class':d['class'],'original_rank':d['original']['r'],'transpose_rank':d['transpose']['r']} for d in out]

def verify_snf_bound():
    exponents=sorted([k for k in range(8) for _ in range(comb(7,k))])
    need(len(exponents)==128,'SNF length')
    out=[]
    for m in range(4,65,4):
        if m&(m-1)==0:continue
        odd=m;v=0
        while odd%2==0:odd//=2;v+=1
        determinant_v=(m//2)*v
        minor_bound=sum(exponents[:m])
        need(determinant_v<minor_bound,'SNF exclusion failed')
        out.append({'m':m,'Hadamard_determinant_v2':determinant_v,'minor_divisibility_v2':minor_bound})
    return out

def verify_universal_slicing():
    B=[0,126,125,123,119,111,95,63,127,115,121,122,107,91,59,4]
    S=[0,1,2,4,8,16,32,64]
    valid_points(B,128,16,'simplex universal witness')
    need(all(walsh(S,a^b)!=0 for a,b in combinations(B,2)),'simplex universal witness failed')
    # Verify slicing on every normalized set, including every non-tile.
    counts=Counter()
    for r in range(3,8):
        fixed=[0]+[2**i for i in range(r)]
        for rest in combinations([x for x in range(2**r) if x not in fixed],7-r):
            T=fixed+list(rest)
            embedding={sum(dot(a,t)<<i for i,t in enumerate(T[1:])):a for a in range(2**r)}
            U=set(embedding)
            slices=[]
            for b in B:
                # All translated slices through a point of B suffice for max size.
                C=[embedding[x^b] for x in B if x^b in U]
                slices.append(C)
            C=max(slices,key=len)[:2**(r-3)]
            need(len(C)==2**(r-3),'slicing cardinality')
            need(all(walsh(T,a^b)!=0 for a,b in combinations(C,2)),'slicing Fourier differences')
            counts[r]+=1
    return {'simplex_witness':B,'normalized_sets_sliced':dict(counts)}

if __name__=='__main__':
    start=time.time()
    report={'eight':verify_eight(),'sixteen':verify_sixteen(),'snf':verify_snf_bound(),'slicing':verify_universal_slicing()}
    report['seconds']=round(time.time()-start,3)
    (OUT/'audit_results.json').write_text(json.dumps(report,indent=2)+'\n')
    print(json.dumps(report,indent=2))
