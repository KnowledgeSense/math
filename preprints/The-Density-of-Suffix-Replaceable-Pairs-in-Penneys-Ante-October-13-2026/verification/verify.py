"""Finite checks for the suffix-generator criterion and overlap probabilities."""
# Author: Knowledge Sense
from itertools import product, combinations
from fractions import Fraction
from pathlib import Path
import json

def words(n):
    return [''.join(p) for p in product('01',repeat=n)]

def occurs(x,t):
    return sum(x[i:i+len(t)]==t for i in range(len(x)-len(t)+1))

def terminal(u,t,other):
    x=u+t
    return occurs(x,t)==1 and occurs(x,other)==0

def direct_R(v,w,contexts):
    return all(terminal(u,v,w)==terminal(u,w,v) for u in contexts)

def generators(a,t):
    return {a[:-k] for k in range(1,len(a)) if a[-k:]==t[:k]}

def generator_R(v,w):
    if v==w: return True
    bv=generators(v,v)|generators(w,v)
    bw=generators(v,w)|generators(w,w)
    return (all(any(x.endswith(y) for y in bw) for x in bv)
        and all(any(x.endswith(y) for y in bv) for x in bw))

def E(v,w,K):
    return all((a[-k:]==v[:k])==(a[-k:]==w[:k])
               for a in (v,w) for k in range(1,K+1))

def exceptional(v,w,K):
    n=len(v)
    a=any(s[-k:]==t[:k] for s in (v,w) for t in (v,w)
          for k in range(K+1,n))
    blocks=[s[i:i+n-2*K] for s in (v,w) for i in range(K+1)]
    b=len(set(blocks))<len(blocks)
    return a or b

counts=[]
localization_count=0
redundancy_witness=None
for n in range(1,7):
    ws=words(n)
    cs=[s for m in range(n) for s in words(m)]
    r_count=0
    for v,w in product(ws,repeat=2):
        direct=direct_R(v,w,cs)
        assert direct==generator_R(v,w),(n,v,w,'generator')
        r_count+=direct
        if v!=w and direct and not E(v,w,n-1) and redundancy_witness is None:
            redundancy_witness={'v':v,'w':w,'B_v':sorted(generators(v,v)|generators(w,v)),'B_w':sorted(generators(v,w)|generators(w,w))}
        for K in range(1,(n-1)//2+1):
            if not exceptional(v,w,K):
                localization_count+=1
                assert direct==E(v,w,K),(n,v,w,K,'localization')
    counts.append({'n':n,'all_ordered_pairs':4**n,'literal_R':r_count,'distinct_R':r_count-2**n})

def probability_equalities(total,edges,fixed):
    par=list(range(total))
    def find(a):
        while par[a]!=a:
            par[a]=par[par[a]];a=par[a]
        return a
    for a,b in edges:
        a,b=find(a),find(b)
        if a!=b: par[a]=b
    states={}
    for a,value in fixed.items():
        root=find(a)
        if root in states and states[root]!=value: return Fraction(0)
        states[root]=value
    roots={find(i) for i in range(total)}
    free_components=len(roots)-len(states)
    unfixed=total-len(fixed)
    return Fraction(1,2**(unfixed-free_components))

conditional_tests=0
for L in range(1,9):
    for n in range(4*L,65):
        fixed={i:0 for i in range(L)}|{i:1 for i in range(n-L,n)}
        fixed_cross=fixed|{n+i:v for i,v in fixed.items()}
        for k in range(1,n):
            d=n-k
            ps=probability_equalities(n,[(i,i+d) for i in range(k)],fixed)
            pc=probability_equalities(2*n,[(i+d,n+i) for i in range(k)],fixed_cross)
            if k<2*L: assert ps==pc==0,(L,n,k,'short')
            else:
                assert ps in [0,Fraction(1,2**k)],(L,n,k,'self',ps)
                expected=Fraction(1,2**(k if d>=L else n-2*L+d))
                assert pc==expected,(L,n,k,'cross',pc,expected)
            conditional_tests+=2

result={'scope':'Finite supplementary checks; the limiting theorem is proved analytically',
        'ordered_pairs_checked':sum(4**n for n in range(1,7)),
        'counts':counts,'localizations_outside_exceptions_checked':localization_count,
        'redundancy_witness':redundancy_witness,
        'conditional_probabilities_checked':conditional_tests,
        'conditional_ranges':{'L':'1..8','n':'4L..64','k':'1..n-1'},
        'failures':0}
Path(__file__).with_name('independent_checks_result.json').write_text(json.dumps(result,ensure_ascii=False,indent=2),encoding='utf-8')
print(json.dumps(result,ensure_ascii=False,indent=2))
