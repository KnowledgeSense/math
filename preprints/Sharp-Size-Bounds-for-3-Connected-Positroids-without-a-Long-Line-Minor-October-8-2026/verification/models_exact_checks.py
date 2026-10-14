"""Independent exact matroid-oracle diagnostics; no numerical representation."""
from functools import lru_cache
from itertools import combinations
import json, random, pathlib, hashlib

ROOT=pathlib.Path(__file__).resolve().parent

def construct(kind,r,t=2,C=None,paths=None,order=None):
    if kind=='G':
        junctions=[f'v{i}' for i in range(r)]
        edges=[(i,(i+1)%r) for i in range(r)]
        def jr(mask):return mask.bit_count()
    elif kind=='A':
        junctions=[f'v{i}' for i in range(r+1)]
        edges=[(i,i+1) for i in range(r)]
        cm=sum(1<<i for i in C)
        def jr(mask):return mask.bit_count()-int((mask&cm)==cm)
    else:
        junctions=[]; edges=[]; starts=[]; ends=[]
        for k,length in enumerate(paths):
            start=len(junctions); starts.append(start)
            junctions.extend(f'p{k}v{i}' for i in range(length+1))
            ends.append(len(junctions)-1)
            edges.extend((start+i,start+i+1) for i in range(length))
        classes=[(ends[i],starts[(i+1)%3]) for i in range(3)]
        cms=[sum(1<<i for i in pair) for pair in classes]
        jm=(1<<len(junctions))-1
        def jr(mask):
            dual_rank=min(2,sum(bool((jm^mask)&c) for c in cms))
            return mask.bit_count()+dual_rank-2
    m=len(junctions)
    extensions=[]; names=list(junctions)
    for ei,(a,b) in enumerate(edges):
        for j in range(t-1):
            index=len(names); names.append(f'e{ei}f{j}')
            extensions.append((index,(1<<a)|(1<<b)))
    oracle=lru_cache(None)(jr)
    if order is None:order=list(range(len(extensions)))
    for e in order:
        index,support=extensions[e]; bit=1<<index
        prior=oracle
        @lru_cache(None)
        def new(mask,prior=prior,bit=bit,support=support):
            if not mask&bit:return prior(mask)
            oldmask=mask^bit
            oldrank=prior(oldmask)
            return oldrank+int(prior(oldmask|support)>oldrank)
        oracle=new
    return names,edges,extensions,oracle

def diagnostic(kind,r,t=2,C=None,paths=None):
    names,edges,extensions,rank=construct(kind,r,t,C,paths)
    n=len(names); full=(1<<n)-1; ranks=[rank(x) for x in range(full+1)]
    assert ranks[full]==r
    # all point and pair ranks; every possible separation, exactly.
    assert all(ranks[1<<i]==1 for i in range(n))
    assert all(ranks[(1<<i)|(1<<j)]==2 for i,j in combinations(range(n),2))
    violations=[]; minlambda=99
    for mask in range(1,full):
        value=ranks[mask]+ranks[full^mask]-r
        if 2<=mask.bit_count()<=n-2:minlambda=min(minlambda,value)
        if value<1 or (2<=mask.bit_count()<=n-2 and value<2):violations.append(mask)
    # all long-line flats, and all global free-point tests.
    lines=set()
    for i,j in combinations(range(n),2):
        pair=(1<<i)|(1<<j)
        flat=sum(1<<k for k in range(n) if ranks[pair|(1<<k)]==2)
        if flat.bit_count()>=3:lines.add(flat)
    free_failures=[]
    for index,support in extensions:
        bit=1<<index
        for mask in range(full+1):
            if not mask&bit and ranks[mask|bit]==ranks[mask] and ranks[mask|support]>ranks[mask]:
                free_failures.append([names[index],mask]);break
    # Every independent contraction of rank r-2; retaining all possible points
    # gives the largest simple rank-two restriction for that contraction.
    q=0; q_contract=None; contraction_sizes={}
    for cs in combinations(range(n),r-2):
        cm=sum(1<<i for i in cs)
        if ranks[cm]!=r-2:continue
        reps=[]
        for i in range(n):
            bit=1<<i
            if cm&bit or ranks[cm|bit]==r-2:continue
            if not any(ranks[cm|bit|(1<<j)]==r-1 for j in reps):reps.append(i)
        if len(reps)>q:q=len(reps);q_contract=cs
    # Independence of extension order, equality on all labeled subset ranks.
    reordered=[]
    for order in [list(reversed(range(len(extensions)))),random.Random(704).sample(range(len(extensions)),len(extensions))]:
        _,_,_,other=construct(kind,r,t,C,paths,order)
        differences=[mask for mask in range(full+1) if other(mask)!=ranks[mask]]
        reordered.append(len(differences))
    # Lemma D exhaustive weak inequalities for every junction on every free line.
    weak_failures=[]
    for index,support in extensions:
        fbit=1<<index
        flat=sum(1<<k for k in range(n) if ranks[support|(1<<k)]==2)
        for v in range(n):
            vbit=1<<v
            if v==index or not flat&vbit:continue
            for mask in range(full+1):
                if mask&fbit:continue
                relabeled=(mask^vbit)|fbit if mask&vbit else mask
                rf=ranks[mask|fbit]-1
                rv=ranks[relabeled|vbit]-1
                if rv>rf:weak_failures.append([names[index],names[v],mask]);break
    return dict(kind=kind,r=r,t=t,C=C,paths=paths,n=n,three_connected=not violations,
                minimum_nontrivial_lambda=minlambda,q=q,q_contraction=[names[i] for i in q_contract],
                long_lines=[[names[i] for i in range(n) if line&(1<<i)] for line in sorted(lines)],
                free_failures=free_failures,extension_order_rank_differences=reordered,
                weak_image_failures=weak_failures,rank_table_sha256=hashlib.sha256(bytes(ranks)).hexdigest())

cases=[]
for r,t in [(3,2),(3,3),(3,4),(4,2),(4,3),(5,2)]:cases.append(('G',r,t,None,None))
for r,t in [(2,2),(2,3),(3,2),(3,3),(4,2),(4,3),(5,2)]:
    for size in range(1,r):
        for inside in combinations(range(1,r),size):cases.append(('A',r,t,[0,*inside,r],None))
for paths in [(1,1,1),(1,1,2),(1,2,1),(2,1,1),(1,1,3),(1,2,2),(2,2,1)]:
    cases.append(('B',sum(paths)+1,2,None,list(paths)))
if __name__=='__main__':
    results=[]
    for case in cases:
        value=diagnostic(*case);results.append(value)
        expected=2*case[2]+int(case[0]!='G')
        assert value['three_connected'] and value['q']==expected and not value['free_failures'] and not any(value['extension_order_rank_differences']) and not value['weak_image_failures'],value
        print(f"{value['kind']} r={value['r']} t={value['t']} C={value['C']} paths={value['paths']}: n={value['n']}, q={value['q']}, PASS",flush=True)
    (ROOT/'models-exact-checks.json').write_text(json.dumps(results,indent=2),encoding='utf-8')
    print(f'{len(results)} exact model diagnostics passed',flush=True)
