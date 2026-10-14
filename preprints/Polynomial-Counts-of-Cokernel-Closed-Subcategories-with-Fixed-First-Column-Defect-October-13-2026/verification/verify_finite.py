"""Finite examples for fixed-defect enumeration. Author: Knowledge Sense."""
import itertools,functools,json,math,time
from pathlib import Path
start=time.perf_counter()
def point_rules(n):
    pts=[(a,b) for b in range(n+1) for a in range(b+1)]; ix={p:j for j,p in enumerate(pts)};rules={}
    for (a,b) in pts:
        eligible=[p for p in pts if a<=p[0]<=b<=p[1]]
        for (c,d),(e,f) in itertools.product(eligible,repeat=2):
            ant=sum(1<<ix[p] for p in {(a,b),(c,d),(e,f)})
            req=1<<ix[(max(c,e),max(d,f))]
            if b<min(d,f):req|=1<<ix[(b+1,min(d,f))]
            req&=~ant
            if req:rules[ant]=rules.get(ant,0)|req
    return pts,list(rules.items())
@functools.lru_cache(None)
def graph_rules(N):
    es=list(itertools.combinations(range(N),2));ix={e:j for j,e in enumerate(es)};rules={}
    for s,t in es:
        eligible=[(x,y) for x,y in es if s<=x<t<=y]
        for x,y in eligible:
            if t<y:
                ant=(1<<ix[(s,t)])|(1<<ix[(x,y)]);req=1<<ix[(t,y)]
                if req&~ant:rules[ant]=rules.get(ant,0)|(req&~ant)
        for (x,y),(z,w) in itertools.product(eligible,repeat=2):
            ant=(1<<ix[(s,t)])|(1<<ix[(x,y)])|(1<<ix[(z,w)])
            req=1<<ix[(max(x,z),max(y,w))]
            if req&~ant:rules[ant]=rules.get(ant,0)|(req&~ant)
    return ix,list(rules.items())
def valid(mask,rules):return all(mask&a!=a or mask&r==r for a,r in rules)
def encode(i,m,d,y,eps):
    order=[('r',0)]
    for t in range(m+1):
        order.extend(('a',j) for j in range(i) if d[j]==t)
        if t<m:order.append(('b',t+1))
    indices={v:j for j,v in enumerate(order)};ix,rules=graph_rules(len(order));mask=0
    def add(u,v):
        nonlocal mask
        mask|=1<<ix[tuple(sorted((indices[u],indices[v])))]
    for u,v in itertools.combinations([('r',0)]+[('b',t) for t in range(1,m+1)],2):add(u,v)
    for j in range(i):
        for t in range(y[j]+1,m+1):add(('a',j),('b',t))
    for bit,(j,k) in enumerate(itertools.combinations(range(i),2)):
        if eps&(1<<bit):add(('a',j),('a',k))
    return mask,rules
direct={}
for n in range(5):
    pts,pr=point_rules(n); counts=[0]*(n+2);column=sum(1<<j for j,p in enumerate(pts) if p[0]==0)
    ix,gr=graph_rules(n+2)
    for mask in range(1<<len(pts)):
        pv=valid(mask,pr)
        gm=sum(1<<ix[(a,b+1)] for j,(a,b) in enumerate(pts) if mask&(1<<j))
        assert pv==valid(gm,gr),(n,mask)
        if pv:counts[(mask&column).bit_count()]+=1
    direct[str(n)]=counts
    print('direct',n,counts,flush=True)
templates={}
for i in range(4):
    cs=[]
    for q in range(2*i+1):
        count=0
        for d in itertools.combinations_with_replacement(range(q+1),i):
            for y in itertools.product(range(q+1),repeat=i):
                if set(d+y)-{0}!=set(range(1,q+1)):continue
                for eps in range(1<<(i*(i-1)//2)):
                    mask,rules=encode(i,q,d,y,eps)
                    if valid(mask,rules):count+=1
        cs.append(count)
    assert cs[-1]==math.factorial(2*i)//math.factorial(i)
    templates[str(i)]=cs
    print('templates',i,cs,flush=True)
for n,counts in direct.items():
    n=int(n)
    for i in range(min(3,n+1)+1):
        m=n+1-i
        expected=sum(c*math.comb(m,q) for q,c in enumerate(templates[str(i)]) if q<=m)
        assert expected==counts[m],(n,i,expected,counts[m])
result={'direct_counts_by_k':direct,'template_coefficients':templates,'point_graph_equivalence':'all subsets n=0..4','template_vs_direct':'i=0..3 within n=0..4','elapsed_seconds':time.perf_counter()-start}
(Path(__file__).resolve().parent/'finite_verification.json').write_text(json.dumps(result,indent=2),encoding='utf-8')
print(json.dumps(result,indent=2))
