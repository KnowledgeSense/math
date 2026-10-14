"""Multiplicity-five numerical semigroups: finite arithmetic and exact jet checks. Author: Knowledge Sense."""
import itertools,json,heapq
from collections import Counter
from fractions import Fraction
from pathlib import Path

def shortest(gs):
    w=[0]+[10**12]*4; heap=[(0,0)]
    while heap:
        n,r=heapq.heappop(heap)
        if n!=w[r]:continue
        for g in gs:
            v,s=n+g,(r+g)%5
            if v<w[s]:w[s]=v;heapq.heappush(heap,(v,s))
    return w

def first_relation(a,b):
    seen=set()
    best=10**12
    for y in range(6):
        for z in range(6):
            n=y*a+z*b
            for x in range((5*a-n)//5+1):
                s=n+5*x
                if s in seen:best=min(best,s)
                seen.add(s)
    return best

def product(p,q,L):
    r={}
    for i,a in p.items():
        for j,b in q.items():
            if i+j<L:r[i+j]=r.get(i+j,0)+a*b
    return {i:a for i,a in r.items() if a}

def pivots(a,b,Z,L):
    rows={};powers=[{0:1}]
    for q in range(1,(L-1)//b+1):powers.append(product(powers[-1],Z,L))
    for q,z in enumerate(powers):
        for p in range((L-1-q*b)//a+1):
            for x in range((L-1-q*b-p*a)//5+1):
                shift=5*x+p*a
                row={n+shift:Fraction(v) for n,v in z.items() if n+shift<L}
                while row:
                    h=min(row); f=row[h]
                    if h not in rows:rows[h]={n:v/f for n,v in row.items()};break
                    for n,v in rows[h].items():
                        row[n]=row.get(n,0)-f*v
                        if row[n]==0:del row[n]
    return set(rows)

def classify(gs):
    e=len(gs)
    if e==2:return 2,None
    if e==3:return 3,'e3'
    _,a,b,c,*rest=gs;i=a%5;k=b*pow(i,-1,5)%5;j=c*pow(i,-1,5)%5
    if e==4:
        if (k==2 and j in (3,4) and c>2*a) or (k==3 and j==4 and c>3*a) or (k==4 and j==3 and c>a+b):return 3,f'e4_k{k}_j{j}'
        return 4,None
    d=rest[0]
    if d<2*a:return 5,None
    if (k,j,d*pow(i,-1,5)%5)==(2,3,4) and c>2*a and d>a+b:return 3,'e5'
    return 4,None

ec=Counter();hc=Counter();bc=Counter();pairs={};witness={};jetcount=0
N=24
for ks in itertools.product(range(1,N+1),repeat=4):
    w=[0]+[5*k+r for r,k in enumerate(ks,1)]
    if any(w[i]+w[j]<w[(i+j)%5] for i in range(1,5) for j in range(i,5)):continue
    gs=[5]+sorted(w[r] for r in range(1,5) if all(w[i]+w[j]!=w[r] for i in range(1,5) for j in range(1,5)))
    assert shortest(gs)==w
    e=len(gs);ec[e]+=1;h,case=classify(gs);hc[h]+=1
    witness.setdefault(f'e{e}_h{h}',{'generators':gs,'apery':w})
    if e<3:continue
    _,a,b,*rest=gs;i=a%5;k=b*pow(i,-1,5)%5
    if (a,b) not in pairs:
        ap=shortest([5,a,b]);expected={2:[a,b,a+b,2*b],3:[a,2*a,b,a+b],4:[a,2*a,min(3*a,2*b),b]}[k]
        assert [ap[(i*r)%5] for r in range(1,5)]==expected
        beta={2:2*a,3:min(3*a,2*b),4:min(a+b,4*a)}[k]
        assert first_relation(a,b)==beta
        pairs[a,b]=beta
    if e==4:assert (h==3)==(rest[0]>pairs[a,b])
    if case is None:continue
    L=max(w)+1
    if e==3:Z={b:1}
    elif e==4:
        c=rest[0];j=c*pow(i,-1,5)%5
        delta=c-(2*a if k==2 else 3*a if k==3 else a+b)
        if (k,j)==(2,3):Z={n:1 for n in range(b,L,delta)}
        else:Z={b:1,b+delta:1}
    else:
        c,d=rest;delta=c-2*a;eps=d-a-b
        assert delta>0 and eps>0 and (2*a-b)%5==0 and (a+b-c)%5==0
        Z={n:1 for n in range(b,L,delta)}
        for n in range(b+delta+eps,L,delta):Z[n]=Z.get(n,0)+1
    actual=pivots(a,b,Z,L);expected={n for n in range(L) if n>=w[n%5]}
    assert actual==expected,(gs,sorted(actual-expected),sorted(expected-actual))
    bc[case]+=1;jetcount+=1;witness.setdefault(case,{'generators':gs,'apery':w,'cutoff':L})
result={'kunz_box':[1,N],'tuples_scanned':N**4,'valid_semigroups':sum(ec.values()),'embedding_dimension_counts':dict(ec),'dimension_by_criterion_counts':dict(hc),'apery_and_first_relation_pairs':len(pairs),'exact_rational_jet_checks':jetcount,'branch_counts':dict(bc),'witnesses':witness,'all_assertions_passed':True,'scope':'Finite computation supplements the general proof; excluded arbitrary analytic parametrizations are handled by the necessity proof, not this program.'}
Path(__file__).with_name('verification-result.json').write_bytes(json.dumps(result,ensure_ascii=False,indent=2).encode('utf-8'))
print(json.dumps(result,ensure_ascii=False,indent=2))
