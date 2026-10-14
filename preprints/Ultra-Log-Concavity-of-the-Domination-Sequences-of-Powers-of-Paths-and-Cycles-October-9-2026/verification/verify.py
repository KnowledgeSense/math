"""Exact finite diagnostics for domination counts and bounded compositions."""
from pathlib import Path
from math import comb
from fractions import Fraction
from collections import Counter
from functools import lru_cache
import json,time,hashlib

C=Counter();start=time.perf_counter()
def check(ok,kind,detail=None):
    C[kind]+=1
    if not ok:raise AssertionError((kind,detail))
def ulc(seq,order,kind):
    for k in range(1,order):
        check(seq[k]**2*comb(order,k-1)*comb(order,k+1)>=seq[k-1]*seq[k+1]*comb(order,k)**2,kind,(order,k,seq))
    support=[k for k,x in enumerate(seq) if x]
    check(support==list(range(support[0],support[-1]+1)),'no_internal_zero')
def poly_mul(a,b,N):
    out=[0]*(N+1)
    for i,x in enumerate(a):
        if not x:continue
        for j,y in enumerate(b[:N-i+1]):
            if y:out[i+j]+=x*y
    return out
def bounded_counts(v,q,m):
    base=poly_mul([0]+[1]*min(q,v+1),[0]+[1]*min(q,v+1),v+1)
    out=[0]
    for k in range(1,v+1):
        out.append(base[v+1]);base=poly_mul(base,[0]+[1]*min(m,v+1),v+1)
    return out
def cycle_counts(v,m):
    p=[1]+[0]*v;out=[0]
    for k in range(1,v+1):
        p=poly_mul(p,[0]+[1]*min(m,v),v)
        check(v*p[v]%k==0,'cycle_integrality')
        out.append(v*p[v]//k)
    return out
def graph_counts(v,ell,cycle):
    full=(1<<v)-1;closed=[]
    for i in range(v):
        closed.append(sum(1<<j for j in range(v) if (min(abs(i-j),v-abs(i-j)) if cycle else abs(i-j))<=ell))
    covered=[0]*(1<<v);counts=[0]*(v+1)
    for s in range(1,1<<v):
        low=s&-s;covered[s]=covered[s^low]|closed[low.bit_length()-1]
    for s,x in enumerate(covered):
        if x==full:counts[s.bit_count()]+=1
    return counts
graph_cases=0;examples=[]
for v in range(17):
    for ell in range(1,v+3):
        for cycle in (False,True):
            exact=graph_counts(v,ell,cycle)
            formula=([1] if v==0 else cycle_counts(v,2*ell+1) if cycle else bounded_counts(v,ell+1,2*ell+1))
            check(exact==formula,'direct_graph_vs_formula',(v,ell,cycle));ulc(exact,v,'graph_ulc');graph_cases+=1
            if (v,ell,cycle) in [(0,1,False),(2,1,True),(5,1,False),(8,1,True),(12,2,False)]:examples.append({'n':v,'ell':ell,'cycle':cycle,'counts':exact})

general_cases=0
for v in range(1,11):
    for q in range(1,9):
        for m in range(q,13):
            exact=[0]*(v+1)
            for mask in range(1,1<<v):
                selected=[i+1 for i in range(v) if mask>>i&1]
                gaps=[selected[0]]+[b-a for a,b in zip(selected,selected[1:])]+[v+1-selected[-1]]
                if gaps[0]<=q and gaps[-1]<=q and max(gaps[1:-1],default=0)<=m:exact[len(selected)]+=1
            check(exact==bounded_counts(v,q,m),'generalized_family_vs_formula',(v,q,m));ulc(exact,v,'generalized_family_ulc');general_cases+=1

def compositions_avoiding_ones(n,t):
    # DP builds the actual positive parts; last index records the final run of 1s.
    dp=[[[0]*t for k in range(n+1)] for total in range(n+1)];dp[0][0][0]=1
    for total in range(n):
        for k in range(total+1):
            for run,ways in enumerate(dp[total][k]):
                if not ways:continue
                if run+1<t:dp[total+1][k+1][run+1]+=ways
                for part in range(2,n-total+1):dp[total+part][k+1][0]+=ways
    return [sum(dp[n][k]) for k in range(n+1)]
composition_cases=0
for n in range(1,51):
    for t in range(2,10):
        actual=compositions_avoiding_ones(n,t)
        if n<t: predicted=[0]+[comb(n-1,k-1) for k in range(1,n+1)]
        else:
            d=bounded_counts(n-1,t,t+1)
            predicted=[0]+[d[n-k] for k in range(1,n+1)]
        check(actual==predicted,'composition_bijection',(n,t))
        a=[Fraction(actual[k],comb(n-1,k-1)) for k in range(1,n+1)]
        for k in range(1,len(a)-1):check(a[k]**2>=a[k-1]*a[k+1],'composition_normalized_lc',(n,t,k))
        check(all(actual[k]**2>=actual[k-1]*actual[k+1] for k in range(1,n)),'composition_ordinary_lc',(n,t))
        composition_cases+=1

result={'graph_range':'0 <= n <= 16; 1 <= ell <= n+2; paths and cycles','graph_cases':graph_cases,'generalized_range':'1 <= v <= 10; 1 <= q <= 8; q <= m <= 12','generalized_cases':general_cases,'restricted_composition_range':'1 <= n <= 50; 2 <= t <= 9','restricted_composition_cases':composition_cases,'checks':dict(C),'assertions':sum(C.values()),'examples':examples,'seconds':time.perf_counter()-start,'verdict':'PASS','scope':'Finite diagnostics for counting identities, supports and coefficient inequalities.'}
Path('results.json').write_text(json.dumps(result,ensure_ascii=False,indent=2)+'\n',encoding='utf-8')
print(json.dumps(result,ensure_ascii=False,indent=2))
