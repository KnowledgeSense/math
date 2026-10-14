#!/usr/bin/env python3
"""Finite diagnostics for checking and update costs in multi-marked local search.
Author: Knowledge Sense. These checks supplement the mathematical proof.
Python 3 standard library only. Run from any working directory.
"""
from fractions import Fraction as F
from itertools import product
from pathlib import Path
from collections import Counter, defaultdict
import json, hashlib, sys

ROOT=Path(__file__).resolve().parent
checks={}

def marked(N,L,D,A):
    return {x for x in range(N) if (x-A)%N < D or (x-A)%L==0}

def gaps(N,M):
    v=sorted(M)
    return [(v[(i+1)%len(v)]-x)%N or N for i,x in enumerate(v)]

def solve(A,b):
    """Exact Gaussian elimination, independent of cycle gap formula."""
    n=len(b); a=[list(map(F,row))+[F(y)] for row,y in zip(A,b)]
    for j in range(n):
        z=next(i for i in range(j,n) if a[i][j]);a[j],a[z]=a[z],a[j]
        d=a[j][j];a[j]=[x/d for x in a[j]]
        for i in range(n):
            if i!=j and a[i][j]:
                d=a[i][j];a[i]=[x-d*y for x,y in zip(a[i],a[j])]
    return [row[-1] for row in a]

def poisson(N,M):
    u=[x for x in range(N) if x not in M]; idx={x:i for i,x in enumerate(u)}
    a=[[F(0) for _ in u] for _ in u]
    for x in u:
        i=idx[x];a[i][i]=F(1,2)
        for y in ((x-1)%N,(x+1)%N):
            if y in idx:a[i][idx[y]]-=F(1,4)
    h=solve(a,[1]*len(u)) if u else []
    return sum(h,F(0))/N

# Full rational Poisson check for every nonempty marked subset on cycles 3..8.
counts=0
for N in range(3,9):
    for mask in range(1,1<<N):
        M={x for x in range(N) if mask>>x&1}
        h=poisson(N,M);g=F(sum(t**3-t for t in gaps(N,M)),3*N)
        assert h==g,(N,mask,h,g)
        counts+=1
checks['all_cycle_marksets_exact_poisson']={'N_min':3,'N_max':8,'cases':counts,'passed':True}

# Actual asymptotic family, all translates for k=2; selected boundary/wrap translates for k=3,4,5.
rows=[]
for k in (2,3,4,5):
    L=k*k;N=k**8;D=k**7
    As=range(N) if k==2 else sorted({0,1,L-1,L,D-1,D,D+1,N-L,N-2,N-1})
    for A in As:
        M=marked(N,L,D,A); gs=gaps(N,M)
        eps=F(1,k)+F(1,k*k)-F(1,k**3)
        H=F(k-1,k)*F(L*L-1,3)
        assert F(len(M),N)==eps
        assert Counter(gs)==Counter({1:D,L:(N-D)//L})
        assert F(sum(g*g*g-g for g in gs),3*N)==H
        # Verify the pointwise Poisson equation using distances to neighboring marks.
        hs={x:0 for x in M}
        sm=sorted(M)
        for i,x in enumerate(sm):
            g=(sm[(i+1)%len(sm)]-x)%N or N
            for t in range(1,g):hs[(x+t)%N]=2*t*(g-t)
        for x in range(N):
            if x not in M:
                assert 4*hs[x]==4+2*hs[x]+hs[(x-1)%N]+hs[(x+1)%N]
        assert F(sum(hs.values()),N)==H
    rows.append({'k':k,'L':L,'N':N,'D':D,'translates_checked':len(As),'epsilon':str(eps),'H':str(H)})
checks['actual_family_mass_gaps_poisson']=rows

# Exhaustive cyclic interval/arc counting, including wrap and full-cycle arcs.
arc_cases=0
for N in range(3,22):
    for D in range(1,N+1):
        for s in range(1,N+1):
            V=set(range(s))
            actual=sum(bool(V & {(A+i)%N for i in range(D)}) for A in range(N))
            assert actual==min(N,D+s-1)
            arc_cases+=1
checks['cyclic_arc_counts']={'cases':arc_cases,'passed':True}

# Exhaustive restoration reachable-set invariant on small cycles for 2 setup roots.
restoration_states=0
for N in range(3,11):
  for root2 in range(N):
    sets={frozenset((0,root2))}
    for T in range(6):
      for V in sets:
        r=0 if len(V)==N else sum(x in V and (x-1)%N not in V for x in range(N))
        assert len(V)<=T+2 and r<=2
        for D in range(1,N):
          count=sum(any((x-A)%N<D for x in V) for A in range(N))
          assert count<=min(N,2*D+T)
        restoration_states+=1
      sets={frozenset(set(V)|{(x+d)%N}) for V in sets for x in V for d in (-1,0,1)}
checks['restoration_connected_range']={'states':restoration_states,'max_updates':5,'setup_cap':2,'passed':True}

# Exact adaptive coupling paths. Generalized toy cycles avoid small-k vacuity.
# Policies inspect labels/history, may restore to visited vertices, stop early,
# and make an arbitrary unvisited final guess. Every real oracle branch is rerun.
def policy(N,inc,start,seed,restoration,oracle):
    current=start;visited={start};queries=[];positive=False;updates=0
    for t in range(len(inc)+1):
        # Check timing and stored-state selection depend on negative history and labels.
        qpoint=sorted(visited)[(seed+len(queries)+current)%len(visited)]
        if len(queries)<3 and ((t+current+seed)%3!=1 or t==len(inc)):
            queries.append(qpoint)
            if oracle(qpoint):return visited,queries,qpoint,updates,True
        if t==len(inc) or (t>0 and (seed+current+len(queries))%13==0):break
        if restoration:
            current=sorted(visited)[(seed+t+len(queries))%len(visited)]
        current=(current+inc[t])%N;visited.add(current);updates+=1
    return visited,queries,(current*7+seed+len(queries)*3+5)%N,updates,positive

adaptive_count=0;adaptive_results=[]
for N,L,D in ((16,4,4),(18,3,6)):
  Msets=[marked(N,L,D,A) for A in range(N)]
  eps=F(len(Msets[0]),N)
  for restoration in (False,True):
    total_w=F(0);succ_w=F(0);bound_w=F(0)
    for inc in product((-1,0,1),repeat=4):
      w=F(1,4)**sum(z!=0 for z in inc)*F(1,2)**sum(z==0 for z in inc)
      for start in range(N):
       for seed in range(3):
        V,Q,y,T,_=policy(N,inc,start,seed,restoration,lambda x:False)
        hit=sum(bool(set(Q)&M) for M in Msets)
        poscount=0;succcount=0
        for A,M in enumerate(Msets):
          rv,rq,ry,rt,rp=policy(N,inc,start,seed,restoration,lambda x,M=M:x in M)
          assert rp==bool(set(Q)&M)
          if not rp:assert (rv,rq,ry,rt)==(V,Q,y,T)
          assert (ry in M) <= bool((set(Q)|{y})&M)
          poscount+=rp;succcount+=ry in M;adaptive_count+=1
        grid=len({q%L for q in Q})
        assert F(poscount,N)<=F(min(len(Q),T+1),L)+F(D+T,N)
        assert F(succcount,N)<=F(len(Q)+1)*eps
        assert F(succcount,N)<=F(grid,L)+F(D+T,N)+eps
        total_w+=w;succ_w+=w*F(succcount,N)
        bound_w+=w*(F(grid,L)+F(D+T,N)+eps)
    adaptive_results.append({'N':N,'L':L,'D':D,'restoration':restoration,'exact_average_success':str(succ_w/total_w),'exact_average_path_bound':str(bound_w/total_w)})
checks['adaptive_all_negative_coupling']={'oracle_runs':adaptive_count,'increment_horizon':4,'results':adaptive_results,'passed':True}

# Lazy range process enumerated exactly, comparing a squared Doob upper bound.
dist={(0,0,0):F(1)};range_rows=[]
for T in range(21):
    er=sum((hi-lo+1)*p for (x,lo,hi),p in dist.items())
    em2=sum(max(abs(lo),abs(hi))**2*p for (x,lo,hi),p in dist.items())
    assert em2<=2*T if T else em2==0
    assert (er-1)**2<=8*T if T else er==1
    range_rows.append({'T':T,'E_range_plus_one':str(er),'E_max_abs_squared':str(em2)})
    nxt=defaultdict(F)
    for (x,lo,hi),p in dist.items():
      for d,w in ((-1,F(1,4)),(0,F(1,2)),(1,F(1,4))):
        z=x+d;nxt[z,min(lo,z),max(hi,z)]+=p*w
    dist=nxt
checks['Doob_range_exact']=range_rows

# Lazy exit means solved as independent linear equations.
exit_rows=[]
for r in range(1,13):
    xs=list(range(-r+1,r));n=len(xs);A=[[F(0)]*n for _ in xs]
    for i,x in enumerate(xs):
      A[i][i]=F(1,2)
      if i:A[i][i-1]=F(-1,4)
      if i+1<n:A[i][i+1]=F(-1,4)
    h=solve(A,[1]*n)
    assert h[r-1]==2*r*r
    exit_rows.append({'radius':r,'E_exit_at_zero':str(h[r-1])})
checks['lazy_exit_exact']=exit_rows

# Every D-interval contains precisely one vertex of the D-spaced net.
net_cases=0
for N in range(2,65):
  for D in range(1,N+1):
    if N%D:continue
    net=set(range(0,N,D))
    for A in range(N):
      assert len(net&{(A+i)%N for i in range(D)})==1;net_cases+=1
checks['net_interval_cover']={'cases':net_cases,'passed':True}

out={'kind':'finite independent diagnostics; not a proof or novelty review','python':sys.version,'checks':checks,'all_passed':True}
path=ROOT/'results.json';path.write_text(json.dumps(out,indent=2)+'\n')
print(json.dumps({'all_passed':True,'actual_family_rows':rows,'adaptive_oracle_runs':adaptive_count,'poisson_marksets':counts,'results_file':path.name},indent=2))
