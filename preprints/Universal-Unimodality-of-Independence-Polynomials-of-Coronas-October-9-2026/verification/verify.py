"""Finite exact-arithmetic diagnostics for corona independence polynomials.
Finite checks are error controls, not the proof of the infinite theorem.
"""
from fractions import Fraction as F
from math import ceil
from itertools import combinations
from functools import lru_cache
import json,subprocess,sys

def graphs(n):
    pairs=list(combinations(range(n),2))
    for code in range(1<<len(pairs)):
        adj=[0]*n
        for k,(i,j) in enumerate(pairs):
            if code>>k&1:
                adj[i]|=1<<j;adj[j]|=1<<i
        yield tuple(adj)

def plus(a,b):
    return tuple((a[k] if k<len(a) else 0)+(b[k] if k<len(b) else 0) for k in range(max(len(a),len(b))))

def times(a,b):
    out=[0]*(len(a)+len(b)-1)
    for i,x in enumerate(a):
        for j,y in enumerate(b):out[i+j]+=x*y
    return tuple(out)

def power(a,k):
    out=(1,)
    while k:
        if k&1:out=times(out,a)
        k>>=1
        if k:a=times(a,a)
    return out

def ip(adj):
    @lru_cache(None)
    def count(mask):
        if not mask:return (1,)
        v=max((v for v in range(len(adj)) if mask>>v&1), key=lambda v:(adj[v]&mask).bit_count())
        rest=mask&~(1<<v)
        return plus(count(rest),(0,)+count(rest&~adj[v]))
    return count((1<<len(adj))-1)

def corona(g,h):
    n,r=len(g),len(h);a=list(g)+( [0]*(n*r))
    for v in range(n):
        off=n+v*r
        for u in range(r):
            a[v]|=1<<(off+u)
            a[off+u]=(h[u]<<off)|(1<<v)
    return tuple(a)

def transform(gp,h,n):
    out=(0,)
    for j,coeff in enumerate(gp):out=plus(out,(0,)*j+tuple(coeff*x for x in power(h,n-j)))
    return out

def shape(p):
    downward=False
    for a,b in zip(p,p[1:]):
        if b<a:downward=True
        if downward and b>a:return False
    return True

def threshold(h):
    q=sum(h);mu=sum(j*x for j,x in enumerate(h))/q
    if mu==1:return None
    D=max(1,len(h)-1);delta= q/((q+1)*(q+2)**2);c=abs(1-mu)*delta/2
    terms=[F(1),2/((q+1)*delta),3/c,64*D**2/c**2,4/c,(576*D**3/c**2)**2,256*D**2*q**2]
    M=1+ceil(max(terms));assert all(M>t for t in terms)
    # All sqrt inequalities are checked via equivalent rational inequalities.
    assert c*M/2>F(3,2)
    assert 4*D**2*M<(c*M/4)**2 and 1<c*M/4
    assert (576*D**3/c**2)**2 < M # square of final valley bound
    assert M>(16*D*q)**2
    return M

classifications=0;polyset=set();threshold_count=0
for n in range(6):
    for g in graphs(n):
        p=ip(g);polyset.add(p);q=sum(p);der=sum(j*x for j,x in enumerate(p))
        nonedges=n*(n-1)//2-sum(v.bit_count() for v in g)//2
        assert (der==q)==(nonedges==1)
        classifications+=1

bases=[g for n in range(5) for g in graphs(n)]
attachments=[h for n in range(4) for h in graphs(n)]
direct=positive=0
for g in bases:
    gp=ip(g)
    for h in attachments:
        assert ip(corona(g,h))==transform(gp,ip(h),len(g));direct+=1
    for r in range(2,7):
        p=transform(gp,(1,r,1),len(g));assert p==p[::-1] and shape(p);positive+=1

thresholds=[];algebra=0
for p in sorted(polyset,key=lambda x:(sum(x),x)):
    h=tuple(map(F,p));r=p[1] if len(p)>1 else 0;lam=F(1,r+1)
    ht=tuple(c*lam**(j-1) for j,c in enumerate(h));q=sum(ht)
    mu=sum(j*c for j,c in enumerate(ht))/q
    assert q>=1 and mu<=r*lam<1
    for f in (h,ht):
        M=threshold(f)
        if M is not None:thresholds.append(str(M));threshold_count+=1
    for a,m in [(1,1),(2,1),(3,2),(8,5)]:
        N=a+2*m
        def abc(f):
            A=times(power(f,2*m),power(plus(f,(0,1)),a))
            B=times(power(f,a+m),power(plus(f,(0,2)),m))
            C=power(f,N)
            return plus(plus(A,B),tuple(-x for x in C))
        original=abc(h);tilted=abc(ht)
        assert tuple(x*lam**N for x in tilted)==tuple(x*lam**j for j,x in enumerate(original))
        assert min(original)>=0 and min(tilted)>=0
        algebra+=1

balance=0
for q in map(F,[1,F(5,4),F(3,2),2,F(7,3),5,100,10**6]):
    u=1+1/q;v=1+2/q
    for m in range(1,31):
        a=m
        while u**(a+1)<=v**m:a+=1
        assert m<=a<2*m and u**a<=v**m<u**(a+1)
        assert F(1,2)<=u**a/v**m<=1 and u**a/v**m>1/u
        balance+=1
print(json.dumps({'status':'PASS','labeled_graphs_through_order_5':classifications,'distinct_attachment_polynomials':len(polyset),
 'direct_corona_recurrence_cases':direct,'positive_direction_cases':positive,
 'exact_rational_threshold_cases':threshold_count,'exact_tilt_identity_cases':algebra,
 'rational_exact_balancing_cases':balance,'smallest_tested_sufficient_M':str(min(map(int,thresholds))),
 'largest_tested_sufficient_M':str(max(map(int,thresholds))),
 'scope':'Independent finite diagnostics only; analytic reconstruction establishes all finite H.'},indent=2))
