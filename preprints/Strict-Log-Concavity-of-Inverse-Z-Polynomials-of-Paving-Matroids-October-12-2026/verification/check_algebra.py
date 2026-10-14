# Author: Knowledge Sense
# Exact-arithmetic checks for inverse Z-polynomials of paving matroids.
"""Exact arithmetic supplements to the mathematical audit. No floating point."""
if not __debug__:
    raise RuntimeError('Run Python without -O or -OO: these checks use assertions.')

from fractions import Fraction as F
from math import comb, factorial
from collections import defaultdict
from pathlib import Path
import json

def U(k,n):
    return [comb(n,j)*comb(n-j-1,n-k) for i in range(k+1) for j in [min(i,k-i)]]

def correction(k,h):
    c=U(k,h)
    if k%2==0:
        m=k//2
        d=F(4*h*factorial(h-1),(2*h-2*m)*(2*h-2*m+2)*factorial(m)*factorial(m-1)*factorial(h-2*m))
        assert d.denominator==1
        c[m]-=int(d)
    return c

def gaps(seq):
    return [seq[i]**2-seq[i-1]*seq[i+1] for i in range(1,len(seq)-1)]

# The multivariate ring Z[x,s,b] verifies the expansion in Lemma 6.2.
def add(*ps):
    d=defaultdict(int)
    for p in ps:
        for mon,c in p.items(): d[mon]+=c
    return {m:c for m,c in d.items() if c}
def scale(p,c): return {m:v*c for m,v in p.items() if v*c}
def mul(*ps):
    d={(0,0,0):1}
    for p in ps:
        e=defaultdict(int)
        for m,c in d.items():
            for n,v in p.items(): e[tuple(i+j for i,j in zip(m,n))]+=c*v
        d={m:c for m,c in e.items() if c}
    return d
one={(0,0,0):1}; x={(1,0,0):1}; s={(0,1,0):1}; b={(0,0,1):1}
a=add(s,x)
polyF=add(mul(s,add(mul(add(a,scale(b,2)),add(s,b)),mul(add(scale(b,2),one),a,add(a,b))),add(a,s,scale(b,2),one)),scale(mul(add(a,s,scale(one,-1)),add(a,b),add(s,b),add(a,scale(b,2),mul(add(scale(b,2),one),s))),-1))
f0=scale(mul(add(s,b),add(mul(add(b,one),s),b),add(scale(s,2),b)),2)
f3=mul(b,add(scale(s,2),scale(one,-1)))
f2=add(scale(mul(b,add(mul(s,s),scale(one,-1))),6),mul(add(scale(mul(b,b),4),scale(b,-2),scale(one,2)),add(s,scale(one,-1))),mul(b,b),scale(b,5),scale(one,2))
f1=add(scale(mul(b,add(mul(s,s,s),scale(one,-1))),4),mul(add(scale(mul(b,b),6),scale(b,2),scale(one,6)),add(mul(s,s),scale(one,-1))),mul(add(scale(mul(b,b,b),2),scale(mul(b,b),-2),scale(b,8)),add(s,scale(one,-1))),scale(mul(b,b),7),scale(b,14),scale(one,6))
assert polyF==add(f0,mul(x,f1),mul(x,x,f2),mul(x,x,x,f3))

counts={'uniform_normalization':0,'paving_formula_equivalence':0,'even_central_identity':0,'ratio_bounds':0,'single_hyperplane_matroids':0,'scalar_bounds':0}
for k in range(1,25):
    for n in range(k,k+41):
        u=U(k,n)
        assert min(u)>0 and u==u[::-1] and all(g>0 for g in gaps(u))
        B=comb(n,k-1)
        for i in range(k//2+1):
            assert F(u[i],B)==F(comb(k-1,i)*(n-k+1),n-i)
            counts['uniform_normalization']+=1
        if k==1: continue
        for h in range(k,n):
            c=correction(k,h)
            older=U(k,h+1)
            prev=U(k-1,h)
            older=[older[i]-(prev[i] if i<k else 0)-(prev[i-1] if i>0 else 0) for i in range(k+1)]
            assert c==older
            counts['paving_formula_equivalence']+=1
            matroid=[v-w for v,w in zip(u,c)]
            assert min(matroid)>0 and matroid==matroid[::-1] and all(g>0 for g in gaps(matroid))
            counts['single_hyperplane_matroids']+=1
            if k%2==0:
                m=k//2; C=comb(k-1,m); N=n-m; D=n-2*m+1
                delta=F(C*D,N*(N+1)); bh=comb(h,k-1)
                assert c[m]==c[m-1]
                assert F(matroid[m]-matroid[m-1],B)==delta
                counts['even_central_identity']+=1
                if m>=2:
                    p=F(matroid[m-1],B); q=F(matroid[m-2],B)
                    eta=F((m-1)*(N+1),m*(N+2))
                    assert q<eta*p
                    assert p>=F(C*m*D,(N+1)*(N+m+1))
                    assert (1-eta)*p-eta*delta>=F(C*D*D,m*N*(N+1)*(N+2))
            max_i=(k//2 if k%2 else k//2-1)
            for i in range(1,max_i+1):
                vi=F(u[i],B); vp=F(u[i-1],B)
                wi=vi-F(c[i],comb(h,k-1)); wp=vp-F(c[i-1],comb(h,k-1))
                lo=F((k-1-i)*(n-i+1),i*(n-i-1)); hi=F((k-i)*(n-i+1),i*(n-i))
                assert lo<=vi/vp<=hi and lo<=wi/wp<hi
                counts['ratio_bounds']+=1

for bb in range(1,15):
    for ss in range(1,20):
        for aa in range(ss,ss+25):
            val=F(ss,aa+2*bb+(2*bb+1)*ss)*(F(aa+2*bb,aa+bb)+F((2*bb+1)*aa,ss+bb))
            assert val>F(aa+ss-1,aa+ss+2*bb+1)
            counts['scalar_bounds']+=1

bad=[F(v,comb(8,3))-F(w,comb(7,3)) for v,w in zip(U(4,8),correction(4,7))]
assert gaps(bad)[0]==-F(5,784)
assert [v-w for v,w in zip(U(4,8),correction(4,7))]==[15,50,70,50,15]
result={'method':'exact rational arithmetic and full multivariate polynomial identity; finite checks supplement analytic proof','ranges':{'k':'1..24','n':'k..k+40','h':'k..n-1','scalar_b':'1..14','scalar_s':'1..19','scalar_a':'s..s+24'},'symbolic_F_identity':True,'checks':counts,'all_checks_passed':True,'forbidden_saturated_component':{'k':4,'n':8,'h':7,'penultimate_gap':str(gaps(bad)[0]),'actual_weight':'5/8','actual_matroid':'U(3,7) direct sum U(1,1)','actual_Y':[15,50,70,50,15]}}
Path(__file__).with_name('algebra_check_results.json').write_text(json.dumps(result,ensure_ascii=False,indent=2),encoding='utf-8')
print(json.dumps(result,ensure_ascii=False,indent=2))
