# Author: Knowledge Sense
"""Finite consistency checks for ordinary and restricted sumset constructions.
Requires Python 3.12 or later; standard library only.
Run: python verify_sumsets.py
"""
import itertools as it
import json
import math
from fractions import Fraction as Q
from pathlib import Path

H=8
counts={}
def checked(name): counts[name]=counts.get(name,0)+1
def add(a,b): return [a[i]+b[i] for i in range(H+1)]
def mul(a,b): return [sum(a[j]*b[i-j] for j in range(i+1)) for i in range(H+1)]
def power(a,n):
    r=[1]+[0]*H
    for _ in range(n): r=mul(r,a)
    return r
def shift(a,n): return [0]*n+a[:H+1-n]
def binpoly(n): return [math.comb(n,j) if j<=n else 0 for j in range(H+1)]
def free(n): return [math.comb(n+j-1,j) if n else int(j==0) for j in range(H+1)]
def subv(a,b): return [x-y for x,y in zip(a,b)]
def vecunit(n,i): return tuple(int(j==i) for j in range(n))
def vsum(ps,n): return tuple(sum(p[i] for p in ps) for i in range(n))
def rG(m,r):
    n=(2*m-1)*r
    ps=[]
    for t in range(r):
        start=t*(2*m-1)
        block=[vecunit(n,start+i) for i in range(2*m-1)]
        last=tuple(sum(p[i] for p in block[:m])-sum(p[i] for p in block[m:]) for i in range(n))
        ps+=block+[last]
    return ps,n
def rH(m,u):
    n=(m-1)*u+1
    ps=[]
    for t in range(u):
        bs=[vecunit(n,t*(m-1)+i) for i in range(m-1)]
        a=tuple(sum(p[i] for p in bs)-int(i==n-1) for i in range(n))
        ps+=bs+[a]
    return ps,n
def enum_restricted(ps,n):
    return [len({vsum(cs,n) for cs in it.combinations(ps,j)}) if j<=len(ps) else 0 for j in range(H+1)]
def rGF(m,r):
    p=binpoly(2*m);p[m]-=1
    return power(p,r)
def rHF(m,u):
    f=binpoly(m);f[1]-=1;f[m-1]-=1
    result=[0]*(H+1)
    for j in range(u+1):
        s=[0]*(H+1)
        for ell in range(j+1):
            deg=j+ell*(m-2)
            if deg<=H:s[deg]+=1
        term=mul(power(f,u-j),s)
        result=add(result,[math.comb(u,j)*a for a in term])
    return result
for m in range(2,6):
    for r in range(3):
        ps,n=rG(m,r)
        if len(ps)<=16:
            assert enum_restricted(ps,n)==rGF(m,r)
            checked('restricted_G_fibers')
    for u in range(1,4):
        ps,n=rH(m,u)
        assert enum_restricted(ps,n)==rHF(m,u)
        checked('restricted_H_fibers')
        diff=subv(mul(binpoly(m),rHF(m,u)),rHF(m,u+1))
        f=binpoly(m);f[1]-=1;f[m-1]-=1
        lower=[u*a for a in shift(power(f,u-1),m)]
        upper=[u*a for a in shift(binpoly(m*(u-1)),m)]
        assert all(0<=lo<=v<=up for lo,v,up in zip(lower,diff,upper))
        checked('restricted_positive_H_bounds')

def oF(m,u,zero):
    S=[1 if j<m else 0 for j in range(H+1)]
    if zero: return mul(power(S,u),free(u+1))
    numerator=subv(power(S,u),shift([1]+[0]*H,m-1))
    denom=[int(j%(m-1)==0) for j in range(H+1)]
    return mul(mul(numerator,free(u)),denom)
def enum_ordinary(ps,n):
    return [len({vsum(cs,n) for cs in it.combinations_with_replacement(ps,j)}) for j in range(H+1)]
for m in range(2,6):
    for u in range(1,4):
        ps=[vecunit(u,i) for i in range(u)]+[tuple(m*x for x in vecunit(u,i)) for i in range(u)]
        assert enum_ordinary(ps,u)==oF(m,u,False)
        assert enum_ordinary(ps+[(0,)*u],u)==oF(m,u,True)
        checked('ordinary_G_H_fibers')
        diff=subv(mul(oF(m,u,False),free(2)),oF(m,u+1,False))
        Sm=[int(j<m) for j in range(H+1)]
        total=[0]*(H+1)
        for j in range(u): total=add(total,power(Sm,j))
        physical=shift(mul(free(u+3),total),m+1)
        assert diff==physical and all(v>=0 for v in diff)
        assert all(v<=up for v,up in zip(diff,[u*x for x in shift(free(2*u+2),m+1)]))
        checked('ordinary_positive_H_identity')

def root(n,p):
    lo,hi=0,1
    while hi**p<=n:hi*=2
    while lo+1<hi:
        mid=(lo+hi)//2
        if mid**p<=n:lo=mid
        else:hi=mid
    return lo
def digit(h,q,D):
    B=q//(4*h);r=1
    while D>B**r:r+=1
    delta=B**(r-1)
    ls=[{j*B**i for j in range(B)} for i in range(r-1)]
    A=set(range(0,D+1,delta))|{D}
    for s in ls:A|=s|{D-x for x in s}
    assert len(A)<=q//2
    for a in range(D+1):
        if len(A)==q:break
        A.add(a)
    assert len(A)==q and set(range(q//2))<=A
    return A
def ordinary_bits(A,h):
    v=1
    for _ in range(h):
        w=0
        for a in A:w|=v<<a
        v=w
    return v
for h in range(2,9):
    for q in [8*h,16*h,32*h,64*h,128*h]:
        maxD=min(q**h//((8*h)**h),2000)
        if maxD<q-1:continue
        for D in sorted({q-1,(q-1+maxD)//2,maxD}):
            A=digit(h,q,D)
            assert ordinary_bits(A,h)==(1<<(h*D+1))-1
            checked('digit_filling')
            for i in range(1,h+1):
                C={0}|{a+i for a in A}
                expected=1|(((1<<(h*(i+D)+1))-1)^((1<<i)-1))
                assert ordinary_bits(C,h)==expected
                checked('ordinary_singleton_filling')

for b in range(2,12):
    previous=None
    for x in range(8*(b-2)+1,b-2,-1):
        A=list(range(b-1))+[x]
        current=[len({sum(s) for s in it.combinations(A,q)}) for q in range(9)]
        if previous is not None:assert all(0<=p-v<=1 for p,v in zip(previous,current))
        previous=current;checked('restricted_dense_positions')
for b in range(3,12):
    L=b-2
    for x in range(8*L+1,L,-1):
        A=list(range(L+1))+[x]
        for q in range(1,9):
            actual=set()
            for t in range(q+1):actual.update(range(t*x,t*x+(q-t)*L+1))
            assert len(actual)==1+sum(min(x,r*L+1) for r in range(1,q+1))
        checked('ordinary_dense_positions')

for h in range(2,201):
    k=(2*h)**80;c=root(k**7,10)
    assert c>=(32*h**3)**10
    assert c>=8*h**3 and c**6>=256**35 and c**3>=(128*h)**5
    R=root(c**9,10);T=root(c**4,5)
    used=sum(2*m*R+m*T for m in range(2,h+1))
    assert (used+2*h)*4*h<=c
    assert c**9>=8**10*c**8
    assert (8*T*(T-1))**5>=c**8
    ell=2*h-1
    epsilon=Q(ell,(64*ell*h)**h);eta=h*epsilon/2**(h+2)
    s=k-1;last=h*(epsilon*s**h//1)+h-(h-1)**2+1
    assert epsilon*s**(h-1)>=2 and last>=3*eta*k**h
    assert k**(3*(h-1))>(2*(1+2*h**3)/eta)**10
    oeps=Q(1,(8*h)**h);oeta=h*oeps/2**(h+3)
    Dmax=oeps*s**h//1
    assert Dmax-k>=h-2 and h*Dmax+1>=7*oeta*k**h
    assert k**(3*(h-1))>(20*h/oeta)**10
    checked('exact_threshold_h')

result={'status':'all assertions passed','counts':counts,'scope':'Finite consistency checks; the all-h statement rests on the algebraic inequalities in the manuscript.'}
dest=Path(__file__).with_name('verification_results.json')
dest.write_text(json.dumps(result,ensure_ascii=False,indent=2)+'\n',encoding='utf-8')
print(json.dumps(result,ensure_ascii=False,indent=2))
