"""Knowledge Sense. Exact supplementary coefficient checks.
Finite checks supplement the general mathematical proof.
"""
from functools import lru_cache
from fractions import Fraction as F
from math import comb
import json,pathlib,time
start=time.perf_counter()
@lru_cache(None)
def gb(n,k,q):
    assert n>=0
    if k<0 or k>n:return 0
    if n==0:return 1
    return q**k*gb(n-1,k,q)+gb(n-1,k-1,q)
def bin2(n):return n*(n-1)//2
def types(r,s,q):
    return [(d,a,q**((s-a)*(d-a))*gb(s,a,q)*gb(r-s,d-a,q)) for d in range(1,r+1) for a in range(max(0,d-r+s),min(s,d-1)+1)]
def p(r,s,q):
    return [gb(s,k,q)-gb(s,r-k,q) for k in range((r+1)//2)] if r else [1]
@lru_cache(None)
def iq(r,s,q):
    if r==0:return (1,)
    ans=[0]*((r+1)//2)
    # P * signed Q = identity in the incidence algebra; all nonempty quotients are PG.
    for d,a,n in types(r,s,q):
        for k,v in enumerate(p(d,a,q)):
            ans[k]-=(-1)**d*n*v*q**bin2(r-d)
    return tuple(ans)
@lru_cache(None)
def mob(r,s,q):
    if r==0:return 1
    return -1-sum(n*mob(d,a,q) for d,a,n in types(r,s,q) if d<r)
def y_definition(r,s,q):
    ans=[0]*(r+1)
    ans[r]=(-1)**r*mob(r,s,q)
    for d,a,n in types(r,s,q):
        for k,v in enumerate(iq(d,a,q)):
            ans[r-d+k]+=n*q**bin2(r-d)*v
    return ans
def jr(r,q):return [gb(r,k,q)*q**(bin2(k)+bin2(r-k)) for k in range(r+1)]
def y_kernel(r,s,q):
    ans=jr(r,q)
    for h in range(1,s+1):
        for l in range(min(h,r-h)+1):
            scalar=(-1)**(h+l)*gb(s,h,q)*gb(r-h,l,q)
            shifts=[l] if l==h else [l,h]
            for shift in shifts:
                for k,v in enumerate(jr(r-h-l,q)):ans[k+shift]+=scalar*v
    return ans
def product(items):
    x=F(1)
    for t in items:x*=t
    return x
def expansion(r,s,q,k):
    z=F(1,q); c=r-s
    pp=[F(1)]
    for i in range(1,r+1):pp.append(pp[-1]*(1-z**i))
    return sum(((1-z**c)*z**(j*(c+j+1))*gb(s,j,z)*pp[r-j-1]/(pp[r]*pp[j])*product((1-z**(k-i))*(1-z**(r-k-i)) for i in range(1,j+1)) for j in range(s+1)),F(0))
families=0; entries=0; r41=0; min_example=[]
fields=[2,3,4,5,7,8,9,11,16,25]
for q in fields:
    for r in range(2,23):
        for s in range(1,r):
            y=y_definition(r,s,q); kernel=y_kernel(r,s,q)
            assert y==kernel,(q,r,s,'definition vs kernel')
            baseline=jr(r,q); row=[F(y[k],baseline[k]) for k in range(r+1)]
            assert y==y[::-1] and all(v>0 for v in y)
            for k in range(1,r):
                assert y[k]**2>y[k-1]*y[k+1],(q,r,s,k,'strict LC')
                assert 2*row[k]>=row[k-1]+row[k+1],(q,r,s,k,'F concavity')
                assert row[k]==expansion(r,s,q,k),(q,r,s,k,'positive expansion')
                entries+=1
            assert row[0]==product(1-F(1,q)**i for i in range(r-s,r)),(q,r,s,'endpoint')
            if s==1:
                expected=jr(r,q)
                for k,v in enumerate(jr(r-1,q)):
                    expected[k]-=v;expected[k+1]-=v
                for k,v in enumerate(jr(r-2,q)):expected[k+1]+=gb(r-1,1,q)*v
                assert y==expected,(q,r,'one-point')
                r41+=1
            if q in [2,3] and r<=4:min_example.append({'q':q,'r':r,'s':s,'Y':y,'F':[str(v) for v in row]})
            families+=1
result={'kind':'finite exact supplementary verification','fields':fields,'rank_range':[2,22],'s_range':'1..r-1','families':families,'internal_entries':entries,'one_point_checks':r41,'checks':['Y from P-inverse and Mobius definition equals full signed kernel','positive expansion equals independently derived coefficients','positive coefficients, symmetry, strict log-concavity','Gaussian-normalized discrete concavity including endpoints','one-point deletion identity'],'all_passed':True,'seconds':time.perf_counter()-start,'examples':min_example}
out=pathlib.Path(__file__).resolve().parent
(out/'exact_audit_results.json').write_text(json.dumps(result,ensure_ascii=False,indent=2),encoding='utf-8')
print(json.dumps({k:v for k,v in result.items() if k!='examples'},indent=2))
