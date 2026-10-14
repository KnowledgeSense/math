"""Supplementary finite exact checks for fan inverse-Z log-concavity.
Author: Knowledge Sense; math@knowledgesense.jp.
The all-rank proof is analytic.

Run: python -X utf8 verification.py
Only standard Python libraries are required. No floating point arithmetic is used.
"""
from datetime import datetime, timezone
from fractions import Fraction as F
from functools import lru_cache
from math import comb
from pathlib import Path
import json

def add(p,q):
    return [p[i] if i<len(p) else 0 for i in range(max(len(p),len(q)))] if not q else [
        (p[i] if i<len(p) else 0)+(q[i] if i<len(q) else 0)
        for i in range(max(len(p),len(q)))]

def scale(p,c):
    return [c*x for x in p]

def sub(p,q):
    return add(p,scale(q,-1))

def mul(p,q):
    r=[F(0)]*(len(p)+len(q)-1)
    for i,a in enumerate(p):
        for j,b in enumerate(q):
            r[i+j]+=a*b
    return r

def der(p):
    return [i*p[i] for i in range(1,len(p))] or [F(0)]

def padded(p,n):
    return (p+[0]*n)[:n]

def dpoly(a,b):
    return [F(comb(a,l)*comb(b,l)) for l in range(min(a,b)+1)]

@lru_cache(None)
def D(a,b,z):
    if min(a,b)<0:
        return F(0)
    return sum((F(comb(a,l)*comb(b,l))*z**l for l in range(min(a,b)+1)),F(0))

def G(N,k,z):
    if k<0 or k>N:
        return [F(0)]
    return [D(k-r,N-k-r,z) for r in range(min(k,N-k)+1)]

def positive_formula(n,k):
    return F(2**(n-1))*sum((
        F((n-2*r)*comb(n,r),n*4**r)*D(k-r,n-k-r,F(1,2))
        for r in range((n-1)//2+1)),F(0))

def recurrence_rows(limit):
    # Gao--Li--Li v2, equation (68), derived by inverse deletion.
    ys=[[F(1)],[F(1),F(1)]]
    for n in range(2,limit+1):
        row=mul([F(2),F(2)],ys[n-1])
        for j in range((n-2)//2+1):
            cat=comb(2*j,j)//(j+1)
            row=sub(row,[F(0)]*(j+1)+scale(ys[n-2*j-2],cat))
        ys.append(padded(row,n+1))
    return ys

def main():
    counts={'fan_ranks':0,'fan_coefficients_compared':0,'fan_internal_inequalities':0,
            'kernel_lower_half_pairs':0,'kernel_coefficient_comparisons':0,
            'kernel_central_pairs':0,'ratio_polynomial_identities':0}
    ys=recurrence_rows(80)
    for n in range(1,81):
        row=ys[n]
        counts['fan_ranks']+=1
        for k in range(n+1):
            assert row[k]==positive_formula(n,k),(n,k,'formula mismatch')
            assert row[k]>0 and row[k]==row[n-k]
            counts['fan_coefficients_compared']+=1
        for k in range(1,n):
            assert row[k]**2>row[k-1]*row[k+1],(n,k,'Turan failed')
            counts['fan_internal_inequalities']+=1
    assert ys[1]==[1,1] and ys[2]==[2,3,2] and ys[3]==[4,9,9,4]
    zvalues=[F(1,7),F(1,2),F(1),F(2),F(10)]
    for z in zvalues:
        for N in range(4,33):
            for k in range(1,N//2):
                p=sub(mul(G(N,k,z),G(N,k,z)),mul(G(N,k-1,z),G(N,k+1,z)))
                p=padded(p,2*k+1)
                assert all(v>0 for v in p[:k+1]),(N,k,z,'positive coefficients failed')
                assert all(v==0 for v in p[k+1:]),(N,k,z,'degree failed')
                counts['kernel_lower_half_pairs']+=1
                counts['kernel_coefficient_comparisons']+=len(p)
        for N in range(2,33):
            for k in sorted({N//2,(N+1)//2}):
                p=sub(mul(G(N,k,z),G(N,k,z)),mul(G(N,k-1,z),G(N,k+1,z)))
                assert p[0]>0 and all(v>=0 for v in p),(N,k,z,'center failed')
                counts['kernel_central_pairs']+=1
    # Verify equation (3.5) as a polynomial identity in z, not by sampling z.
    for a in range(1,11):
        for b in range(a+1,15):
            d=dpoly(a,b); dp=der(d); dpp=der(dp)
            lhs=sub(mul(dpoly(a,b+1),dpoly(a,b-1)),mul(dpoly(a-1,b),dpoly(a+1,b)))
            braces=add(mul(d,dp),mul([F(1),F(-1)],sub(mul(dp,dp),mul(d,dpp))))
            factor=F((b-a)*(a+b+1),a*b*(a+1)*(b+1))
            rhs=[F(0),F(0)]+scale(braces,factor)
            assert all(v==0 for v in sub(lhs,rhs)),(a,b,'ratio identity failed')
            counts['ratio_polynomial_identities']+=1
    result={'status':'all exact assertions passed','executed_at_utc':datetime.now(timezone.utc).isoformat(),
            'arithmetic':'integer and Fraction; no floats','fan_rank_range':[1,80],
            'kernel_N_range':[4,32],'kernel_z_values':[str(z) for z in zvalues],
            'counts':counts,'first_rows':{str(n):[int(x) for x in ys[n]] for n in range(1,9)},
            'interpretation':'Finite cross-checks corroborate formulas and boundaries. The all-rank and all-positive-z claims rely on the analytic proof in the accompanying manuscript.'}
    output=Path(__file__).with_name('verification_results.json')
    output.write_text(json.dumps(result,ensure_ascii=False,indent=2)+'\n',encoding='utf-8')
    print(json.dumps(result,ensure_ascii=False,indent=2))

if __name__=='__main__':
    main()
