"""Exact checks for complete-bipartite quadratic ideals.
Author: Knowledge Sense
Run: python -X utf8 check.py --output certificate.json
Requires sympy for symbolic rational identities; other checks use Python integers.
Finite checks supplement the universal proof and never replace it.
"""
from pathlib import Path
from math import comb
from functools import lru_cache
from fractions import Fraction
from collections import Counter
import argparse, json, datetime, hashlib

def C(n,k):
    return comb(n,k) if 0<=k<=n else 0

def vectors(n,total):
    if n==1:
        yield (total,); return
    for a in range(total+1):
        for v in vectors(n-1,total-a): yield (a,)+v

def direct_order_function(p,q):
    n=p+q; generators=[]
    for j in range(n):
        g=[0]*n; g[j]=2; generators.append(tuple(g))
    for a in range(p):
        for b in range(p,n):
            g=[0]*n; g[a]=g[b]=1; generators.append(tuple(g))
    @lru_cache(None)
    def order(v):
        best=0
        for g in generators:
            if all(a>=b for a,b in zip(v,g)):
                best=max(best,1+order(tuple(a-b for a,b in zip(v,g))))
        return best
    return order

def packing(v,p):
    A=sum(v[:p]); B=sum(v[p:]); oa=sum(x%2 for x in v[:p]); ob=sum(x%2 for x in v[p:])
    return min((A+B)//2,A+(B-ob)//2,B+(A-oa)//2)

def deficiency_count(a,b,s):
    ans=0
    for t in range(a-1):
        for r in range(1,(a-t)//2+1):
            if t+r>s: continue
            ans+=C(t+b-1,b-1)*sum(C(a,k) for k in range(t+2*r,a+1))*C(s-t-r+a-1,a-1)
    return ans

def length_formula(p,q,s):
    return C(2*s+p+q-1,p+q)+deficiency_count(p,q,s)+deficiency_count(q,p,s)

def P(a,b):
    result=Counter()
    for t in range(a-1):
        for r in range(1,(a-t)//2+1):
            result[t+r-1]+=C(t+b-1,b-1)*sum(C(a,k) for k in range(t+2*r,a+1))
    return result

def coefficients(p,q):
    n=p+q
    e=[C(n-i,i)*2**(n-2*i) if 2*i<=n else 0 for i in range(n+1)]
    for a,b in ((p,q),(q,p)):
        for d,c in P(a,b).items():
            for j in range(d+1):
                e[b+1+j]+=(-1)**(b+1)*c*C(d,j)
    return e

def T(m,i,r):
    ans=0
    for j in range(m):
        t=sum((-1)**a*C(j,a)*2**(r-a)*C(i+r-a,i) for a in range(min(j,r)+1))
        ans+=(-1)**j*C(i-1,j)*t
    return ans

def integral_expression(m,i,r):
    # Integrate the polynomial in Eq.(8) by exact rational term sums.
    k=i-m-1; out=Fraction(0)
    for v in range(r+1):
        front=C(r+1,v)*2**v
        for a in range(min(m,r-v)+1):
            b=r-v-a
            if not 0<=b<=k: continue
            integ=sum(Fraction(C(b,j),m+k-b+j) for j in range(b+1))
            out+=front*C(m,a)*C(k,b)*integ
    return (i-1)*out

def symbolic_checks():
    import sympy as sp
    x,y,u,w,z,t=sp.symbols('x y u w z t')
    D=lambda v:1-2*v-u*v*v
    A=x-y+x*y; B=y-x+x*y
    base=x*y/(x-y)*(x*(4+u+2*u*x)/D(x)-y*(4+u+2*u*y)/D(y))
    cor1=u*u*x*x*y*(1-x)/((1-2*x)*D(x)*(1-(2+u)*x+u*y*(1-x)))
    cor2=cor1.xreplace({x:y,y:x})
    target=4*x*y/((1-2*x)*(1-2*y))+u*x*y/(x-y)*(x/((1-2*x)*(1-2*x-u*A))-y/((1-2*y)*(1-2*y-u*B)))
    assert sp.cancel(base+cor1+cor2-target)==0
    pre=w*w/((1-w)*(1-(1+u)*w)**3*(1-(1+u)*w*w))
    rhs=x*x*(1-x)**3/((1-2*x)*(1-(2+u)*x)**3*D(x))
    assert sp.cancel(pre.subs(w,x/(1-x))/(1-x)-rhs)==0
    F=(4+u+2*u*x)/D(x)-u**3*x*x*(1-x)**2/((1-2*x)*(1-(2+u)*x)**2*D(x))-u/(1+u*x)
    pf=-(7*x-3)/(x*(2*x-1))-(x-1)*(2*x-1)/(x*(u*x+2*x-1)**2)+(2*x-3)/(x*(u*x+2*x-1))+1/(x*(u*x+1))
    assert sp.cancel(F-pf)==0
    integral_identities=0
    for i in range(2,15):
        for m in range(1,i):
            S=sum((-1)**j*C(i-1,j)*(1-z)**j for j in range(m))
            R=(-1)**(m-1)*(i-1)*C(i-2,m-1)*sp.integrate(t**(m-1)*(t+z)**(i-m-1),(t,0,1-z))
            assert sp.expand(S-z**(i-1)-R)==0
            integral_identities+=1
    return {'rational_identities':3,'integral_polynomial_identities':integral_identities,'sympy_version':sp.__version__}

def main():
    parser=argparse.ArgumentParser(); parser.add_argument('--output',default='certificate.json'); args=parser.parse_args()
    started=datetime.datetime.now(datetime.timezone.utc).isoformat()
    results={'author':'Knowledge Sense','started_utc':started,'method':'exact integer and rational calculations'}
    results['symbolic']=symbolic_checks(); print('symbolic identities passed',flush=True)
    monomials=0; lengths=[]
    for p in range(1,5):
        for q in range(p,6):
            order=direct_order_function(p,q); n=p+q
            for d in range(10):
                for v in vectors(n,d):
                    assert order(v)==packing(v,p),(p,q,v)
                    monomials+=1
            if p<=2 and q<=4:
                for s in range(1,4):
                    direct=sum(order(v)<s for d in range(2*s+n-1) for v in vectors(n,d))
                    expected=length_formula(p,q,s)
                    assert direct==expected,(p,q,s,direct,expected)
                    lengths.append({'p':p,'q':q,'s':s,'length':direct})
            order.cache_clear()
    results['monomial_membership']={'p_range':[1,4],'q_range':'p..5','total_degree_range':[0,9],'count':monomials}
    results['direct_lengths']=lengths; print('membership and direct lengths passed',flush=True)
    pairs=0; high_coeffs=0; all_power_polynomials=0; examples=[]
    for p in range(1,17):
        for q in range(p,31):
            e=coefficients(p,q); n=p+q
            assert e[n]==0
            for s in range(1,9):
                value=sum((-1)**i*e[i]*C(s+n-i-1,n-i) for i in range(n+1))
                assert value==length_formula(p,q,s),(p,q,s,value)
                all_power_polynomials+=1
            assert length_formula(p,q,1)==2**p+2**q-1
            for i in range(p+1): assert e[i]==C(n-i,i)*2**(n-2*i)>0
            for i in range(p+1,n):
                r=n-i-1; v=T(p,i,r)+(T(q,i,r) if q<i else 0)
                assert e[i]==v
                assert e[i]*(-1)**(p+1)>0
                if q<i and (p-q)%2:
                    assert (-1)**(p-1)*T(p,i,r) > (-1)**(q-1)*T(q,i,r)>0
                high_coeffs+=1
            if p==2:
                for i in range(3,n):
                    r=n-i-1
                    v=Fraction(-2**(r-1)*C(i+r-1,i-1)*(2*i*(i-2)+(i-3)*r),i) if r else 3-n+(-1)**(n-1)
                    assert e[i]==v
            if (p,q) in ((1,1),(1,2),(1,4),(2,2),(2,3),(2,4),(3,3),(3,4),(4,4),(4,5)):
                examples.append({'p':p,'q':q,'coefficients':e})
            pairs+=1
    results['coefficients']={'p_range':[1,16],'q_range':'p..30','parameter_pairs':pairs,'higher_coefficient_comparisons':high_coeffs,'all_power_polynomial_checks':all_power_polynomials,'s_range':[1,8],'examples':examples}
    checks=0
    for i in range(2,23):
        for r in range(i-1):
            previous=None
            for m in range(1,i):
                exact=Fraction((-1)**(m-1)*T(m,i,r),C(i-2,m-1))
                assert exact==integral_expression(m,i,r)>0
                assert previous is None or previous>=exact
                previous=exact; checks+=1
    results['normalized_integral_and_monotonicity']={'i_range':[2,22],'r_range':'0..i-2','m_range':'1..i-1','checks':checks}
    results['all_assertions_passed']=True
    results['finished_utc']=datetime.datetime.now(datetime.timezone.utc).isoformat()
    results['script_sha256']=hashlib.sha256(Path(__file__).read_bytes()).hexdigest()
    Path(args.output).write_text(json.dumps(results,ensure_ascii=False,indent=2),encoding='utf-8')
    print(json.dumps({k:v for k,v in results.items() if k not in ('direct_lengths','coefficients')},ensure_ascii=False,indent=2))

if __name__=='__main__': main()
