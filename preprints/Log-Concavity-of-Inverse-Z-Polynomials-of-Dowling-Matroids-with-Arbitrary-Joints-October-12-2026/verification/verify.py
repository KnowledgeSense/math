# Author: Knowledge Sense
# Contact: math@knowledgesense.jp

"""Exact supplemental checks. Finite computations supplement the all-parameter proof.

The direct lattice check uses rank and closure, independently of the flat description,
Dowling generating series, or deletion formula. Only P/Z defining recursions and
signed incidence inversion are used to compute the invariant.
"""
from fractions import Fraction as F
from functools import lru_cache
from itertools import permutations
from math import factorial, comb, prod
from pathlib import Path
import json, time

def add(a,b):
    c=[F(0)]*max(len(a),len(b))
    for i,v in enumerate(a): c[i]+=v
    for i,v in enumerate(b): c[i]+=v
    while len(c)>1 and not c[-1]: c.pop()
    return c
def scale(a,x): return [v*x for v in a]
def shift(a,h): return [F(0)]*h+a
def mul(a,b):
    c=[F(0)]*(len(a)+len(b)-1)
    for i,v in enumerate(a):
        for j,w in enumerate(b): c[i+j]+=v*w
    return c
def rising(a,s): return F(prod(a+i for i in range(s)))
def falling(a,s): return prod(a-i for i in range(s))
def w(j,l): return F(0) if j<0 else (l-j)*l**(j-1)/factorial(j)
def tau(m,h):
    return F(1) if h==1 else F(m**(2*h-2)*prod(range(1,2*h-2,2))*(2*h-1)**(h-2))
@lru_cache(None)
def B(n,m):
    a=F(1,m);l=(n+a)/2
    return [factorial(n)*m**n*sum(w(j,l)*rising(a,p-j)/factorial(p-j)*rising(a,n-p-j)/factorial(n-p-j) for j in range(min(p,n-p)+1)) for p in range(n+1)]
def expected(n,m,k):
    if n==1: return [F(1),F(1)] if k else [F(1)]
    if m==1:
        if k==0:return B(n-1,1)
        ell=n-k
        out=scale(B(n,1),F(k,n))
        for h in range(1,n//2+1):out=add(out,scale(shift(B(n-2*h,1),h),(F(ell,n)*comb(n,2*h)-(comb(ell,2*h) if ell>=2*h else 0))*tau(1,h)))
        return out
    delta=mul([F(1),F(1)],B(n-1,m))
    for h in range(1,n//2+1):delta=add(delta,scale(shift(B(n-2*h,m),h),-comb(n-1,2*h-1)*tau(m,h)))
    return add(B(n,m),scale(delta,-(n-k)))
def weights(n,m,k):
    a=F(1,m);l=(n+a)/2;mu=l-F(1,2);J=n//2
    U=[a*(l-j)*l**(j-2)/(2*factorial(j)) for j in range(J+1)]
    if m>=2:
        c=a*n/(n+a-1);b=a*(1-a);d=a*a/3
        v=[w(j,l)-c*w(j,mu)-b*w(j-1,mu)-d*w(j-2,mu) for j in range(J+1)]
        W=[a/2*(v[j]/(l-j)-(v[j-1]/(l-j+1) if j else 0)) for j in range(J+1)]
        return [F(k,n)*U[j]+F(n-k,n)*W[j] for j in range(J+1)],U
    ell=n-k
    q=[]
    for j in range(J+1):
        z=F(k,n)
        for h in range(1,j+1):
            ratio=F(falling(ell,2*h),falling(n,2*h))
            fh=falling(j,h)*(l-h)**(j-h-2)/l**(j-2)
            z+=(F(ell,n)-ratio)*tau(1,h)/factorial(2*h)*fh
        q.append(z)
    return [U[j]*q[j] for j in range(J+1)],U
def from_weights(n,m,W):
    d=[rising(F(1)+F(1,m),z)/factorial(z) for z in range(n+1)]
    return [factorial(n)*m**n*sum(W[j]*d[p-j]*d[n-p-j] for j in range(min(p,n-p)+1)) for p in range(n+1)]

def cyclic(m):
    return list(range(m)),0,lambda a,b:(a+b)%m,lambda a:(-a)%m
def symmetric3():
    g=list(permutations(range(3)));e=(0,1,2)
    def multiply(a,b):return tuple(a[b[i]] for i in range(3))
    def inverse(a):return tuple(a.index(i) for i in range(3))
    return g,e,multiply,inverse

def lattice(n,group,k):
    elements,e,op,inv=group
    edges=[(i,j,g) for i in range(n) for j in range(i+1,n) for g in elements]+[(i,None,e) for i in range(k)]
    N=len(edges);full=(1<<N)-1
    @lru_cache(None)
    def rank(mask):
        adj=[[] for _ in range(n)];marks=set()
        for h,(i,j,g) in enumerate(edges):
            if not (mask>>h)&1:continue
            if j is None:marks.add(i)
            else:adj[i].append((j,g));adj[j].append((i,inv(g)))
        seen={};balanced=0
        for start in range(n):
            if start in seen:continue
            seen[start]=e;stack=[start];ok=True
            while stack:
                i=stack.pop()
                if i in marks:ok=False
                for j,g in adj[i]:
                    value=op(seen[i],g)
                    if j in seen:
                        if seen[j]!=value:ok=False
                    else:seen[j]=value;stack.append(j)
            balanced+=ok
        return n-balanced
    @lru_cache(None)
    def closure(mask):
        r=rank(mask);result=mask
        for h in range(N):
            if not (mask>>h)&1 and rank(mask|(1<<h))==r:result|=1<<h
        return result
    found={closure(0)};todo=list(found)
    while todo:
        mask=todo.pop()
        for h in range(N):
            if not (mask>>h)&1:
                f=closure(mask|(1<<h))
                if f not in found:found.add(f);todo.append(f)
    flats=sorted(found,key=lambda x:(rank(x),x));ranks=[rank(x) for x in flats];count=len(flats)
    above=[[j for j in range(i+1,count) if flats[i]&flats[j]==flats[i]] for i in range(count)]
    def middle(i,j):return [h for h in above[i] if flats[h]&flats[j]==flats[h]]
    @lru_cache(None)
    def P(i,j):
        if i==j:return [F(1)]
        r=ranks[j]-ranks[i];A=[F(0)]*(r+1)
        for h in middle(i,j):A=add(A,shift(P(h,j),ranks[h]-ranks[i]))
        return [A[r-z]-(A[z] if z<len(A) else 0) for z in range((r-1)//2+1)]
    @lru_cache(None)
    def Z(i,j):
        out=P(i,j)
        for h in middle(i,j):out=add(out,shift(P(h,j),ranks[h]-ranks[i]))
        r=ranks[j]-ranks[i]
        assert out==list(reversed(out)) and len(out)==r+1
        return out
    @lru_cache(None)
    def signedY(i,j):
        if i==j:return [F(1)]
        out=[F(0)]
        for h in middle(i,j):out=add(out,mul(Z(i,h),signedY(h,j)))
        return scale(out,-1)
    y=scale(signedY(0,count-1),(-1)**ranks[-1])
    assert y==expected(n,len(elements),k),(n,len(elements),k,y,expected(n,len(elements),k))
    return {'n':n,'m':len(elements),'k':k,'rank':ranks[-1],'flats':count,'coefficients':[int(x) for x in y],'rank_subsets_evaluated':rank.cache_info().currsize,'intervals_P':P.cache_info().currsize}

def main():
    counts = dict(kernel_rows=0, weight_comparisons=0, coefficient_comparisons=0,
                  closed_coloop_values=0, attenuation_sequences=0,
                  normalized_curvature_comparisons=0, jointless_trivial_rows=0)
    for n in range(2, 25):
        for m in (1, 2, 3, 4, 6, 10, 100, 1000):
            for k in range(0 if m > 1 else 1, n + 1):
                W, U = weights(n, m, k)
                y = from_weights(n, m, W)
                assert y == expected(n, m, k)
                assert all(v > 0 for v in W)
                for j in range(1, len(W) - 1):
                    assert W[j]**2 > W[j-1] * W[j+1]
                    counts['weight_comparisons'] += 1
                assert all(v.denominator == 1 and v > 0 for v in y)
                assert y == list(reversed(y))
                assert y[0] == ((m-1)*(n-1)+k)*prod(m*h+1 for h in range(1, n-1))
                for p in range(1, n):
                    assert y[p]**2 > y[p-1] * y[p+1]
                    counts['coefficient_comparisons'] += 1
                counts['kernel_rows'] += 1
                if m == 1:
                    ell = n-k
                    # sigma_0=1 and 1<=h<=floor(n/2); all denominators are positive.
                    sigma = [F(1)] + [F(ell-n*F(falling(ell, 2*h), falling(n, 2*h)),
                                        k*(2*h-1)) for h in range(1, n//2+1)]
                    assert all(sigma[i] >= sigma[i+1] >= 0 for i in range(len(sigma)-1))
                    counts['attenuation_sequences'] += 1
                    W1, U1 = weights(n, 1, 1)
                    q = [W[z]/U[z] for z in range(len(W))]
                    Q = [W1[z]/U1[z] for z in range(len(W1))]
                    for j in range(len(W)):
                        r = F(n+1, 2)-j
                        mu = F(n, 2)
                        s = mu/F(n+1, 2)
                        Pj = 2-(r+F(1, 2))/mu+F(3, 8)/mu*(1/r+1/(r+1))+1/(4*r*r*(r+1))
                        assert Q[j] == s**(j-2)*Pj/n
                        counts['closed_coloop_values'] += 1
                    for j in range(1, len(W)-1):
                        assert (q[j-1]+q[j+1]-2*q[j])/q[j] <= max(F(0), (Q[j-1]+Q[j+1]-2*Q[j])/Q[j])
                        counts['normalized_curvature_comparisons'] += 1
        y = expected(n, 1, 0)
        assert len(y) == n and y == list(reversed(y))
        assert all(v > 0 and v.denominator == 1 for v in y)
        assert all(y[p]**2 > y[p-1]*y[p+1] for p in range(1, len(y)-1))
        counts['jointless_trivial_rows'] += 1
    direct = []
    for name, n, group in [('C1', 4, cyclic(1)), ('C2', 4, cyclic(2)),
                           ('C3', 3, cyclic(3)), ('C6', 3, cyclic(6)), ('S3', 3, symmetric3())]:
        for k in range(n+1):
            row = lattice(n, group, k)
            row['group'] = name
            direct.append(row)
    small = []
    for m in (1, 2, 6):
        for k in (0, 1):
            row = lattice(1, cyclic(m), k)
            assert row['rank'] == k
            assert row['coefficients'] == ([1] if k == 0 else [1, 1])
            row['group'] = 'C' + str(m)
            small.append(row)
    C6 = [row['coefficients'] for row in direct if row['group'] == 'C6']
    S3 = [row['coefficients'] for row in direct if row['group'] == 'S3']
    assert C6 == S3
    out = {
        'author': 'Knowledge Sense', 'status': 'PASS',
        'scope': 'Finite exact checks supplementary to the analytic proof in the paper.',
        'exact_arithmetic': 'fractions.Fraction and integer gain products',
        'parameters': {'n': [2, 24], 'm': [1, 2, 3, 4, 6, 10, 100, 1000],
                       'k': '0 through n; m=1,k=0 checked separately with rank n-1'},
        'sigma_domain': 'sigma_0=1; 1<=h<=floor(n/2), n>=2, 1<=k<=n',
        'counts': counts, 'direct_lattice': direct, 'rank_zero_and_one': small,
        'equal_order_group_comparison': {'groups': ['C6', 'S3'], 'n': 3, 'k': [0, 3], 'status': 'PASS'}
    }
    Path(__file__).with_name('verification_results.json').write_text(
        json.dumps(out, ensure_ascii=False, indent=2)+'\n', encoding='utf-8')
    print(json.dumps({'status': out['status'], 'counts': counts,
                      'direct_lattice_cases': len(direct), 'rank_zero_and_one_cases': len(small)}))

if __name__ == '__main__':
    main()
