"""Exact rational certificate and an explicitly specified domination polynomial."""
from fractions import Fraction
from math import factorial
from pathlib import Path
import json
F=Fraction
def multiply(p,q):
    r=[0]*(len(p)+len(q)-1)
    for i,a in enumerate(p):
        for j,b in enumerate(q): r[i+j]+=a*b
    return r
def evaluate(p,x):
    r=0
    for a in p[::-1]: r=r*x+a
    return r
def derivative(p): return [j*p[j] for j in range(1,len(p))]
Q=[1]
for p in ([0,1],[-1,1],[-1,1],[-2,1],[1,-3,1]):
    Q=multiply(Q,p)
assert Q==[0,-2,11,-21,18,-7,1]
brackets=[(1464,1465),(5960,5961),(15422,15423),(22636,22637),(30332,30333)]
barriers=[(F(0),F(3,8)),(F(2,5),F(1)),(F(1),F(2)),(F(2),F(13,5)),(F(21,8),None)]
q=lambda x:x*x-3*x+1
assert q(F(3,8))>0>q(F(2,5)) and q(F(13,5))<0<q(F(21,8))
certificates=[]
for (an,bn),(left,right) in zip(brackets,barriers):
    a,b=F(an,10000),F(bn,10000)
    assert left<a<b and (right is None or b<right)
    df=lambda x:2*x-1-evaluate(derivative(Q),x)/evaluate(Q,x)
    assert df(a)<0<df(b)
    zs=[a,b]+([F(1,2)] if a<=F(1,2)<=b else [])
    u=min(z*z-z-2 for z in zs)
    qs=[a,b]+([F(3,2)] if a<=F(3,2)<=b else [])
    R=b*max(abs(a-1),abs(b-1))**2*max(abs(a-2),abs(b-2))*max(abs(q(z)) for z in qs)
    T=sum(u**j/F(factorial(j)) for j in range(20))
    assert T>R>0
    certificates.append({'a':str(a),'b':str(b),'derivative_a':str(df(a)),'derivative_b':str(df(b)),
                         'energy_lower':str(u),'Q_absolute_upper':str(R),'Taylor19_lower':str(T),
                         'exact_margin':str(T-R),'margin_floor_millionths':(T-R)*10**6//1})


edges=[(0,1),(1,2),(0,3),(0,4),(1,5),(2,6),(2,7)]
n=8
closed=[1<<i for i in range(n)]
for i,j in edges:
    closed[i]|=1<<j
    closed[j]|=1<<i
counts=[0]*(n+1)
for s in range(1<<n):
    union=0
    for i in range(n):
        if s>>i&1: union|=closed[i]
    if union==(1<<n)-1: counts[s.bit_count()]+=1
factor=[0,0,0,1]
for p in ([2,1],[1,3,1],[1,3,1]): factor=multiply(factor,p)
assert counts==factor==[0,0,0,2,13,28,23,8,1]
result={'certificates':certificates,'tree':{'n':n,'edges':edges,'coefficients_ascending':counts,'factorization':'x^3 (x+2) (x^2+3x+1)^2'}}
Path('certificate_results.json').write_text(json.dumps(result,indent=2),encoding='utf-8')
print('Five exact certificates and direct enumeration of the specified tree agree.')
