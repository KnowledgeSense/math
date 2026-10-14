"""Exact verification for extendably 312-avoiding alternating sign rectangles.
Author: Knowledge Sense
Python 3.10 or newer; standard library only.
"""
from fractions import Fraction
from functools import lru_cache
from itertools import combinations
from math import comb
from pathlib import Path
import datetime, json

ROOT=Path(__file__).resolve().parent
def B(u,v):
    if v<0: return 0
    if u>=0: return comb(u,v) if v<=u else 0
    return (-1)**v*comb(v-u-1,v)
def cat(i): return comb(2*i,i)//(i+1)
def F(r,k,d):
    return (sum(2**(i-1)*B(k,i)*(B(r-2,d-i)-2*B(r-2,d-i-2)) for i in range(1,d+1))
            + B(r,d)+sum(cat(2*i)*B(r-1+2*i,d-1-2*i) for i in range((d-1)//2+1))
            +2*sum((-1)**i*B(r,d-i) for i in range(1,d+1)))
sch=[1]
for n in range(1,32): sch.append(sch[n-1]+sum(sch[i]*sch[n-1-i] for i in range(n)))
@lru_cache(None)
def S(r,k,d):
    if d<0 or r<d or k<d: return 0
    if d==0: return 1
    if r==k==d: return sch[d-1]
    if d==k:
        return sum(S(j,k,j)*B(r-j-1,k-j) for j in range(k+1))
    return (S(r,k-1,d)+S(r-1,k-1,d-1)
            +sum(sch[i-2]*(S(r+1-i,k+1-i,d+1-i)-(B(r-i,d+1-i) if d<r else 0)) for i in range(2,d+1)))

checks=0
for r in range(31):
 for k in range(31):
  for d in range(min(r,k)+1):
   assert F(r,k,d)==S(r,k,d), (r,k,d,F(r,k,d),S(r,k,d))
   checks+=1

N=20
def mul(p,q): return [sum(p[i]*q[n-i] for i in range(n+1)) for n in range(N+1)]
def power(p,n):
    result=[1]+[0]*N
    for _ in range(n): result=mul(result,p)
    return result
def inverse(p):
    q=[Fraction(1,p[0])]
    for n in range(1,N+1): q.append(-sum(p[i]*q[n-i] for i in range(1,n+1))/p[0])
    return q
R=sch[:N+1]; P=[Fraction(1,2)]+[Fraction(R[i-1],2) for i in range(1,N+1)]
Q=inverse([1]+[-R[i-1] for i in range(1,N+1)])
series_checks=0
for a in range(9):
 for b in range(9):
    U=[B(a+n-1,n) for n in range(N+1)]
    other=mul(power(R,b),power(Q,a))
    T=mul(P,[U[n]+other[n] for n in range(N+1)])
    for d in range(N+1):
        assert T[d]==F(d+a,d+b,d), (a,b,d,T[d],F(d+a,d+b,d))
        series_checks+=1

@lru_cache(None)
def shorter(row):
    return tuple(prev for prev in combinations(range(1,row[-1]+1),len(row)-1)
                 if all(row[i]<=prev[i]<=row[i+1] for i in range(len(prev))))
def chains(row):
    if len(row)==1:
        yield (row,)
    else:
        for prev in shorter(row):
            for top in chains(prev): yield top+(row,)
def asm(chain,n):
    prev=set(); out=[]
    for row in chain:
        curr=set(row); out.append(tuple(int(j in curr)-int(j in prev) for j in range(1,n+1))); prev=curr
    return tuple(out)
def avoid312(m):
    ones=[tuple(j for j,v in enumerate(row) if v==1) for row in m]
    for i,j,k in combinations(range(len(m)),3):
        if any(a<b<c for c in ones[i] for a in ones[j] for b in ones[k]): return False
    return True
def valid_asm(m):
    n=len(m)
    assert all(sum(row)==1 for row in m)
    assert all(sum(m[i][j] for i in range(n))==1 for j in range(n))
    for row in list(m)+[tuple(m[i][j] for i in range(n)) for j in range(n)]:
        vals=[v for v in row if v]
        assert vals and vals[0]==vals[-1]==1 and all(x==-y for x,y in zip(vals,vals[1:]))
witnesses={(r,k,d):set() for r in range(4) for k in range(4) for d in range(min(r,k)+1)}
square=[]
for n in range(1,7):
    total=avoiding=0
    for chain in chains(tuple(range(1,n+1))):
        m=asm(chain,n); valid_asm(m); total+=1
        if not avoid312(m): continue
        avoiding+=1
        for r in range(min(n,3)+1):
         for k in range(min(n,3)+1):
            prefix=tuple(row[:k] for row in m[:r])
            if any(any(row) and sum(row)!=1 for row in prefix): continue
            d=sum(any(row) for row in prefix)
            if d<=min(r,k): witnesses[r,k,d].add(prefix)
    assert avoiding==sch[n-1]
    expected=1
    # classical unrestricted ASM product, computed as an integer rational
    import math
    p=Fraction(1)
    for j in range(n): p*=Fraction(math.factorial(3*j+1),math.factorial(n+j))
    assert total==p
    square.append({'n':n,'all_asms':total,'avoiding_312':avoiding})
matrix_checks=[]
for (r,k,d),ws in witnesses.items():
    assert len(ws)==F(r,k,d), (r,k,d,len(ws),F(r,k,d))
    matrix_checks.append({'r':r,'k':k,'d':d,'prefixes_witnessed_in_ASMs_of_order_at_most_6':len(ws),'formula':F(r,k,d)})

result={'checked_at_utc':datetime.datetime.now(datetime.timezone.utc).isoformat(),
        'recurrence_comparison':{'domain':'0 <= r,k <= 30; 0 <= d <= min(r,k)','triples':checks,'mismatches':0},
        'generating_series_comparison':{'domain':'0 <= a,b <= 8; 0 <= d <= 20','coefficients':series_checks,'mismatches':0},
        'independent_ASM_generation':square,'prefix_comparison':matrix_checks,
        'interpretation':'Finite checks support the formal proof. Prefix enumeration establishes witnesses through order 6; exhaustion of arbitrary extension orders is not assumed.',
        'example':{'S_2_2_1':F(2,2,1),'excluded_single_one_at_row_2_column_1':[[0,0],[1,0]],'reason':'An extension forces a 1 right of the first empty row, then the displayed 1, then a later 1 in column 2, giving 312.'}}
(ROOT/'verification_results.json').write_text(json.dumps(result,ensure_ascii=False,indent=2)+'\n',encoding='utf-8')
print(json.dumps({k:v for k,v in result.items() if k!='prefix_comparison'},ensure_ascii=False,indent=2))
