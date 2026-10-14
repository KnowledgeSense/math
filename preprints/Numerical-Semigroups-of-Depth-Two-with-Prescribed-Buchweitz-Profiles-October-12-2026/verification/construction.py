"""Arithmetic checks for prescribed Buchweitz profiles.
Author: Knowledge Sense
Contact: math@knowledgesense.jp
Python 3.10 or later; standard library only.
"""
from pathlib import Path
from itertools import product
from fractions import Fraction
import json, random, time, hashlib, datetime

OUT = Path(__file__).resolve().parent
OUT.mkdir(parents=True, exist_ok=True)
started = time.perf_counter()

def params(N, B):
    x = N + 1
    h = x*x + 2*B*x
    K = 2*x
    M = h + 1
    u = (2*K + 1)*M
    m = K*(u + 2*M) + 1
    return h, K, M, u, m

def construct(N, B, target, order=None):
    h, K, M, u, m = params(N, B)
    prev, a_prev, data = h, 1, []
    for n, a in enumerate(target, 2):
        R = 2*h + 5 - 2*n + a - a_prev
        q, rem = divmod(R, 2*n-1)
        assert R > 0 and 0 <= q < prev
        data += [(n, rem)] + [(n, 0)]*(prev-q-1)
        prev, a_prev = q, a
    data += [(N+1, 0)]*prev
    assert len(data) == h
    if order is not None:
        order(data)
    large = [m-1-(d-1)*u-(t-1)*M-j for j,(d,t) in enumerate(data,1)]
    C = [0, u, u+M, u+2*M] + large
    assert len(set(C)) == h+4
    assert 0 < min(large) and 2*min(large)>m
    assert 2*(u+2*M)<m and max(C)<=m-2
    genus = m-1+len(C)
    x=N+1
    assert genus == 8*x**4+(16*B+6)*x**3+(12*B+9)*x*x+(2*B+6)*x+4
    return C, data, genus

records=[]
def check_profile(N, B, target, order=None, literal_gap=False):
    C,data,g=construct(N,B,target,order)
    h,K,M,u,m=params(N,B)
    mask=(1<<m)-1
    bits=1
    counts=[]
    for n in range(1,K+3):
        nxt=0
        for c in C:
            nxt |= bits << c
        nxt &= mask
        expected=(min(n,K)+1)**2+sum((min(n-1,d-2)+1)**2+t*(n>=d) for d,t in data)
        H=nxt.bit_count()
        assert H==expected, (N,B,target,n,H,expected)
        beta=H-(2*n-1)*(len(C)-1)
        assert beta==(1 if n==1 else target[n-2]) if n<=N else beta<0
        if n>K:
            assert nxt==bits
        bits=nxt
        counts.append(H)
    if literal_gap:
        G=list(range(1,m))+[2*m-1-c for c in C]
        assert len(set(G))==g and m not in G and 2*m-1 in G
        total=1
        for n in range(1,N+3):
            new=0
            for c in G:
                new |= total << c
            total=new
            assert total.bit_count()-(2*n-1)*(g-1)==counts[n-1]-(2*n-1)*(len(C)-1)
    records.append(dict(N=N,B=B,target=list(target),g=g,m=m,H=counts,literal_gap=literal_gap))

exhaustive=0
for N,B in [(2,1),(2,2),(2,3),(3,1),(3,2),(3,3),(4,1),(4,2),(5,1),(6,1)]:
    for a in product(range(-B,B+1),repeat=N-1):
        check_profile(N,B,a,literal_gap=N==2 and B==1)
        exhaustive+=1

rng=random.Random(19102026)
for N,B in [(2,10),(3,7),(4,4),(6,3),(8,2),(10,1)]:
    for a in [tuple([-B]*(N-1)),tuple([B]*(N-1)),tuple(B*(-1)**i for i in range(N-1)),tuple(0 for _ in range(N-1))]:
        check_profile(N,B,a)
    check_profile(N,B,tuple(rng.randint(-B,B) for _ in range(N-1)),order=rng.shuffle)

# Literal, untruncated sumsets test the general fringe lemma for all admissible C.
fringe=0
for m in range(3,11):
    for choices in product([False,True],repeat=m-2):
        C={0}|{i+1 for i,b in enumerate(choices) if b}
        if C=={0}: continue
        A=C|set(range(m,2*m-1))
        G={2*m-1-a for a in A}
        AC,AA,GG={0},{0},{0}
        for n in range(1,9):
            AC={a+c for a in AC for c in C}
            AA={a+c for a in AA for c in A}
            GG={a+c for a in GG for c in G}
            assert AA==AC|set(range(m,2*n*(m-1)+1))
            assert len(GG)-(2*n-1)*(len(G)-1)==len(AC&set(range(m)))-(2*n-1)*(len(C)-1)
        fringe+=1

# Worst coherent triples and exact arithmetic at enormous parameters.
local=0
for N in [2,3,4,7,100,10**4,10**9]:
    for B in [1,2,7,10**6,10**40]:
        h,K,M,u,m=params(N,B)
        assert B+2*N-2*h-3<0 and 2*K+1<2*(h+3)
        for n in sorted({3,N,max(3,N//2)}):
            if not 3<=n<=N: continue
            for left,mid,right in product([-B,B],repeat=3):
                if n==3: left=1
                Rprev=2*h+7-2*n+mid-left
                R=2*h+5-2*n+right-mid
                D=(2*n-3)*(2*n-1)
                numer=4*h+8+(4*n-4)*mid-(2*n-1)*left-(2*n-3)*right
                assert Fraction(Rprev,2*n-3)-Fraction(R,2*n-1)==Fraction(numer,D)>1
                assert Rprev//(2*n-3)>R//(2*n-1)>=0
                local+=1

# A small example in the supplied proof, counted directly.
m=169; C={0,26,28,97}; G=set(range(1,m))|{2*m-1-c for c in C}; sumG={0}; example=[]
for n in range(1,11):
    sumG={v+c for v in sumG for c in G}
    example.append(len(sumG)-(2*n-1)*(len(G)-1))
assert example[1:6]==[0,1,0,0,1] and all(v<0 for v in example[6:])

result=dict(status='all assertions passed',exhaustive_profiles=exhaustive,total_profiles=len(records),
            full_gap_profiles=sum(r['literal_gap'] for r in records),generic_fringe_sets=fringe,
            generic_degree_cases=8*fringe,extreme_local_comparisons=local,example_beta=example,
            elapsed_seconds=time.perf_counter()-started,completed_utc=datetime.datetime.now(datetime.timezone.utc).isoformat(),
            code_sha256=hashlib.sha256(Path(__file__).read_bytes()).hexdigest(),records_sha256=hashlib.sha256(json.dumps(records,sort_keys=True).encode()).hexdigest())
(OUT/'certificate.json').write_text(json.dumps(result,ensure_ascii=False,indent=2),encoding='utf-8')
print(json.dumps({k:v for k,v in result.items() if k!='records'},ensure_ascii=False,indent=2))
