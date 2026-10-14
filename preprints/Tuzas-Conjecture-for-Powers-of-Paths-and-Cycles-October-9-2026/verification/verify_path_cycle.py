"""Exact identities and finite graph checks for path and cycle powers.

The polynomial identities are exact; graph checks are finite corroboration.
Skolem existence and the co-chain lemma are mathematical inputs in the accompanying proofs.
"""
from itertools import combinations
from math import gcd
from pathlib import Path
import hashlib, json

def edge(a, b):
    assert a != b
    return tuple(sorted((a, b)))

def graph(n, k, cyclic=False):
    return {(i,j) for i in range(n) for j in range(i+1,n)
            if (min(j-i,n-j+i) if cyclic else j-i) <= k}

def verify_packing(edges, triangles):
    used = set()
    for tri in triangles:
        assert len(set(tri)) == 3
        support = {edge(a,b) for a,b in combinations(tri,2)}
        assert support <= edges and not (used & support)
        used |= support
    return len(triangles)

def delta(m):
    return int(m % 4 in (2,3))

def maximal_m(k):
    m = k // 3
    while 3*m+delta(m) > k:
        m -= 1
    assert 3*m+delta(m) <= k < 3*(m+1)+delta(m+1)
    return m

# Exact polynomials in t, stored in increasing degree order.
def add(a,b):
    return [(a[i] if i<len(a) else 0)+(b[i] if i<len(b) else 0)
            for i in range(max(len(a),len(b)))]

def scale(a,c):
    return [x*c for x in a]

def mul(a,b):
    out = [0]*(len(a)+len(b)-1)
    for i,x in enumerate(a):
        for j,y in enumerate(b):
            out[i+j] += x*y
    return out

expected = [(6,20),( -2,12),(-2,16),(6,20),(8,24),(16,28),
            (20,32),(8,24),(32,40),(20,32),(24,36),(8,28)]
rows = []
for r,(constant,linear) in zip(range(7,19),expected):
    m0 = maximal_m(r)
    m = [m0,4]
    h = [r//2,6]
    n = [2*r+2,24]
    a = add(scale(m,2),scale(h,-1))
    # Twice D, to avoid even an intermediate nonintegral coefficient.
    d2 = add(scale(mul(a,n),2),scale(mul(h,add(h,[1])),2))
    d2 = add(d2,scale(mul(m,m),-9))
    d2 = add(d2,scale(m,-3))
    d2 = add(d2,[-2*delta(m0)])
    assert d2 == [2*constant,2*linear,24]
    assert a[0] >= 0 and a[1] == 2
    assert constant >= 0 or r in (8,9)
    if constant < 0:
        assert 12+linear+constant > 0
    rows.append({'r':r,'m0':m0,'slope_coefficients':a,
                 'D_boundary_coefficients':[constant,linear,12]})

# The periodic selector is independently checked on a finite range as well.
for k in range(7,10001):
    assert maximal_m(k+12) == maximal_m(k)+4
    assert 2*maximal_m(k) >= k//2

path_repairs = 0
for k in (8,9):
    for n in range(2*k+2,206):
        es = graph(n,k)
        tris = [(x,x+u,x+w) for u,w in ((1,4),(2,7))
                for x in range(n-w)]
        tris.append((n-9,n-3,n-1))
        length = verify_packing(es,tris)
        mono = sum(i%2 == j%2 for i,j in es)
        assert length == 2*n-10 and mono == 4*n-20 == 2*length
        path_repairs += 1

cycle_specials = 0
for k,start in ((2,5),(6,14)):
    for n in range(start,206):
        es = graph(n,k,True)
        if k == 2:
            tris = [(2*j,(2*j+1)%n,(2*j+2)%n) for j in range(n//2)]
        else:
            tris = [(v,(v+1)%n,(v+5)%n) for v in range(n)]
            d = gcd(n,3)
            length = n//d
            for start_vertex in range(d):
                walk = [(start_vertex+3*j)%n for j in range(length)]
                tris += [(walk[2*j],walk[2*j+1],walk[(2*j+2)%length])
                         for j in range(length//2)]
        length = verify_packing(es,tris)
        mono = sum(i%2 == j%2 for i,j in es)
        h = k//2
        assert mono == (h*n if n%2 == 0 else h*(n-1))
        assert mono <= 2*length
        cycle_specials += 1

def bounded_compositions(total,parts,capacity):
    if parts == 1:
        if 0 <= total <= capacity:
            yield (total,)
        return
    for first in range(max(0,total-capacity*(parts-1)),min(capacity,total)+1):
        for rest in bounded_compositions(total-first,parts-1,capacity):
            yield (first,)+rest

run_colourings = 0
for k in (3,5,7,9,11):
    h = k//2
    for n in range(2*k+2,2*k+2+2*(h+1)):
        r = 2*(n//(k+1))
        extra = n-r*(h+1)
        for extras in bounded_compositions(extra,r,h):
            runs = [h+1+x for x in extras]
            assert len(runs)%2 == 0 and sum(runs) == n
            colours = [c%2 for c,length in enumerate(runs) for _ in range(length)]
            mono = sum(colours[i] == colours[j] for i,j in graph(n,k,True))
            formula = sum(length*length-(k+1)*length+k*(k+1)//2 for length in runs)
            assert mono == formula <= h*n
            run_colourings += 1

cochain_reductions = 0
for k in range(65):
    for n in range(2*k+3):
        es = graph(n,k)
        split = min(n,k+1)
        left, right = range(split),range(split,n)
        assert all(edge(i,j) in es for i,j in combinations(left,2))
        assert all(edge(i,j) in es for i,j in combinations(right,2))
        cross_left = [{j for j in right if edge(i,j) in es} for i in left]
        cross_right = [{i for i in left if edge(i,j) in es} for j in right]
        assert all(a<=b or b<=a for a,b in combinations(cross_left,2))
        assert all(a<=b or b<=a for a,b in combinations(cross_right,2))
        cochain_reductions += 1

receipt = {'passed':True,
    'exact_polynomial_rows':rows,'selector_finite_checks':9994,
    'path_repair_graphs':path_repairs,'cycle_special_graphs':cycle_specials,
    'all_admissible_run_colourings_in_test_range':run_colourings,
    'short_path_cochain_reductions':cochain_reductions,
    'scope':'Polynomial identities exact. Graph samples finite, not the general proof.',
    'script_sha256':hashlib.sha256(Path(__file__).read_bytes()).hexdigest()}
print(json.dumps(receipt,ensure_ascii=False,indent=2))
