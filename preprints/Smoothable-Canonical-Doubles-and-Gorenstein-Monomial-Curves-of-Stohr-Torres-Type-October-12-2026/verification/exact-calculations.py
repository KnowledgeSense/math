"""Exact algebra calculations accompanying Smoothable canonical doubles
and Gorenstein monomial curves of Stöhr–Torres type.
Author: Knowledge Sense.
Dependency: SymPy 1.14.0.
"""
import json, heapq, time
import sympy as sp
start=time.perf_counter()

def apery(gens):
    m=min(gens); w=[None]*m; w[0]=0; heap=[(0,0)]
    while heap:
        n,r0=heapq.heappop(heap)
        if w[r0]!=n: continue
        for a in gens:
            n1=n+a; r1=n1%m
            if w[r1] is None or n1<w[r1]:
                w[r1]=n1; heapq.heappush(heap,(n1,r1))
    assert None not in w
    return w

S=[8,12,18,22,51,55]; w=apery(S)
contains=lambda n:n>=0 and n>=w[n%8]
F=max(w)-8; genus=(sum(w)-28)//8
k=[next(n for n in range(r0,200,8) if not contains(F-n)) for r0 in range(8)]
K=lambda n:n>=0 and n>=k[n%8]
kmin=[n for n in range(max(k)+1) if K(n) and not any(K(n-a) for a in S)]
shifts=[0,4,8,61,65,122]
j=[next(n for n in range(r0,200,8) if all(contains(n+a) for a in shifts)) for r0 in range(8)]
assert w==[0,73,18,51,12,69,22,55]
assert kmin==[0,4,61] and genus==34 and F==65
assert j==[8,73,18,51,12,69,22,55]
assert all(w[r0]+a-w[(r0+a)%8]>=0 for r0 in range(8) for a in S)

genera=list(range(111,4304))+[10**6,10**9,10**18]
for g in genera:
    b=2*g-131; gens=[2*a for a in S]+[b,b+8,b+122]
    wg=apery(gens)
    direct=[None]*16
    for r0 in range(8):
        direct[2*r0]=2*w[r0]
        direct[(b+2*r0)%16]=b+2*k[r0]
    assert wg==direct
    assert max(wg)-16==2*g-1
    assert (sum(wg)-120)//16==g
    def ing(n): return n>=0 and n>=wg[n%16]
    minimal=[a for a in sorted(gens) if not any(0<h<a and ing(h) and ing(a-h) for h in range(1,min(a,2*max(gens))))] if g<5000 else None
    if minimal is not None: assert minimal==sorted(gens)

s,r,L,p,q=sp.symbols('s r L p q')
domain=sp.QQ.frac_field(s,r)
rels=[L**2-r-s**4,p**2-s**9*p-L**3*r**3,q**2-L**3*p**5-s**47*r]
gb=sp.groebner(rels,q,p,L,order='lex',domain=domain)
def nf(expr): return sp.expand(gb.reduce(sp.sympify(expr))[1])
def ell(expr): return sp.Poly(nf(expr),L,p,q).coeff_monomial(L*p*q)
BB=[1,r*L,p,L*p,q,L*q,p*q,L*p*q]
WW=[L*(p-s**9)*q,(p-s**9)*q/r,L*q,q,L*(p-s**9),p-s**9,L,1]
pair=[[sp.cancel(ell(a*b)) for b in BB] for a in WW]
assert pair==sp.eye(8).tolist()
def is_in_R(expr):
    try:
        sp.Poly(nf(expr),q,p,L,s,r)
        return True
    except sp.PolynomialError: return False
def is_in_B(expr):
    if not is_in_R(expr): return False
    c=sp.Poly(nf(expr),q,p,L).coeff_monomial(L)
    return sp.expand(c).subs(r,0)==0
assert all(is_in_R(r*a) for a in WW)
assert all(is_in_B(a*b) for i,a in enumerate(BB) for b in BB[i:])
assert all(is_in_B(r**3*a*b) for i,a in enumerate(WW) for b in WW[i:])

# Exact Jacobian calculation for the geometric generic quotient fiber.
# After s!=0 and a geometric square-root extension: L=lambda/s^2,
# P=p/s^9, Q=q/s^(51/2), and r/s^4=L^2-1.
P=sp.Symbol('P'); R=L**2-1
G=P**2-P-L**3*R**3; H=L**3*P**5+R
J=sp.diff(G,L)*sp.diff(H,P)-sp.diff(G,P)*sp.diff(H,L)
plane_gb=sp.groebner([G,sp.diff(G,L),sp.diff(G,P)],P,L,domain=sp.QQ)
branch_gb=sp.groebner([G,H,J],P,L,domain=sp.QQ)
assert list(plane_gb)==[1]
assert list(branch_gb)==[1]

extended=apery([4,18,51]); assert extended==[0,69,18,51]
assert max(extended)-4+1==66
for g in genera:
    b=2*g-131
    exponent=((b-93)//4 if b%4==1 else (b-75)//4)
    assert exponent>=0
    lifted_degree=(24+4*exponent+69 if b%4==1 else 24+4*exponent+51)
    assert lifted_degree==b


result=dict(sympy_version=sp.__version__,base_apery=w,canonical_apery=k,
 canonical_minimal_generators=kmin,multiplier_apery=j,base_frobenius=F,base_genus=genus,
 genera_tested=len(genera),dual_pairing_64='identity',denominator_checks_8=True,
 subring_products_36=True,multiplication_lifts_36=True,global_generic_plane_basis=[str(x) for x in plane_gb],
 global_generic_branch_basis=[str(x) for x in branch_gb],extended_apery=extended,
 g208_Q='r^3 lambda^48 p q',g208_semigroup=[16,24,36,44,102,110,285,293,407])
print(json.dumps(result,ensure_ascii=False,indent=2))
