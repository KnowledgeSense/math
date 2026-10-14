#!/usr/bin/env python3
"""Second verifier: binary fixed point, Mercator logs, symbolic jets.

No module from the first program is imported. All decisions use integers; floats record time only.
The logarithm is obtained by scaling to (1/2,1], then using -log(1-w).
Derivatives are generated from Laurent monomials by the chain rule, rather than
copied from the first program's derivative formulas. Closed dyadic splits give full coverage.
"""
from fractions import Fraction as F
from math import isqrt
import hashlib, json, time
from pathlib import Path

S = 2**170
N = 180
def ceildiv(a,b): return -((-a)//b)
class Box:
    def __init__(self,lo,hi=None):
        lo=F(lo); hi=lo if hi is None else F(hi)
        assert lo<=hi
        self.lo=lo.numerator*S//lo.denominator
        self.hi=ceildiv(hi.numerator*S,hi.denominator)
    @classmethod
    def raw(cls,a,b):
        assert a<=b
        out=object.__new__(cls); out.lo=a; out.hi=b; return out
    @staticmethod
    def wrap(x): return x if isinstance(x,Box) else Box(x)
    def __add__(self,x):
        x=self.wrap(x); return Box.raw(self.lo+x.lo,self.hi+x.hi)
    __radd__=__add__
    def __neg__(self): return Box.raw(-self.hi,-self.lo)
    def __sub__(self,x): return self+-self.wrap(x)
    def __rsub__(self,x): return self.wrap(x)+-self
    def __mul__(self,x):
        x=self.wrap(x)
        vals=[a*b for a in (self.lo,self.hi) for b in (x.lo,x.hi)]
        return Box.raw(min(vals)//S,ceildiv(max(vals),S))
    __rmul__=__mul__
    def reciprocal(self):
        assert self.lo>0 or self.hi<0
        return Box.raw((S*S)//self.hi,ceildiv(S*S,self.lo))
    def __truediv__(self,x): return self*self.wrap(x).reciprocal()
    def __rtruediv__(self,x): return self.wrap(x)*self.reciprocal()
    def __pow__(self,n):
        assert isinstance(n,int)
        if n<0: return (self.reciprocal())**(-n)
        if n==0: return Box(1)
        # Direct endpoint powers, a different implementation from recursion.
        den=S**(n-1)
        if n%2: return Box.raw(self.lo**n//den,ceildiv(self.hi**n,den))
        lower=0 if self.lo<=0<=self.hi else min(self.lo**n,self.hi**n)//den
        upper=ceildiv(max(self.lo**n,self.hi**n),den)
        return Box.raw(lower,upper)
    def sqrt(self):
        assert self.lo>=0
        a=isqrt(self.lo*S); b=isqrt(self.hi*S)
        return Box.raw(a,b+(b*b<self.hi*S))
    def log(self):
        assert self.lo>0
        return Box.raw(log_endpoint(self.lo).lo,log_endpoint(self.hi).hi)
    def report(self): return [str(F(self.lo,S)),str(F(self.hi,S))]

def minus_log_one_minus(w):
    assert 0<=w.lo<=w.hi<S
    power=Box(1); result=Box(0)
    for k in range(1,N+1):
        power=power*w; result=result+power/k
    remainder=power*w/((N+1)*(1-w))
    return Box.raw(result.lo,result.hi+remainder.hi)
LOG2=minus_log_one_minus(Box(F(1,2)))
def log_endpoint(a):
    # a/S = 2^k * u, 1/2 < u <= 1; exact integer comparisons.
    k=a.bit_length()-S.bit_length()
    numerator=a; denominator=S
    if k>=0: denominator*=2**k
    else: numerator*=2**(-k)
    if numerator>denominator: denominator*=2; k+=1
    assert denominator<2*numerator<=2*denominator
    return k*LOG2-minus_log_one_minus(Box(F(denominator-numerator,denominator)))

# Laurent polynomials in q,y,z,c, exact rational coefficients.
def addterm(out,m,a):
    out[m]=out.get(m,F(0))+a
    if not out[m]: del out[m]
def add(a,b):
    out=dict(a)
    for m,v in b.items(): addterm(out,m,v)
    return out
def scale(a,k): return {m:v*k for m,v in a.items() if v*k}
def mul(a,b):
    out={}
    for m,u in a.items():
        for n,v in b.items(): addterm(out,tuple(x+y for x,y in zip(m,n)),u*v)
    return out
def mon(a,b=0,d=0,e=0): return {(a,b,d,e):F(1)}
def derivative(poly):
    # d/dx=(1-q)d/dq - q^(-1)d/dy.
    out={}
    for (a,b,d,e),v in poly.items():
        if a:
            addterm(out,(a-1,b,d,e),a*v)
            addterm(out,(a,b,d,e),-a*v)
        if b: addterm(out,(a-1,b-1,d,e),-b*v)
    return out
one=mon(0); qp=mon(1); yp=mon(0,1); zp=mon(0,0,1); cp=mon(0,0,0,1)
phi_poly=add(yp,mul(cp,mul(yp,mul(add(yp,scale(zp,-1)),add(yp,scale(zp,-1))))))
jets=[mul(mon(2),phi_poly)]
for _ in range(4): jets.append(derivative(jets[-1]))
q2four=mul(mon(2),jets[4]); assert all(m[0]>=0 and 0<=m[1]<=3 for m in q2four)

# Compare independently differentiated polynomial with all four printed formulas.
def P(*terms):
    out={}
    for coefficient,a,d,e in terms: addterm(out,(a,0,d,e),F(coefficient))
    return out
qm1=add(qp,scale(one,-1))
listed=[
 mul(qm1,P((15,2,2,1),(-6,1,2,1),(-28,1,1,1),(-2,0,2,1),(-4,0,1,1),(12,0,0,1),(15,2,0,0),(-6,1,0,0),(-2,0,0,0))),
 scale(mul(qm1,P((8,3,2,1),(-7,2,2,1),(-30,2,1,1),(12,1,1,1),(21,1,0,1),(4,0,1,1),(3,0,0,1),(8,3,0,0),(-7,2,0,0))),2),
 scale(mul(cp,mul(qm1,P((32,3,1,0),(-28,2,1,0),(-45,2,0,0),(18,1,0,0),(6,0,0,0)))),-1),
 scale(mul(cp,mul(mon(2),mul(qm1,add(scale(qp,8),scale(one,-7))))),2)
]
assembled={}
for k,poly in enumerate(listed): assembled=add(assembled,mul(mon(0,k),poly))
assert assembled==q2four

c=Box(F(2,125)); qstar=Box(5).sqrt().reciprocal()
L=qstar/(1-qstar)**6; lnL=L.log(); xs=-(1-qstar).log(); ys=5*xs
d=2*(1-qstar)/(1+5*qstar); DD=d-1/ys
z=ys-DD/(c*(1+(1-DD**2/c).sqrt()))
def eval_poly(poly,q,y):
    values=(q,y,z,c); out=Box(0)
    powers=[{} for _ in values]
    for m,a in poly.items():
        term=Box(a)
        for j,n in enumerate(m):
            if n not in powers[j]: powers[j][n]=values[j]**n
            term=term*powers[j][n]
        out=out+term
    return out
def xy(q): return -(1-q).log(),lnL+(1-q).log()-q.log()
def phi(y): return y*(1+c*(y-z)**2)
def efficiency(q):
    x,y=xy(q); return q**2*phi(y)/x
def f2(q):
    _,y=xy(q); return eval_poly(jets[2],q,y)
def f4scaled(q):
    _,y=xy(q); return eval_poly(q2four,q,y)
def G2(q):
    x,_=xy(q); return 25*c*(30*x-4*z)-5*f2(q)

assert Box(F(5,2)).hi<z.lo and z.hi<Box(3).lo
assert DD.lo>0 and (c-DD**2).lo>0
assert (1-c*z**2/3).lo>0
assert Box(F(1,2)).hi<xs.lo<xs.hi<Box(F(31,50)).lo
assert (L/(1+L)).hi<Box(F(941,1000)).lo
assert L.lo>Box(F(3,2)).hi # ensures A<X
for endpoint in [F(5,2),F(31,10)]:
    assert (c*(Box(endpoint)-z)**2-Box(F(1,1000))).lo>0
assert (-Box(F(2,5)).log()-Box(F(9,10))).lo>0
assert Box(F(1001,1000)-F(11,1000)*F(9,31)-1).hi<0
assert (-(1-Box(F(406,1000))).log()-Box(F(13,25))).lo>0
assert (-(1-Box(F(4647,10000))).log()-Box(F(5,8))).hi<0
assert (-(1-Box(F(393,1000))).log()-Box(F(1,2))).hi<0
assert (-(1-Box(F(463,1000))).log()-Box(F(31,50))).lo>0
small_u=lnL-Box(F(1,100)).log()
assert small_u.lo>max(3*S,z.hi)
small=Box(F(1,100))*(small_u+c*small_u**3); assert small.hi<S

near=[]
for k in range(4):
    poly={m:v for m,v in q2four.items() if m[1]==k}
    near.append(eval_poly(poly,Box(0,F(1,20)),Box(1)))
assert near[0].lo>0 and near[2].lo>0
# Exact polynomial comparison above permits this sign-preserving factorization.
near[3]=2*c*Box(0,F(1,20))**2*(1-Box(0,F(1,20)))*(7-8*Box(0,F(1,20)))
assert near[3].lo>=0
B=max(abs(near[1].lo),abs(near[1].hi))
assert B*B<4*near[0].lo*near[2].lo
assert f2(Box(F(3,5))).hi<0

records=[]; cover=[]
def prove(name,fn,left,right):
    pending=[(F(left),F(right),0)]; nodes=0; leaves=0; worst=None; depthmax=0
    while pending:
        a,b,depth=pending.pop(); nodes+=1; depthmax=max(depthmax,depth)
        interval=fn(Box(a,b))
        if interval.lo>0:
            leaves+=1; worst=interval.lo if worst is None else min(worst,interval.lo)
            cover.append([name,str(a),str(b),str(F(interval.lo,S))])
        else:
            assert depth<28,(name,str(a),str(b),interval.report())
            middle=(a+b)/2
            pending.extend([(middle,b,depth+1),(a,middle,depth+1)])
    # Independent post-pass coverage: exact chain of rational endpoints.
    pieces=sorted((F(a),F(b)) for label,a,b,_ in cover if label==name)
    assert pieces[0][0]==F(left) and pieces[-1][1]==F(right)
    assert all(pieces[i][1]==pieces[i+1][0] for i in range(len(pieces)-1))
    records.append(dict(name=name,nodes=nodes,leaves=leaves,depth=depthmax,
                        smallest_margin=str(F(worst,S))))

start=time.time()
prove('a_global',lambda q:Box(F(1001,1000))-efficiency(q),F(1,100),F(941,1000))
prove('b_high',lambda q:Box(F(99,100))-efficiency(q),F(3,5),F(941,1000))
prove('c_low',lambda q:1-efficiency(q),F(1,100),F(406,1000))
prove('c_high',lambda q:1-efficiency(q),F(4647,10000),F(941,1000))
prove('d_fourth',f4scaled,F(1,20),F(3,5))
prove('e_Gsecond',G2,F(393,1000),F(463,1000))
here=Path(__file__).resolve().parent
out=dict(status='PASS',arithmetic='integer binary fixed point',denominator=str(S),
         logarithm='180-term Mercator after scaling to (1/2,1]',
         symbolic_derivative_monomials=[len(p) for p in jets],
         fourth_polynomial_formula_exact_match=True,z_between_5over2_and_3=True,
         constants=dict(qstar=qstar.report(),L=L.report(),z=z.report()),
         small_q_upper=str(F(small.hi,S)),nearzero_coefficients=[a.report() for a in near],
         checks=records,wall_seconds=time.time()-start,
         source_sha256=hashlib.sha256(Path(__file__).read_bytes()).hexdigest())
(here/'independent_cover.json').write_text(json.dumps(cover,indent=2)+'\n')
(here/'independent_result.json').write_text(json.dumps(out,indent=2)+'\n')
print(json.dumps(out,indent=2))
