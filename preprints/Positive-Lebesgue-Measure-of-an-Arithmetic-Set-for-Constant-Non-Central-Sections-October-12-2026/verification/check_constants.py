"""Rational certificate for the explicit seed and the tail constants.
Author: Knowledge Sense. Contact: math@knowledgesense.jp.
Python 3.12, standard library only. All asserted comparisons use Fraction
interval endpoints rounded outwards to a 10^-28 grid.
"""
from fractions import Fraction as F
from math import factorial, isqrt
from pathlib import Path
import json

S = 10**28
def floor(v): return v.numerator // v.denominator
def ceil(v): return -floor(-v)
class B:
    def __init__(self,a,b=None):
        a,b=F(a),F(a if b is None else b)
        assert a<=b
        self.a,self.b=F(floor(a*S),S),F(ceil(b*S),S)
    def __add__(self,x):
        x=box(x); return B(self.a+x.a,self.b+x.b)
    __radd__=__add__
    def __neg__(self): return B(-self.b,-self.a)
    def __sub__(self,x): return self+-box(x)
    def __rsub__(self,x): return box(x)+-self
    def __mul__(self,x):
        x=box(x); p=[u*v for u in [self.a,self.b] for v in [x.a,x.b]]
        return B(min(p),max(p))
    __rmul__=__mul__
    def __truediv__(self,x):
        x=box(x); assert x.a*x.b>0
        return self*B(1/x.b,1/x.a)
    def __pow__(self,n):
        assert n>=0
        ans=B(1)
        for _ in range(n):ans=ans*self
        return ans
def box(v):return v if isinstance(v,B) else B(v)
def cos(v):
    v=box(v)
    n=32
    ans=sum(((-1)**j*v**(2*j)/factorial(2*j) for j in range(n)), B(0))
    rem=max(abs(v.a),abs(v.b))**(2*n)/factorial(2*n)
    return ans+B(-rem,rem)
def atan_rational(v,n=42):
    assert 0<v<F(1,2)
    z=sum(((-1)**j*v**(2*j+1)/F(2*j+1) for j in range(n)),F(0))
    rem=v**(2*n+1)/F(2*n+1)
    return B(z-rem,z+rem)
pi=16*atan_rational(F(1,5))-4*atan_rational(F(1,239))
rt=isqrt(2*S*S)
sqrt2=B(F(rt,S),F(rt+1,S))
assert sqrt2.a**2<2<sqrt2.b**2
gamma=(4+sqrt2)/14
angle=pi*gamma
ca=cos(angle)
assert ca.a>0
assert (1-5*ca**2).a>0
ds=[]
for r in range(1,8):
    x=(2*r-1)*gamma
    z=floor(x.a+F(1,2))
    assert x.b+F(1,2)<z+1
    v=x-z
    assert v.a*v.b>0
    if v.b<0:v=-v
    ds.append(pi*v)
def decimal_floor(x):return str(F(floor(x*10**9),10**9))
rows=[]
for k in range(2,7):
    ids=sorted(range(k),key=lambda r:ds[r].a)
    for i,j in zip(ids,ids[1:]):assert ds[i].b<ds[j].a
    s,t=ds[ids[0]],ds[ids[1]]
    dn=ds[k]
    assert 0<s.a<s.b<t.a<t.b<pi.a/2
    cs=cos(s)
    assert (cs-ca).a>0 # R*cos(s)>1, defining domain of Fminus.
    minus_angle=angle-dn
    if minus_angle.b<=0:
        minus={'automatic':True,'reason':'angle-delta_next <= 0'}
    else:
        assert minus_angle.a>0
        v=cs*cos(minus_angle)-ca
        assert v.a>0
        minus={'automatic':False,'cosine_margin_lower':str(v.a),'simple_lower':decimal_floor(v.a)}
    plus_angle=angle+dn
    if plus_angle.a>pi.b/2:
        plus={'automatic':True,'reason':'angle+delta_next > pi/2'}
    else:
        assert plus_angle.b<pi.a/2
        v=ca*cos((s+t)/2)-cos((t-s)/2)*cos(plus_angle)
        assert v.a>0
        plus={'automatic':False,'cosine_margin_lower':str(v.a),'simple_lower':decimal_floor(v.a)}
    rows.append({'k':k,'s_index':ids[0]+1,'t_index':ids[1]+1,'Fminus_test':minus,'Fplus_test':plus})
# Source (21) at j0=4, maximum tail digit 2. Square a positive inequality.
threshold=169*cos(pi/13)**2*(cos(pi/31)**2-ca**2)-(4*pi*ca)**2
assert threshold.a>0
# All-j universal comparisons: exact bases and the induction ratio.
bases=[]
for j in [256,257]:
    M=((j+4)**2+2)**4
    gap=2**(j//2)-72*M
    assert gap>0
    bases.append({'j':j,'M':str(M),'integer_gap':str(gap)})
assert 131**8<2*130**8
# q256 for theta0=[0;1,3,2,2,...]. The prefix alone fixes this denominator.
prev,q=0,1
for j in range(1,257):
    digit=1 if j==1 else 3 if j==2 else 2
    prev,q=q,digit*q+prev
out = {'method':'rational cosine-sign certificate', 'endpoint_scale':str(S),
'cosine_terms':32, 'atan_terms':42, 'pi_interval':[str(pi.a),str(pi.b)],
'gamma_interval':[str(gamma.a),str(gamma.b)], 'seed_checks':rows,
'source21_squared_margin_lower':str(threshold.a),
'source21_simple_lower':decimal_floor(threshold.a), 'tail_integer_bases':bases,
'ratio_integer_gap':str(2*130**8-131**8), 'theta_q256':str(q)}
Path(__file__).with_suffix('.json').write_text(json.dumps(out,indent=2),encoding='utf-8')
print('PASS: five seed inequalities, source tail threshold, and universal integer constants.')
