#!/usr/bin/env python3
"""First verifier: directed fixed-point interval certificate for the cubic potential.
Standard library only. All interval endpoints denote integers / 10**40.
This checks scalar inequalities; the universal partition reduction is separate.
"""
import math,json,time,hashlib
from fractions import Fraction
from pathlib import Path
S=10**40
class I:
 def __init__(self,a,b=None,raw=False):
  if raw:self.a,self.b=a,b;return
  a=Fraction(a);self.a=a.numerator*S//a.denominator;self.b=-((-a.numerator*S)//a.denominator)
 @staticmethod
 def cv(x):return x if isinstance(x,I) else I(x)
 def __add__(self,o):o=I.cv(o);return I(self.a+o.a,self.b+o.b,True)
 __radd__=__add__
 def __neg__(self):return I(-self.b,-self.a,True)
 def __sub__(self,o):return self+-I.cv(o)
 def __rsub__(self,o):return I.cv(o)+-self
 def __mul__(self,o):
  o=I.cv(o);v=[self.a*o.a,self.a*o.b,self.b*o.a,self.b*o.b]
  return I(min(v)//S,-((-max(v))//S),True)
 __rmul__=__mul__
 def __truediv__(self,o):
  o=I.cv(o);assert not o.a<=0<=o.b
  v=[Fraction(a*S,b) for a in (self.a,self.b) for b in (o.a,o.b)]
  lo=min(v);hi=max(v)
  return I(lo.numerator//lo.denominator,-((-hi.numerator)//hi.denominator),True)
 def __rtruediv__(self,o):return I.cv(o)/self
 def __pow__(self,n):
  assert isinstance(n,int) and n>=0
  if n==0:return I(1)
  if n%2==0:
   h=self**(n//2);v=[h.a*h.a,h.b*h.b]
   return I(0 if h.a<=0<=h.b else min(v)//S,-((-max(v))//S),True)
  return self*(self**(n-1))
 def sqrt(self):
  assert self.a>=0
  a=math.isqrt(self.a*S);b=math.isqrt(self.b*S)
  if b*b<self.b*S:b+=1
  return I(a,b,True)
 def log(self):
  assert self.a>0
  return I(log_point(self.a).a,log_point(self.b).b,True)
 def bounds(self):return [str(Fraction(self.a,S)),str(Fraction(self.b,S))]
 def floats(self):return [self.a/S,self.b/S]
def series(z):
 n=55;power=z;out=I(0);zz=z*z
 for j in range(n):out+=power/(2*j+1);power*=zz
 tail=2*power/((2*n+1)*(1-zz))
 out=2*out
 return I(out.a,out.b+tail.b,True)
LN2=series(I(Fraction(1,3)))
def log_point(x):
 A=x;B=S;k=0
 while A<B:A*=2;k-=1
 while A>=2*B:B*=2;k+=1
 z=I(Fraction(A-B,A+B));return series(z)+k*LN2
c=I(Fraction(2,125));q0=1/I(5).sqrt();L=q0/(1-q0)**6;lnL=L.log();x0=-(1-q0).log();y0=5*x0
d0=2*(1-q0)/(5*q0+1);D=d0-1/y0
z=y0-D/(c*(1+(1-D*D/c).sqrt()))
def phi(y):return y*(1+c*(y-z)**2)
def phi1(y):return 1+c*(3*y*y-4*z*y+z*z)
def phi2(y):return c*(6*y-4*z)
def base(q):
 x=-(1-q).log();y=lnL+(1-q).log()-q.log()
 return x,y

def eff(q):
 x,y=base(q);return q*q*phi(y)/x

def f2(q):
 x,y=base(q);a0=q*q;a1=2*q*(1-q);a2=2*(1-q)*(1-2*q)
 y1=-1/q;y2=(1-q)/(q*q)
 return a2*phi(y)+2*a1*phi1(y)*y1+a0*(phi2(y)*y1*y1+phi1(y)*y2)

def f4coeff(q):
 a0=(q-1)*(15*c*q*q*z*z-6*c*q*z*z-28*c*q*z-2*c*z*z-4*c*z+12*c+15*q*q-6*q-2)
 a1=2*(q-1)*(8*c*q**3*z*z-7*c*q*q*z*z-30*c*q*q*z+12*c*q*z+21*c*q+4*c*z+3*c+8*q**3-7*q*q)
 a2=-c*(q-1)*(32*q**3*z-28*q*q*z-45*q*q+18*q+6)
 a3=2*c*q*q*(q-1)*(8*q-7)
 return a0,a1,a2,a3

def q2f4(q):
 _,y=base(q);a=f4coeff(q)
 return a[0]+a[1]*y+a[2]*y*y+a[3]*y**3

def G2(q):
 x,y=base(q);return 25*phi2(5*x)-5*f2(q)

records=[]
def certify(name,fun,lo,hi,positive=True,maxdepth=35):
 lo=I(lo).a;hi=I(hi).b;stack=[(lo,hi,0)];count=0;deep=0;best=None
 while stack:
  a,b,d=stack.pop();v=fun(I(a,b,True));count+=1;deep=max(deep,d)
  margin=v.a if positive else -v.b
  if margin>0:
   best=margin if best is None else min(best,margin);continue
  if d>=maxdepth:raise RuntimeError((name,'uncertified',a/S,b/S,v.floats()))
  m=(a+b)//2;assert a<m<b
  stack.extend([(a,m,d+1),(m,b,d+1)])
 records.append({'name':name,'evaluations':count,'max_depth':deep,'certified_margin_lower_bound':str(Fraction(best,S))})

start=time.time()
# Exact endpoint and structural checks.
assert I(Fraction(5,2)).b<z.a<z.b<3*S and D.a>0 and (D*D-c).b<0
assert x0.a>I(Fraction(1,2)).b and x0.b<I(Fraction(31,50)).a
assert (1-c*z*z/3).a>0
assert (L/(1+L)).b<I(Fraction(941,1000)).a
assert ((1+c*(I(Fraction(5,2))-z)**2)-I(Fraction(1001,1000))).a>0
assert ((1+c*(I(Fraction(31,10))-z)**2)-I(Fraction(1001,1000))).a>0
assert ((-I(Fraction(2,5)).log())-I(Fraction(9,10))).a>0
assert (I(Fraction(1001,1000))-(I(Fraction(1001,1000))-I(Fraction(99,100)))*I(Fraction(9,31))-1).b<0
assert (-(1-I(Fraction(406,1000))).log()-I(Fraction(13,25))).a>0
assert (-(1-I(Fraction(4647,10000))).log()-I(Fraction(5,8))).b<0
assert (-(1-I(Fraction(393,1000))).log()-I(Fraction(1,2))).b<0
assert (-(1-I(Fraction(463,1000))).log()-I(Fraction(31,50))).a>0
# Small q: f/x <= q Phi(log(L/q)) <= q [y+c y^3], whose last expression increases with q for y>=3.
y=lnL-I(Fraction(1,100)).log();assert y.a>3*S and y.a>z.b
small=I(Fraction(1,100))*(y+c*y**3);assert small.b<S
# Near zero fourth derivative: q^2 f'''' is a cubic in y with nonnegative cubic coefficient.
a0,a1,a2,a3=f4coeff(I(0,I(Fraction(1,20)).b,True))
assert a3.a>=0 and a0.a>0 and a2.a>0
B=max(abs(a1.a),abs(a1.b));assert B*B<4*a0.a*a2.a
nearzero={'q_max':'1/20','a0_lower':str(Fraction(a0.a,S)),'a2_lower':str(Fraction(a2.a,S)),'abs_a1_upper':str(Fraction(B,S))}
certify('f/x < 1001/1000',lambda q:I(Fraction(1001,1000))-eff(q),Fraction(1,100),Fraction(941,1000))
certify('f/x < 99/100 when q >= 3/5',lambda q:I(Fraction(99,100))-eff(q),Fraction(3,5),Fraction(941,1000))
certify('f/x < 1 on low interval',lambda q:1-eff(q),Fraction(1,100),Fraction(406,1000))
certify('f/x < 1 on high interval',lambda q:1-eff(q),Fraction(4647,10000),Fraction(941,1000))
certify('fourth x derivative >0',q2f4,Fraction(1,20),Fraction(3,5))
assert f2(I(Fraction(3,5))).b<0
certify('G second x derivative >0',G2,Fraction(393,1000),Fraction(463,1000))
out={'status':'PASS: exact scalar interval certificate only; partition reduction is separate','precision_denominator':str(S),'log_series_terms':55,'constant_intervals':{'q0':q0.bounds(),'L':L.bounds(),'z':z.bounds()},'small_q_efficiency_upper':str(Fraction(small.b,S)),'nearzero_fourth_derivative':nearzero,'checks':records,'wall_seconds':time.time()-start,'source_sha256':hashlib.sha256(Path(__file__).read_bytes()).hexdigest()}
print(json.dumps(out,indent=2))
