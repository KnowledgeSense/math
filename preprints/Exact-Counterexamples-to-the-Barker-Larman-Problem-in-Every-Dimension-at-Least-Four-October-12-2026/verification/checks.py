"""Finite algebra and integration checks for constant-volume noncentral sections.

Author: Knowledge Sense
Contact: math@knowledgesense.jp
"""
from pathlib import Path
import json
import sympy as s
from scipy.integrate import quad
from math import pi, gamma, sqrt, acos, sin, cos

checks=[]
def check(name, test, detail):
    if not bool(test): raise AssertionError((name,detail))
    checks.append(dict(name=name,result='pass',detail=str(detail)))

x,n,lam=s.symbols('x n lam', real=True)
a=lambda k:(k+1)/(2*(k+lam))
b=lambda k:(k+2*lam-1)/(2*(k+lam))
d=2*lam+2
diag=s.factor((d*(a(n)*b(n+1)+b(n)*a(n-1))-1)/(d-1))
target=lam*n*(n+2*lam)/((2*lam+1)*((n+lam)**2-1))
check('all-degree product diagonal',s.simplify(diag-target)==0,diag)
r1=-2*(d-2)/((d-1)*(d+4))
check('branch r1=-c22/2',s.simplify(r1+target.subs(n,2)/2)==0,r1)
derivative=2*lam*(n+lam)*(lam*lam-1)/((2*lam+1)*((n+lam)**2-1)**2)
check('all-degree monotonicity identity',s.simplify(s.diff(target,n)-derivative)==0,derivative)
check('n=2 coefficient identity c22+2*r1=0',s.simplify(target.subs(n,2)+2*r1)==0,'c22+2*r1=0')
dd=s.symbols('d', positive=True)
rr=-2*(dd-2)/((dd-1)*(dd+4))
twist=s.factor(2*(rr+(dd-2)/(2*(dd-1)))/(s.sqrt(dd)*s.sqrt(dd-1)))
check('frequency twist',s.simplify(twist-s.sqrt(dd)*(dd-2)/((dd-1)**s.Rational(3,2)*(dd+4)))==0,twist)
volume_slope=s.factor(rr*s.sqrt(dd)*(dd-1)**((dd-3)/2)/twist)
check('volume slope factor',s.simplify(volume_slope+2*(dd-1)**((dd-2)/2))==0,volume_slope)

for dim in (5,6,7,8,10,12):
    l=s.Rational(dim-2,2); R=s.symbols('R',positive=True)
    Y=lambda k:s.gegenbauer(k,l,x)/s.gegenbauer(k,l,1)
    q=Y(2)
    coeff=s.solve(s.Poly(q*q-s.Symbol('c0')-s.Symbol('c2')*Y(2)-s.Symbol('c4')*Y(4),x).coeffs(),s.symbols('c0 c2 c4'))
    check(f'd={dim}: product c22',s.simplify(coeff[s.Symbol('c2')]-target.subs({lam:l,n:2}))==0,coeff)
    L4=R*(R*R-1)**s.Rational(dim-3,2)*Y(4).subs(x,1/R)
    h2=s.simplify(-coeff[s.Symbol('c4')]*s.diff(L4,R).subs(R,s.sqrt(dim))/(2*L4.subs(R,s.sqrt(dim))))
    if dim==5: check('d5 second complement',h2==-25/(72*s.sqrt(5)),h2)
    if dim==6: check('d6 second complement',h2==-1071*s.sqrt(6)/10000,h2)
    check(f'd={dim}: low nonresonance',all(Y(k).subs(x,1/s.sqrt(dim))!=0 for k in (4,6)),'Y4,Y6 at 1/sqrt(d)')

A,B,X,e=s.symbols('A B X e')
G=lambda z:z+e*z**3
H=lambda u,v:s.cancel((G(u)-G(v))/(u-v))
Q=s.cancel(H(A,X)*H(X,B)/(H(A,B)*s.diff(G(X),X)))
num,den=s.fraction(s.factor(Q-1))
quot=s.cancel(num/((X-A)*(X-B)))
check('cross-ratio endpoint double factor',s.denom(quot)==1,quot)
check('cross-ratio at merged endpoint',s.simplify(s.diff(Q,X).subs({X:A,B:A}))==0,'Q_X(A,A,A)=0')

# Independent first coefficients of the exact axis-cycle symmetric formulas.
t=s.symbols('t'); J=s.sqrt(-3)
v=1+s.Rational(15,32)*t; c=-s.Rational(3,4)
D=4*(v**3+6*v*t*c+t+t*t*c**3)
d0=1-9*v*v+9*t*c
d1=3*(v-v**3-t-t*t*c**3+3*v*t*c)
K=(d0+J*d1)/(d0-J*d1)
check('divergence cycle volume constant',s.diff(D,t).subs(t,0)==-s.Rational(67,8),'-67/8')
check('divergence cycle multiplier constant',s.simplify(s.diff(K,t).subs(t,0)-s.Rational(201,64)*J)==0,'201 sqrt(-3)/64')

def sphere(k):return 2*pi**((k+1)/2)/gamma((k+1)/2)
for dim in (4,5,6,7,8,10,12):
    R=sqrt(dim); radius=sqrt(R*R-1)
    beta=(dim-4)/2
    area=sphere(dim-3)/(dim-1)*quad(lambda z:radius**(dim-1)*(1-z*z)**beta,-1,1,epsabs=1e-8)[0]
    expected=pi**((dim-1)/2)/gamma((dim+1)/2)*(R*R-1)**((dim-1)/2)
    check(f'd={dim}: ray volume normalization',abs(area/expected-1)<1e-9,(area,expected))
    cnormal=cos(.73)
    center=cnormal/R; width=sqrt((1-1/(R*R))*(1-cnormal*cnormal))
    val=sphere(dim-3)*(1-cnormal*cnormal)**(-(dim-3)/2)*quad(lambda z:R*R*(R*R*width*width*(1-z*z))**((dim-4)/2)*width,-1,1,epsabs=1e-8)[0]
    expect=sphere(dim-2)*R*(R*R-1)**((dim-3)/2)
    check(f'd={dim}: coarea derivative normalization',abs(val/expect-1)<1e-9,(val,expect))

out={'scope':'Symbolic identities and numerical round-ball integrals','count':len(checks),'checks':checks}
Path(__file__).with_name('results.json').write_text(json.dumps(out,ensure_ascii=False,indent=2),encoding='utf8')
print(json.dumps({'count':len(checks),'result':'all pass'},ensure_ascii=True))
