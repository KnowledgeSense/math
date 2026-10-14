#!/usr/bin/env python3
"""Standalone universal symbolic/rational checks for the bulk moment proof."""
import sympy as s,json,hashlib
from fractions import Fraction as Q
from pathlib import Path
T,t,m,ell=s.symbols('T t m ell');ff={0:s.Integer(1),1:-s.Rational(7,6),3:s.Rational(1,6)};ll={-4:6,-3:-7,-2:42,-1:-84,0:336,1:-840,2:78,3:133};roots=[s.Integer(2),-s.Integer(3)];d=lambda k:2**s.Integer(k)+T*(-3)**s.Integer(k)
A=[];B=[];C=[]
for v in roots:
 A.append(s.factor(sum(z*v**(-k)/d(k)for k,z in ff.items())))
 B.append(s.factor(sum(z*v**(-k)/d(k)for k,z in ll.items())))
 C.append(s.factor(sum(zu*zv*d(-j)*v**(-i+j)/d(i-j)for i,zu in ff.items()for j,zv in ff.items())))
DAC=-9475375*T*(8736*T*T+1277*T-1134)/(10077696*(T+1)*(3*T-2)*(4*T+9)*(9*T+4)*(27*T-8));assert s.cancel(A[0]*C[1]-A[1]*C[0]-DAC)==0
P=609140736*T**6-2807074304*T**5-4400288360*T**4+13769852070*T**3-1887377085*T**2-2495601009*T+589545216
CT=-7776*P/(175*T*(2*T-3)*(8*T-27)*(16*T+81)*(8736*T*T+1277*T-1134))
for i in range(2):assert s.cancel(-9870*A[i]+B[i]-CT*C[i])==0
Delta=-1950*T/((4*T+9)*(64*T+729));assert s.cancel(d(-3)/d(-2)-d(-7)/d(-6)-Delta)==0
corr=101088*P/((2*T-3)*(4*T+9)*(8*T-27)*(16*T+81)*(64*T+729)*(8736*T*T+1277*T-1134));assert s.cancel(s.Rational(7,6)*CT*Delta-corr)==0
g0=1-t/6-t*t/6;g1=sum(t**j for j in range(1,7));Z=t**7-463*t+798;quot,rem=s.div(Z,g0,t);assert rem==0
LZ=s.expand(-t*g0*quot.subs(t,1/t));assert LZ==sum(v*t**k for k,v in ll.items())
Pperp=t*t*(1-t*t)**2*(t*t+t**4-20)*(t*t+t**4-90);N,rem=s.div(Pperp,(1-t)*g0,t);assert rem==0
QH=s.div(g1,g0,t)[0];assert [QH.coeff(t,j)for j in [4,3,2,1]]==[-6,0,-42,36]
# Reverse highest/lowest expansions; only degree <=3 is relevant.
rev=1+7*t*t-6*t**3
R=s.series((1+7*t*t-6*t**3)*rev**ell,t,0,4).removeO().expand()
LL=s.series((6-7*t+42*t*t-84*t**3)*rev**m,t,0,4).removeO().expand()
for j,v in enumerate([1,0,7*(ell+1),-6*(ell+1)]):assert s.simplify(R.coeff(t,j)-v)==0
for j,v in enumerate([6,-7,42*(m+1),-84-85*m]):assert s.simplify(LL.coeff(t,j)-v)==0
bound=Q(1792,5103)*Q(2,3)**6/(1-Q(1,3)**29);assert bound<Q(1,30)
assert Q(1792,5103)/(1-Q(1,3)**29)<Q(1,2)
assert Q(21,160)*Q(1,2)**25/(1-Q(1,2)**29)+Q(56,1215)*Q(1,3)**25/(1-Q(1,3)**29)<Q(1,10000)
coeff=list(reversed([int(z)for z in s.Poly(P,T).all_coeffs()]));pbound=sum(Q(abs(v),30**j)for j,v in enumerate(coeff));assert pbound<700000000
assert 1134-Q(1277,30)-Q(8736,900)>1080
correction=Q(101088*700000000,2*8*26*80*726*1080);positive=Q(252*420*30,31);assert correction==Q(328125,121)and correction<2712 and positive>102000
out={'scope':'Universal symbolic and exact rational checks for bulk characters7<=chi<=n-16, n>=29; boundary ranks not checked.','all_pass':True,'DAC':str(s.factor(DAC)),'A_over_B':-9870,'C':str(s.factor(CT)),'T_bound':str(bound),'P_absolute_bound':str(pbound),'correction_bound':str(correction),'positive_lower_bound':str(positive)};path=Path(__file__).with_suffix('.json');path.write_text(json.dumps(out,indent=2)+'\n');print(json.dumps({'path':str(path),'sha256':hashlib.sha256(path.read_bytes()).hexdigest(),'all_pass':True}))
