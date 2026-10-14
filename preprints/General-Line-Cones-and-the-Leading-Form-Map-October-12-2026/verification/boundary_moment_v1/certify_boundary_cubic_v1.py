from pathlib import Path
import sympy as s,json
from fractions import Fraction as Q
T,x,b=s.symbols('T x b');f={0:s.Integer(1),1:-s.Rational(7,6),3:s.Rational(1,6)};lz={-4:6,-3:-7,-2:42,-1:-84,0:336,1:-840,2:78,3:133}
d=lambda k:2**s.Integer(k)+T*(-3)**s.Integer(k)
a=[];bb=[];c=[]
for v in[s.Integer(2),-s.Integer(3)]:
 a.append(s.factor(sum(aa*v**(-k)/d(k)for k,aa in f.items())))
 bb.append(s.factor(sum(aa*v**(-k)/d(k)for k,aa in lz.items())))
 c.append(s.factor(sum(au*av*d(-j)*v**(-i+j)/d(i-j)for i,au in f.items()for j,av in f.items())))
DAC=s.factor(a[0]*c[1]-a[1]*c[0]);C=s.factor((a[0]*bb[1]-a[1]*bb[0])/DAC)
FF={1:9072+C*d(0),2:9072+C*d(0),3:-173628+C*(78*d(-3)+s.Rational(931,6)*d(-1)),4:-1462104-133*C*d(0),5:468*(-468-s.Rational(7,6)*C*d(-1)),6:468*(9072+C*d(0)),13:T*(252/d(-4)+252/d(-2)+s.Rational(7,6)*C*d(-3)/d(-2))}
def inte_mul(v,w):
 q=[v[0]*w[0],v[0]*w[1],v[1]*w[0],v[1]*w[1]];return min(q),max(q)
def bound(poly,lo,hi):
 ans=(Q(0),Q(0))
 for a in s.Poly(poly,T).all_coeffs():
  a=Q(int(s.numer(a)),int(s.denom(a)));ans=inte_mul(ans,(lo,hi));ans=(ans[0]+a,ans[1]+a)
 return ans
assert (Q(1,2**29)+Q(1,3**29))/(1-Q(1,3**29))<Q(1,10**8)
assert Q(1792,5103)*Q(2,3)**73/(1-Q(1,3**89))<Q(1,10000)
out=[]
for chi,F in FF.items():
 if chi==13:lo,hi=-Q(1,10000),Q(1,10000)
 else:
  t0=Q(1792,5103)*Q(-2,3)**(chi-1);lo,hi=sorted([t0*(1-Q(1,10**8)),t0*(1+Q(1,10**8))])
 F=s.factor(F);nu,de=s.fraction(F);nb,db=bound(nu,lo,hi),bound(de,lo,hi);assert nb[0]>0 or nb[1]<0,(chi,nb);assert db[0]>0 or db[1]<0,(chi,db)
 for other in [DAC]:
  nn,dd=s.fraction(other);nn=s.cancel(nn/T)if chi==13 else nn
  for poly in[nn,dd]:
   rr=bound(poly,lo,hi);assert rr[0]>0 or rr[1]<0,(chi,rr)
 print(chi,F,'SIGN PASS',flush=True);out.append({'chi_or_h':chi,'function':str(F),'interval':[str(lo),str(hi)],'numerator_bounds':list(map(str,nb)),'denominator_bounds':list(map(str,db))})
# Exact G,H derivative and Laurent Z-family derivative.
g0=1-x/6-x*x/6;g1=sum(x**k for k in range(1,7));vars=s.symbols('u1:3')+s.symbols('v1:5');G1=sum(vars[k-1]*x**k for k in range(1,3));H1=sum(vars[k+1]*x**k for k in range(1,5));sol=s.solve(s.Poly(G1+g0*H1-g1,x).coeffs(),vars);G1=s.expand(G1.subs(sol));H1=s.expand(H1.subs(sol))
rem=s.rem(x**7,g0+b*G1,x);Z0=x**7-rem.subs(b,0);Z1=-s.diff(rem,b).subs(b,0);q0=s.div(Z0,g0,x)[0];q1=s.cancel((Z1-q0*G1)/g0);assert s.denom(q1)==1
R1=s.expand(-x*(g1*q0.subs(x,1/x)+g0*q1.subs(x,1/x)-g0*q0.subs(x,1/x)*H1.subs(x,1/x))-9870*(x-x**7))
print('high derivative',[(k,R1.coeff(x,k))for k in range(4,8)],flush=True);assert [R1.coeff(x,k)for k in range(4,8)]==[-504,-546,-468,9072]
open(Path(__file__).with_name('boundary_cubic_certificate_v1.json'),'w').write(json.dumps({'rational_nonvanishing':out,'high_derivative':[-504,-546,-468,9072]},indent=2))
