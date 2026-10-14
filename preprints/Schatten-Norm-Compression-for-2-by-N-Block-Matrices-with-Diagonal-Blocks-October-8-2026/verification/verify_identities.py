#!/usr/bin/env python3
"""Exact algebraic identities for two-row diagonal compression."""
import sympy as s
checks=[]
def eq(label,expr):
 out=s.factor(s.cancel(expr))
 assert out==0,(label,out)
 checks.append(label)
 print('PASS',label,flush=True)

a,b,c,k,x1,x2,r,S,T,Z12,A,B,C,q11,q12,q22,u,v,w=s.symbols('a b c k x1 x2 r S T Z12 A B C q11 q12 q22 u v w', nonzero=True,real=True)
beta=k+1
H=s.Matrix([[a,c],[c,b]])
x=s.Matrix([x1,x2]); Z=s.Matrix([[S,Z12],[Z12,T]])
K=beta*s.diag(*[(H*x)[i]/x[i] for i in range(2)])-H
Ki=K.inv(); D=s.factor(K.det()*x1*x2)
Dclaim=k*(beta*a*c*x1**2+(k*a*b+(k+2)*c**2)*x1*x2+beta*b*c*x2**2)
eq('general denominator',D-Dclaim)
for i in range(2):eq('gauge Kx=kHx '+str(i),(K*x-k*H*x)[i])
y=Z*x; h=s.factor((y.T*Ki*y)[0])
P=(k*b*x1*x2+beta*c*x1**2)*y[0]**2+2*c*x1*x2*y[0]*y[1]+(k*a*x1*x2+beta*c*x2**2)*y[1]**2
eq('general quartic numerator',h*D-P)
eq('first axis limit',s.limit(h,x2,0)-x1**2*S**2/(k*a))
eq('second axis limit',s.limit(h,x1,0)-x2**2*T**2/(k*b))
y1,y2=s.symbols('y1 y2',real=True); Y=s.Matrix([y1,y2]); X2=s.Matrix([-beta*y1*y1/x1,-beta*y2*y2/x2])
M2=X2*x.T+x*X2.T+2*Y*Y.T
eq('Hessian K term',s.Rational(1,2)*(H*M2).trace()+(Y.T*K*Y)[0])

# Compute residual from the inverse and raw ray weights.
hr=h.subs({x1:1,x2:r,Z12:0}); Dr=D.subs({x1:1,x2:r})
raw=q11*S*S+2*q12*S*T+q22*T*T-(A-C/r)*S*S/(k*a)-(B-C*r)*T*T/(k*b)-C/r*hr
raw=raw.subs({q11:u+A/(k*a),q22:v+B/(k*b),q12:w})
U=s.factor(s.diff(raw,S,2)/2); V=s.factor(s.diff(raw,T,2)/2); W=s.factor(s.diff(s.diff(raw,S),T)/2)
Uc=u+C*c*((k+2)*c+beta*b*r)/(a*Dr)
Vc=v+C*c*(beta*a*r+(k+2)*c*r*r)/(b*Dr)
Wc=w-C*c*r/Dr
for label,e in [('derived U',U-Uc),('derived V',V-Vc),('derived W',W-Wc)]:eq(label,e)
F=s.factor((U*V-W*W)*Dr)
Fc=(u*v-w*w)*Dr+C*c*(u*(beta*a*r+(k+2)*c*r*r)/b+v*((k+2)*c+beta*b*r)/a+2*w*r)+(C*c)**2*(k+2)*r/(a*b*k)
eq('quadratic determinant cancellation',F-Fc)
assert s.Poly(F,r).degree()==2
L=s.expand(F).coeff(r,2)
Lc=(u*v-w*w)*k*beta*b*c+C*c*u*(k+2)*c/b
eq('leading coefficient L',L-Lc)

# Derive spectral q coefficients from two orthogonal projector blocks.
alpha,theta,hp=s.symbols('alpha theta hp',nonzero=True,real=True)
t=s.symbols('t',positive=True)
e=(1-t*hp)/(1-t)
qform=(alpha*(theta*S+(1-theta)*T)**2+alpha*hp*((1-theta)*S+theta*T)**2+2*e*theta*(1-theta)*(S-T)**2)/2
Q11=s.factor(s.diff(qform,S,2)/2); Q22=s.factor(s.diff(qform,T,2)/2); Q12=s.factor(s.diff(s.diff(qform,S),T)/2)
eq('spectral q11',Q11-(alpha*theta**2+alpha*hp*(1-theta)**2+2*e*theta*(1-theta))/2)
eq('spectral q22',Q22-(alpha*(1-theta)**2+alpha*hp*theta**2+2*e*theta*(1-theta))/2)
eq('spectral q12',Q12-theta*(1-theta)*(alpha*(1+hp)-2*e)/2)
aa=t+(1-t)*theta; bb=1-(1-t)*theta
AA=t*hp+(1-t*hp)*theta; BB=1-(1-t*hp)*theta
Cc=(1-t*hp)*(1-t)*theta*(1-theta)
kk=2/alpha
uu=Q11-AA/(kk*aa); vv=Q22-BB/(kk*bb); ww=Q12
Loverc=(uu*vv-ww**2)*kk*(kk+1)*bb+Cc*uu*(kk+2)/bb

def Q(tt,zz):return tt*zz**2-(2*alpha+1+tt)*zz+alpha*(alpha+2)
P1=-(t-1)**2*Q(t,e)
# Under t -> 1/t, t^alpha -> 1/(t*hp), t^(2alpha+1) -> t^3 hp^2.
zrec=(1/(t*hp)-1)/(1/t-1)
P0=t**3*hp**2*(-(1/t-1)**2*Q(1/t,zrec))
Lc_certificate=2*theta**2*(1-theta)**2/(alpha*aa*bb)*((1-theta)*P0+theta*P1)
eq('spectral leading coefficient identity for both signs',Loverc-Lc_certificate)
P1expanded=-alpha**2*(t-1)**2+2*alpha*t*(t-1)*(hp-1)-t**3*hp**2+t*hp*(t*t+2*t-1)-t*t-t+1
eq('expanded P1',P1-P1expanded)

# Upper scalar branch identities and trace sign certificate.
d=alpha+1-(alpha-1)*t; RR=2*alpha/d
Delta=(2*alpha+1+t)**2-4*t*alpha*(alpha+2)
t0=(2*alpha+1)/(2*alpha-1)
eq('upper Q rational bound',Q(t,RR)-alpha**2*(alpha-1)*(alpha+1)*(t-1)**2/d**2)
eq('upper Q at alpha',Q(t,alpha)-alpha*(alpha-1)*(t-1))
eq('upper d at threshold',d.subs(t,t0)-2*alpha/(2*alpha-1))
eq('upper discriminant at one',Delta.subs(t,1)-4)
eq('upper discriminant at threshold',Delta.subs(t,t0)+4*t0*alpha*(alpha-1)*(t0-1))
eq('upper vertex after threshold',2*alpha**2+2*alpha-1-t0-2*alpha*(alpha-1)*(2*alpha+3)/(2*alpha-1))
Eu=s.factor(2*aa*uu/(theta*(1-theta)))
E0=2*t*e-alpha*(1+(2*t-1)*hp); E1=2*e-alpha*(2-t+t*hp)
eq('affine u sign certificate',Eu-((1-theta)*E0+theta*E1))
eq('u endpoint0 trapezoid bound',alpha*t*(1+hp)-alpha*(1+(2*t-1)*hp)+alpha*(1-t)*(1-hp))
eq('u endpoint1 trapezoid bound',alpha*(1+hp)-alpha*(2-t+t*hp)+alpha*(1-t)*(1-hp))

# Lower scalar certificates.
m=s.symbols('m',positive=True)
yy=s.symbols('yy',positive=True)
VM=t*yy**2+(t+1-2*m)*yy+m*(m-2)
YY=m*t**(-(m+1)/2)
RM=t+1-2*m+m*t**(-(m-1)/2)+(m-2)*t**((m+1)/2)
eq('negative alpha substitution',Q(t,-yy).subs(alpha,-m)-VM)
eq('lower substitution Y',s.powsimp(VM.subs(yy,YY)-m*t**(-(m+1)/2)*RM,force=True))
eq('lower R at one',RM.subs(t,1))
eq('lower R derivative at one',s.diff(RM,t).subs(t,1))
eq('lower R second derivative',s.powsimp(s.diff(RM,t,2)-(m*m-1)/4*(m*t**(-(m+3)/2)+(m-2)*t**((m-3)/2)),force=True))
LD=(t+1-2*m)**2-4*t*m*(m-2)
eq('lower discriminant at one',LD.subs(t,1)-4)
eq('lower discriminant at threshold',LD.subs(t,2*m-1)+4*m*(m-2)*(2*m-1))
eq('lower discriminant vertex',2*m*m-2*m-1-(2*m-1)-2*m*(m-2))
rho,dd=s.symbols('rho dd',positive=True)
eq('negative K definiteness factor',k*rho**2+(k+2)*dd**2-2*(k+1)*dd*rho-(rho-dd)*(k*rho-(k+2)*dd))

# Endpoint nonvanishing/inertia identities, derived without choosing signs.
r1,r2=s.symbols('r1 r2',nonzero=True)
eq('equal endpoint offdiagonals factor',r1*Dr.subs(r,r2)-r2*Dr.subs(r,r1)-(r1-r2)*k*(k+1)*c*(a-b*r1*r2))
eq('spectral aA-bB',aa*AA-bb*BB-(2*theta-1)*(1-t*t*hp))
eq('symmetric residual diagonal difference',(U-V).subs({b:a,v:u})-C*c*c*(k+2)*(1-r*r)/(a*Dr.subs(b,a)))
print('ALL PASS:',len(checks),'exact identities')
