"""Exact algebra checks for the full proof. These do not replace analytic audits."""
import sympy as s,json
from pathlib import Path
checks=[]
def check(name,expr):
 assert s.factor(expr)==0,(name,expr);checks.append(name)
a,b,c,x,y,z,v,w,q,theta=s.symbols('a b c x y z v w q theta')
S=s.Matrix([[a,b],[b,c]]);T=s.Matrix([[x,y],[y,z]]);I=s.eye(2);B=(I+2*S*T).inv();ST=B*S;vv=s.Matrix([v,w])
for i in range(2):
 for j in range(2):check(f'resolvent_{i}{j}',(T-2*T*ST*T-T*B)[i,j])
check('TB_symmetric',(T*B)[0,1]-(T*B)[1,0])
A=(vv.T*T*B*vv)[0]
rhs=-q*(vv.T*T*vv)[0]+2*q*(vv.T*T*ST*T*vv)[0]+2*theta*A*A
check('rank_one_ODE',rhs-(-q*A+2*theta*A*A))
# Generic 2-by-2 rank-one subtraction identity: its determinant vanishes.
O=s.Matrix([[a,b],[b,c]]);den=(vv.T*O.inv()*vv)[0];O0=O-vv*vv.T/den
check('rank_drop_determinant',O0.det())
# Independent W-coordinate operator check in a regularized (2,1) partition.
u0,u1,u2,u3,u4,u5=s.symbols('u0:6');W=s.Matrix([[u0,u1,u2],[u1,u3,u4],[u2,u4,u5]])
A1=W[:2,:2]+s.diag(1,2);A2=s.Matrix([[u5+3]]);powers=[s.Rational(2,5),s.Rational(7,3)]
logf=powers[0]*s.log(A1.det())+powers[1]*s.log(A2.det())
coord={(0,0):u0,(0,1):u1,(1,0):u1,(0,2):u2,(2,0):u2,(1,1):u3,(1,2):u4,(2,1):u4,(2,2):u5}
def gr(expr,i,j):return s.diff(expr,coord[i,j])*(1 if i==j else s.Rational(1,2))
point={u0:6,u1:1,u2:2,u3:5,u4:-1,u5:7};WW=W.subs(point);AA=[A1.subs(point),A2.subs(point)];D=s.diag(powers[0]*AA[0].inv(),powers[1]*AA[1].inv())
mat=[]
for ids,pow,Ai in zip([(0,2),(2,3)],powers,AA):
 Wj=WW[ids[0]:ids[1],ids[0]:ids[1]];inv=Ai.inv();h=s.trace(inv*Wj);Tau=inv*Wj*inv;mat.append(pow*((q-h)*inv-Tau))
expected=s.diag(*mat)+2*D*WW*D
for k,V in enumerate([s.Matrix([1,0,0]),s.Matrix([0,1,0]),s.Matrix([0,0,1]),s.Matrix([1,1,0]),s.Matrix([1,0,1]),s.Matrix([0,1,1])]):
 H=V*V.T;rr=0
 for i in range(3):
  for j in range(3):
   rr+=q*H[j,i]*gr(logf,i,j).subs(point)
   for u in range(3):
    for l in range(3):
     ratio=(gr(gr(logf,u,l),i,j)+gr(logf,i,j)*gr(logf,u,l)).subs(point)
     rr+=2*WW[i,u]*H[l,j]*ratio
 check(f'real_q_operator_direction_{k}',rr-(V.T*expected*V)[0])
out={'status':'PASS','number_of_exact_identities':len(checks),'checks':checks,'scope':'symbolic resolvent/ODE/rank-drop identities and real-q operator coefficient checks; no analytic boundary claims automated'}
Path(__file__).with_name('full_real_shape_exact_certificate.json').write_text(json.dumps(out,indent=2));print(json.dumps(out))
