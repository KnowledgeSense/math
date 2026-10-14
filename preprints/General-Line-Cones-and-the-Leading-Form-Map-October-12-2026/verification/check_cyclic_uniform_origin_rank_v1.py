#!/usr/bin/env python3
"""Exact standalone checks for the uniform origin-rank degeneration.
Symbolic identities support the written all-n proof. Modular Taylor checks
are additional finite consistency checks, not an extrapolation in n.
"""
import itertools,json,hashlib
from fractions import Fraction as Q
import sympy as S
from pathlib import Path
u,b,D,E,x,y,L=S.symbols('u b D E x y L')
a=-S.Rational(1,6); g=1+a*u+a*u*u; h=u*u+a*u+a
G=g+b*sum(u**j for j in range(1,7)); q=u**4*h+b*sum(u**j for j in range(6))
P=S.div(-u**7*G,q,u)[0]; P0=S.expand(P.subs(b,0));P1=S.expand(S.diff(P,b).subs(b,0))
r0=-u**3*g/h; T=S.series(r0,u,0,15).removeO().expand()
roots=[S.Rational(1,2),-S.Rational(1,3)];res=[-S.Rational(21,160),-S.Rational(56,1215)]
assert S.cancel(r0-P0-sum(R/(u-z)for R,z in zip(res,roots)))==0
cs=[1,a-1,(L+1)*(a-1)/a,(L*a*a-2*L*a+2*L-2*a+2)/a]
aa=S.symbols('a');cgeneral=[1,aa-1,(L+1)*(aa-1)/aa,(L*aa*aa-2*L*aa+2*L-2*aa+2)/aa]
ser=S.series((1+aa*u+aa*u*u)*(1+u+u*u+u**3)**L*(1+u+u*u/aa)**(-L-1),u,0,4).removeO().expand()
for j in range(4): assert S.simplify(ser.coeff(u,j)-cgeneral[j])==0
pos={0:([1,3,7],38329200),1:([0,3,7],38329200),2:([0,3,7],32853600),3:([0,1,7],-26044200),4:([0,1,3],119700),5:([0,1,7],-32853600),6:([0,1,3],-421200)}
for chi,(cols,C)in pos.items():
 A=S.Matrix([[D*roots[0]**(-j-e)+E*roots[1]**(-j-e)for e in cols]for j in [1,3,7]])
 Z=S.Matrix([[(P0 if chi<3 else P1).coeff(u,chi+j+e)for e in cols]for j in [1,3,7]])
 val=S.factor((A+Z).det()if chi<3 else sum(Z[i,j]*A.cofactor(i,j)for i in range(3)for j in range(3)))
 assert S.simplify(val-C*D*E)==0,(chi,val)
neg={1:([0,1,3],15120*x*y-112*x-2268*y,5),2:([0,1,3],21952*x-250047*y,1620),3:([0,1,3],3136*x-35721*y,1620),4:([0,1,3],S.Integer(-49),11664),5:([0,1,7],1015-28672*x-413343*y,233280),6:([0,1,3],S.Integer(343),419904),7:([0,1,3],S.Integer(49),419904),8:([0,1,7],S.Integer(343),1259712),9:([0,1,7],S.Integer(343),15116544),10:([0,1,7],S.Integer(343),544195584),11:([0,1,7],S.Integer(49),544195584)}
for hh,(cols,num,den)in neg.items():
 A=S.Matrix([[sum(R*z**(hh-j-e-1)/(1-v)for R,z,v in zip(res,roots,[x,y]))+(T.coeff(u,j+e-hh)if j+e-hh>=0 else 0)for e in cols]for j in [1,3,7]])
 assert S.cancel(A.det()-num/(den*(x-1)*(y-1)))==0,hh
assert Q(2,3)**29<Q(1,1000)and Q(1,2)**29<Q(1,1000)and Q(1,3)**29<Q(1,1000)
assert Q(2268+15120,1000)<112 and Q(250047,1000)<21952 and Q(35721,1000)<3136 and Q(28672+413343,1000)<1015

def isprime(p):return p>=2 and all(p%d for d in range(2,int(p**.5)+1))
def prime_root(n,start):
 for p in range(((start+n-1)//n)*n+1,1000000,n):
  if not isprime(p):continue
  for g0 in range(2,p):
   w=pow(g0,(p-1)//n,p)
   if pow(w,n,p)==1 and all(pow(w,n//d,p)!=1 for d in range(2,n+1)if n%d==0 and isprime(d)):return p,w
 raise ValueError('prime search exhausted')
def modq(q,p):q=Q(q);return q.numerator*pow(q.denominator,-1,p)%p
def mp(z,k,p):return pow(z,k,p)if k>=0 else pow(pow(z,-1,p),-k,p)
def predicted(n,chi,p):
 U=[modq(Q(1,2),p),modq(Q(-1,3),p)];R=[modq(Q(-21,160),p),modq(Q(-56,1215),p)];k=n-chi
 ds=[R[i]*mp(U[i],k-1,p)*pow((1-pow(U[i],n,p))%p,-1,p)%p for i in range(2)]
 if chi<7:
  cols,C=pos[chi];return cols,int(chi>=3),C*ds[0]*ds[1]%p
 if chi<=n-15 or n-14<=chi<=n-12:
  kk=k-14;ell=(kk+6)//4;r=4*ell-kk-3;ap=modq(Q(-1,6),p)
  cv=cs[r].subs(L,ell)if hasattr(cs[r],'subs')else cs[r]
  gamma=((-1)**(ell+1))*mp(ap,-ell-1,p)*modq(cv,p)%p
  return [0,1,7],ell,150*ds[0]*ds[1]*gamma%p
 hh=n-chi;cols,num,den=neg[hh];xx=pow(U[0],n,p);yy=pow(U[1],n,p)
 return cols,0,int(num.subs({x:xx,y:yy}))%p*pow(den*(xx-1)*(yy-1)%p,-1,p)%p

def mul(A,B,m,p):
 C=[0]*(m+1)
 for i,a0 in enumerate(A):
  for j,b0 in enumerate(B[:m+1-i]):C[i+j]=(C[i+j]+a0*b0)%p
 return C

def detseries(A,m,p):
 out=[0]*(m+1)
 for perm in itertools.permutations(range(3)):
  sg=(-1)**sum(perm[i]>perm[j]for i in range(3)for j in range(i+1,3));v=[1]+[0]*m
  for i in range(3):v=mul(v,A[i][perm[i]],m,p)
  out=[(z+sg*v0)%p for z,v0 in zip(out,v)]
 return out
checks=[]
for n in [29,30,31,37,45,61,89]:
 start=32000
 while True:
  p,w=prime_root(n,start);start=p+1
  try:pred=[predicted(n,chi,p)for chi in range(n)]
  except ValueError:continue
  if all(v[2]for v in pred):break
 m=max(v[1]for v in pred);ts=[pow(w,i,p)for i in range(n)];ap=modq(Q(-1,6),p)
 f0=[(1+(ap-1)*t-ap*pow(t,3,p))%p for t in ts];f1=[(t-pow(t,7,p))%p for t in ts]
 assert all(f0[i]for i in range(1,n))
 rr=[[-1]+[0]*m]
 for i in range(1,n):
  inv=pow(f0[-i],-1,p);vals=[f0[i]*inv%p]
  for j in range(1,m+1):vals.append(((f1[i]if j==1 else 0)-f1[-i]*vals[-1])*inv%p)
  rr.append(vals)
 av=pow(n,-1,p);lam=[[sum(rr[i][j]*mp(ts[i],-k,p)for i in range(n))*av%p for j in range(m+1)]for k in range(n)]
 records=[]
 for chi,(cols,order,lead)in enumerate(pred):
  A=[[lam[(chi+j+e)%n][:order+1]for e in cols]for j in [1,3,7]];det=detseries(A,order,p)
  assert det==[0]*order+[lead],(n,chi,cols,order,det,lead)
  records.append({'chi':chi,'columns':cols,'order':order,'leading_residue':lead})
 checks.append({'n':n,'p':p,'omega':w,'characters':records})
out={'scope':'Symbolic all-n identities for cyclic origin ranks and additional finite Taylor consistency checks. The manuscript proves the first-opening rank in Section 7 and Appendix A.','symbolic_identities':{'residue_coefficients':[str(v)for v in cgeneral],'P0':str(P0),'P1':str(P1),'positive_boundaries':7,'negative_boundaries':11,'nonvanishing_bounds':'exact rational inequalities at n>=29'},'modular_taylor_checks':checks,'total_characters':sum(z['n']for z in checks),'all_pass':True}
path=Path(__file__).with_suffix('.json');path.write_text(json.dumps(out,indent=2)+'\n');print(json.dumps({'path':str(path),'sha256':hashlib.sha256(path.read_bytes()).hexdigest(),'total_characters':out['total_characters'],'all_pass':True}))
