#!/usr/bin/env python3
"""Standalone finite composition certificate for n=29,...,88.
Uses NumPy and the standard library only. Mathematical interpretation depends
on the separately frozen exact quadratic-opening reduction.
"""
import numpy as np,json,hashlib,time
from pathlib import Path

def isprime(p):return p>=2 and all(p%d for d in range(2,int(p**.5)+1))
def prime(n,start=32000):
 p=((start+n-1)//n)*n+1
 while not isprime(p):p+=n
 return p

def generator(p,n):
 ds=[d for d in range(2,n+1)if n%d==0 and isprime(d)]
 for z in range(2,p):
  w=pow(z,(p-1)//n,p)
  if all(pow(w,n//d,p)!=1 for d in ds):return w
 raise ValueError('no generator')

def rref(A,p):
 A=np.array(A,dtype=np.int64)%p;row=0;cols=[]
 for j in range(A.shape[1]):
  z=next((i for i in range(row,len(A))if A[i,j]),None)
  if z is None:continue
  A[[row,z]]=A[[z,row]];A[row]=A[row]*pow(int(A[row,j]),-1,p)%p
  for i in range(len(A)):
   if i!=row and A[i,j]:A[i]=(A[i]-int(A[i,j])*A[row])%p
  cols.append(j);row+=1
  if row==len(A):break
 return A,cols

def det(A,p):
 A=np.array(A,dtype=np.int64)%p;d=1
 for j in range(len(A)):
  z=next((i for i in range(j,len(A))if A[i,j]),None)
  if z is None:return 0
  if z!=j:A[[j,z]]=A[[z,j]];d=-d
  pv=int(A[j,j]);d=d*pv%p;iv=pow(pv,-1,p)
  for i in range(j+1,len(A)):
   if A[i,j]:A[i]=(A[i]-int(A[i,j])*iv%p*A[j])%p
 return d%p

def minor(A,p):
 _,cols=rref(A,p);_,rows=rref(A[:,cols].T,p);d=det(A[np.ix_(rows,cols)],p);assert d
 return {'rank':len(cols),'rows':rows,'columns':cols,'determinant':d,'matrix_shape':list(A.shape),'matrix_sha256':hashlib.sha256(A.astype('<i8').tobytes()).hexdigest()}
def data(n,co=None,p=None):
 if p is None:p=prime(n)
 w=generator(p,n);F=[0,1,3,7];a=np.array([1]+(co if co is not None else[2,3,-6]),dtype=np.int64)%p;t=np.array([pow(w,i,p)for i in range(n)],dtype=np.int64);ft=np.array([[pow(w,(-k*j)%n,p)for j in range(n)]for k in range(n)],dtype=np.int64);f=np.array([sum(int(aa)*pow(int(v),e,p)for e,aa in zip(F,a))%p for v in t],dtype=np.int64);assert all(f[1:]);r=np.array([-1]+[int(f[j])*pow(int(f[-j]),-1,p)%p for j in range(1,n)],dtype=np.int64)%p;lam=ft@r%p;assert all(lam)
 psi=np.zeros((n,3),dtype=np.int64);phi=np.zeros((n,2),dtype=np.int64);fp=sum(e*int(aa)for e,aa in zip(F,a))%p
 for j in range(1,n):
  z=int(t[j]);d1=(z-pow(z,7,p))%p;d3=(pow(z,3,p)-pow(z,7,p))%p;iv=pow(int(f[j]),-1,p);psi[j]=[d1*d1*iv%p,d1*d3*iv%p,d3*d3*iv%p];phi[j]=[int(a[1])*(z-1)*iv%p,int(a[2])*(pow(z,3,p)-1)*iv%p]
 phi[0]=[int(a[1])*pow(fp,-1,p)%p,3*int(a[2])*pow(fp,-1,p)%p];Psi=ft@psi%p;Phi=ft@phi%p
 return n,p,w,F,a,t,f,lam,Psi,Phi

def matrices(geo,chi,detector=True):
 n,p,w,F,a,t,f,lam,Psi,Phi=geo;glob=chi in[0,n-1,n-3,n-7];nv=6+glob;B=np.zeros(n,dtype=np.int64)
 for u,e in enumerate(F):
  for v,j in enumerate(F):B[(e-j-chi)%n]=(B[(e-j-chi)%n]+int(a[u])*int(a[v])*int(lam[(-chi-j)%n]))%p
 H=np.zeros((n,nv),dtype=np.int64)
 for j in range(n):
  iv=pow(int(lam[j]),-1,p)
  for v,e in enumerate(F):H[j,v]=int(lam[(chi+j+e)%n])*iv%p
  H[j,4]=-n*int(B[j])*iv%p
 W=Psi.T@H%p*pow(n,-1,p)%p;P=np.zeros((4,nv),dtype=np.int64)
 for j,e in enumerate(F):
  for v,ee in enumerate(F):P[j,v]=lam[(chi+e+ee)%n]
  P[j,4]=-n*int(B[e]);
  if j==0:P[j,5]=-int(lam[0])
  if chi==0:P[j,6]=-int(lam[e])*pow(2,-1,p)%p;P[j,4]=(P[j,4]+int(lam[e])*n*pow(2,-1,p))%p
  elif glob:
   ee=next(v for v in F[1:]if(chi+v)%n==0);ae=int(a[F.index(ee)]);P[j,6]=-int(lam[e]);P[j,4]=(P[j,4]+int(lam[e])*n*ae)%p
 if chi in[(n-k)%n for k in [2,4,6,8,10,14]]:
  row=np.zeros(nv,dtype=np.int64);row[4]=1;P=np.vstack((P,row))
 P%=p
 if not detector:return P,W
 TT=np.array([[int(Phi[(k-chi)%n,0])*int(Phi[-k%n,0]),int(Phi[(k-chi)%n,0])*int(Phi[-k%n,1])+int(Phi[(k-chi)%n,1])*int(Phi[-k%n,0]),int(Phi[(k-chi)%n,1])*int(Phi[-k%n,1])]for k in range(n)],dtype=np.int64)%p;O=np.zeros_like(TT)
 for u,e in enumerate(F):
  for v,j in enumerate(F):O=(O+int(a[u])*int(a[v])*np.roll(TT,e-j,axis=0))%p
 diff={(e-j)%n for e in F for j in F};support=diff|{(chi+k)%n for k in diff}
 for e in F:
  for j in F:
   if(e+j+chi)%n==0:support|={(k-j)%n for k in diff}
 outside=[k for k in range(n)if k not in support]
 return P,W,O[outside],outside

def poly_gcd(A,B,p):
 def trim(C):
  while len(C)>1 and C[-1]%p==0:C.pop()
  return [v%p for v in C]
 A=trim(A[:]);B=trim(B[:])
 while B!=[0]:
  R=A[:]
  while len(R)>=len(B)and R!=[0]:
   z=R[-1]*pow(B[-1],-1,p)%p;k=len(R)-len(B)
   for i,v in enumerate(B):R[k+i]=(R[k+i]-z*v)%p
   R=trim(R)
  A,B=B,R
 return [(v*pow(A[-1],-1,p))%p for v in A]

def run():
 result=[];start=time.monotonic()
 for n in range(29,89):
  low=32000
  while True:
   p=prime(n,low);low=p+1
   try:geo=data(n,p=p)
   except (AssertionError,ValueError):continue
   n,p,w,F,a,t,f,lam,Psi,Phi=geo
   gcd=poly_gcd([1,3,3,6,6,6,6],[6,6,6,6,3,3,1],p)
   if gcd!=[1] or (-31)%p==0:continue
   edges=[(0,j)for j in range(1,n)]+[(1,2),(1,3)];E=np.zeros((n+1,n+1),dtype=np.int64)
   for j,(u,v)in enumerate(edges):E[u,j]=pow(int(f[(u-v)%n]),-1,p);E[v,j]=pow(int(f[(v-u)%n]),-1,p);E[n,j]=1
   edet=det(E,p)
   if not edet:continue
   cases=[];failed=False
   for chi in range(n):
    P,W,O,outside=matrices(geo,chi);M=np.vstack((P,O@W%p));pm=minor(P,p);mm=minor(M,p);expected=5 if chi in[(n-k)%n for k in [2,4,6,8,10,14]]else 4
    if pm['rank']!=expected or mm['rank']!=6:failed=True;break
    cases.append({'chi':chi,'origin_minor':pm,'combined_minor':mm,'outside_indices':outside,'moment_matrix_sha256':hashlib.sha256(W.astype('<i8').tobytes()).hexdigest(),'detector_matrix_sha256':hashlib.sha256(O.astype('<i8').tobytes()).hexdigest(),'opening_rank':6-expected})
   if not failed:break
  A=1
  for v in f[1:]:A=A*int(v)%p
  assert A and all(lam) and sum(c['opening_rank']for c in cases)==2*n-6
  record={'n':n,'d':n-2,'s':n+1,'r':n*(n-1)*(n-2)//6+n+1,'p':p,'omega':w,'exact_order_verified':pow(w,n,p)==1 and all(pow(w,n//d,p)!=1 for d in range(2,n+1)if n%d==0 and isprime(d)),'coefficients':[2,3,-6],'reciprocal_residual_gcd':gcd,'f_derivative_at_one':(-31)%p,'incidence_values':f.tolist(),'star_pivot_product_A':A,'fourier_denominators':lam.tolist(),'evaluation_minor':{'edges':edges,'determinant':edet,'matrix_sha256':hashlib.sha256(E.astype('<i8').tobytes()).hexdigest()},'special_kernel':2*n-2,'first_opening_rank':2*n-6,'remaining_kernel':4,'common_coordinate_rank':n*(n-1)*(n-2)//2+3*n-1,'characters':cases};assert record['common_coordinate_rank']==3*record['r']-4;result.append(record)
  print(n,p,'PASS',flush=True)
 out={'scope':'Finite exact composition certificate for every 29<=n<=88; interpretation uses the frozen uniform reductions and new quadratic-opening proof. No uniform moment-gate assertion.','all_pass':True,'degrees':60,'characters':sum(z['n']for z in result),'results':result};path=Path(__file__).with_suffix('.json');path.write_text(json.dumps(out,indent=2)+'\n');print(json.dumps({'path':str(path),'sha256':hashlib.sha256(path.read_bytes()).hexdigest(),'elapsed_seconds':time.monotonic()-start,'all_pass':True}))
if __name__=='__main__':run()
