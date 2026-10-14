"""Standalone exact direct Jacobian verification for one finite seed.
Depends only on Python, NumPy, and FINITE_SEED_RATIONAL_DATA_v1.json.
No star opening, compact surrogate, or prior audit code is imported.
"""
from pathlib import Path
from fractions import Fraction as F
import numpy as np
import math,itertools,json,hashlib,time
HERE=Path(__file__).resolve().parent
DATA=HERE/'FINITE_SEED_RATIONAL_DATA_v1.json'
data=json.loads(DATA.read_text());P=data['prime']
assert all(P%k for k in range(2,math.isqrt(P)+1))
def md(x):
 x=F(x);assert x.denominator%P
 return x.numerator*pow(x.denominator,-1,P)%P

def rref(A):
 A=np.array(A,dtype=np.int64,copy=True)%P;m,n=A.shape;r=0;piv=[];det=1
 for j in range(n):
  ids=np.flatnonzero(A[r:,j])
  if not len(ids):continue
  k=r+int(ids[0])
  if k!=r:A[[k,r]]=A[[r,k]];det=-det
  z=int(A[r,j]);det=det*z%P;A[r]=A[r]*pow(z,-1,P)%P
  col=A[:,j].copy();col[r]=0;A=(A-col[:,None]*A[r])%P
  piv.append(j);r+=1
  if r==m:break
 return A,piv,det%P

def rank(A):return len(rref(A)[1])
def kernel(A):
 R,piv,_=rref(A);free=[i for i in range(A.shape[1])if i not in piv];N=np.zeros((A.shape[1],len(free)),dtype=np.int64)
 N[free,np.arange(len(free))]=1
 N[piv]=-R[:len(piv),free]%P
 assert not np.any(A@N%P)
 return N

n=data['n'];s=data['s'];d=data['d'];assert (n,d,s)==(13,11,14)
nu=np.array([[md(x)for x in row]for row in data['plane_normals']],dtype=np.int64)
stars=np.array([[md(x)for x in row]for row in data['star_points']],dtype=np.int64)
triples=[tuple(T)for T in data['star_triples']];assert triples==list(itertools.combinations(range(n),3))
L=len(triples);edges=list(itertools.combinations(range(n),2));M=len(edges);ei={ab:i for i,ab in enumerate(edges)}
ellstars=(1+stars@nu.T)%P
for T,row in zip(triples,ellstars):assert set(np.flatnonzero(row==0))==set(T)
assert all(rank(nu[list(T)])==3 for T in triples)
assert len(set(map(tuple,stars)))==L
# Independently repeat all exact rational incidence statements supplied in the data.
Qnu=[[F(x)for x in row]for row in data['plane_normals']]
for T,row in zip(triples,data['star_points']):
 q=[F(x)for x in row]
 assert all((1+sum(x*y for x,y in zip(v,q))==0)==(j in T)for j,v in enumerate(Qnu))
out=[]
for lam,B in data['auxiliary_points'].items():
 start=time.monotonic();aux=np.array([[md(x)for x in row]for row in B],dtype=np.int64)
 assert len(set(map(tuple,np.vstack((stars,aux)))))==L+s
 assert rank(np.c_[np.ones(s,dtype=np.int64),aux])==4
 ell=(1+aux@nu.T)%P;assert np.all(ell)
 E=np.empty((s,M),dtype=np.int64);G=np.empty((s,M,3),dtype=np.int64);V=np.empty((s,L),dtype=np.int64)
 for j in range(s):
  invell=np.array([pow(int(x),-1,P)for x in ell[j]],dtype=np.int64);prod=1
  for x in ell[j]:prod=prod*int(x)%P
  weighted=nu*invell[:,None]%P;total=weighted.sum(axis=0)%P
  for z,(a,b) in enumerate(edges):
   E[j,z]=prod*int(invell[a])%P*int(invell[b])%P
   G[j,z]=int(E[j,z])*(total-weighted[a]-weighted[b])%P
  for z,(a,b,c) in enumerate(triples):V[j,z]=prod*int(invell[a])%P*int(invell[b])%P*int(invell[c])%P
 assert rank(E)==s
 K=kernel(E);m=K.shape[1];assert m==64
 J=np.zeros((s*m,3*(L+s)),dtype=np.int64)
 for z,T in enumerate(triples):
  for j,k in enumerate(T):
   ab=tuple(a for a in T if a!=k);J[:,3*z+j]=(-V[:,z,None]*K[ei[ab]][None,:]%P).reshape(-1)
 for j in range(s):J[j*m:(j+1)*m,3*L+3*j:3*L+3*j+3]=K.T@G[j]%P
 globals=np.zeros((J.shape[1],4),dtype=np.int64)
 for z,T in enumerate(triples):globals[3*z:3*z+3,:3]=nu[list(T)];globals[3*z:3*z+3,3]=-1
 for j in range(s):globals[3*L+3*j:3*L+3*j+3,:3]=np.eye(3,dtype=np.int64);globals[3*L+3*j:3*L+3*j+3,3]=aux[j]
 assert rank(globals)==4 and not np.any(J@globals%P)
 _,piv,det=rref(J);assert len(piv)==896 and det
 # Small contractions and rref products are bounded far below signed int64.
 bound=max(J.shape)*(P-1)**2;assert bound<2**63
 record={'parameter':lam,'prime':P,'evaluation_rank':s,'J_shape':list(J.shape),'J_rank':len(piv),'kernel_dimension':J.shape[1]-len(piv),'four_global_motions_verified':True,'max_integer_contraction_bound':bound,'rank_witness_column_indices':piv,'rank_witness_determinant_mod_prime':det,'J_sha256':hashlib.sha256(J.astype('<i8').tobytes()).hexdigest(),'K_sha256':hashlib.sha256(K.astype('<i8').tobytes()).hexdigest(),'elapsed_seconds':time.monotonic()-start}
 out.append(record);print(lam,J.shape,len(piv),det,flush=True)
result={'scope':'Finite exact direct certificate only: general degree 11, position 14 has kernel 4. No all-degree H3 or all-postulation conclusion is encoded.','data_sha256':hashlib.sha256(DATA.read_bytes()).hexdigest(),'source_sha256':hashlib.sha256(Path(__file__).read_bytes()).hexdigest(),'exact_rational_geometry_and_modular_geometric_open_verified':True,'prime_verified':True,'cases':out}
(HERE/'verify_direct_rational_seed_v1_execution.json').write_text(json.dumps(result,indent=2)+'\n')
