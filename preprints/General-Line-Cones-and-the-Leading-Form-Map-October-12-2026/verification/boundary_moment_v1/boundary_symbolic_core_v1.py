from pathlib import Path
import sympy as s,itertools,math,sys,json,time
from functools import lru_cache
N=s.symbols('N',integer=True,positive=True);t=s.symbols('t');F=[0,1,3,7];S=14
# Laurent coefficients of infinite r=-u(1-t A)/(1-t Q).
r=[{1:-1}]
for k in range(1,S+1):
 out={}
 for e,v in r[-1].items():
  for j in range(1,7):out[e-j]=out.get(e-j,0)+v
 if k==1:
  for j in range(1,7):out[j+1]=out.get(j+1,0)+1
 r.append(out)
def l(m):return sum(r[k].get(m,0)*t**k for k in range(S+1))
def tr(expr):return s.Poly(expr,t).trunc(10**100000) if False else s.Poly(s.expand(expr),t)
def coeffs(expr):
 pp=s.Poly(s.expand(expr),t);return [pp.nth(k)for k in range(S+1)]
def mul(a,b):return [sum(a[j]*b[k-j]for j in range(k+1))for k in range(S+1)]
def add(a,b):return [x+y for x,y in zip(a,b)]
def neg(a):return [-x for x in a]
def determinant(M):
 out=[0]*(S+1)
 for pp in itertools.permutations(range(len(M))):
  sign=(-1)**sum(pp[i]>pp[j]for i in range(len(pp))for j in range(i+1,len(pp)))
  row=[1]+[0]*S
  for i,j in enumerate(pp):row=mul(row,M[i][j])
  out=add(out,[sign*x for x in row])
 return out
A=[coeffs(v)for v in [1,-1-t,0,t]]
L={m:coeffs(l(m))for m in range(-20,40)}
@lru_cache(None)
def orig(h):
 glob=h in[0,1,3,7];quad=h in[2,4,6,8,10,14];nc=4+(not quad)+glob
 cols=[0,1,2,3]+([]if quad else[4])+([5]if glob else[])
 M=[]
 for j in [1,3,7]:
  row=[]
  for e in F:row.append(L[j+e-h])
  if not quad:
   cb=[0]*(S+1)
   for ui,u in enumerate(F):
    for vi,v in enumerate(F):
     if u-v==j-h:cb=add(cb,mul(mul(A[ui],A[vi]),L[h-v]))
   cb=neg(cb)
   if glob:cb=add(cb,[s.Rational(x,2) for x in L[j]])if h==0 else add(cb,mul(A[F.index(h)],L[j]))
   row.append(cb)
  if glob:row.append([(-s.Rational(x,2) if h==0 else -x)for x in L[j]])
  M.append(row)
 piv=None
 for cc in itertools.combinations(range(nc),3):
  dd=determinant([[row[k]for k in cc]for row in M]);val=next((i for i,x in enumerate(dd)if x),999)
  if piv is None or val<piv[0]:piv=(val,cc,dd)
 val,cc,dd=piv;out=[]
 for free in range(nc):
  if free in cc:continue
  V=[[0]*(S+1)for k in range(nc)];V[free]=dd
  for i,k in enumerate(cc):
   mm=[[row[free]if q==i else row[c]for q,c in enumerate(cc)]for row in M]
   V[k]=neg(determinant(mm))
  vv=min(next((i for i,x in enumerate(row)if x),999)for row in V);V=[row[vv:]+[0]*vv for row in V]
  # validate through reliable S-vv
  assert all(not any(sum(M[i][j][ell]*V[j][k-ell]for j in range(nc)for ell in range(k+1))for k in range(S-vv+1))for i in range(3))
  out.append(V)
 return cols,cc,val,out
@lru_cache(None)
def C(qshift,d):
 if d<0:return s.Integer(0)
 return s.expand(sum((-1)**i*s.prod(N+qshift-j for j in range(i))/s.factorial(i)*s.prod(N+qshift+d-6*i-1-j for j in range(d-6*i))/s.factorial(d-6*i)for i in range(d//6+1)))
@lru_cache(None)
def den(smod,j,delta):return s.expand(-C(delta,6*delta-smod+j-1)+sum(C(delta-1,6*delta-smod+j-a-7)for a in range(1,7)))
# psi=P/(1-u)/(1-tA), coefficients by infinite positive polynomial convolution.
psi=[]
for e,f in[(1,1),(1,3),(3,3)]:
 pp={e+f:1};pp[e+7]=pp.get(e+7,0)-1;pp[f+7]=pp.get(f+7,0)-1;pp[14]=pp.get(14,0)+1
 dd={j:sum(v for k,v in pp.items()if k<=j)for j in range(14)};ser=[dd]
 for k in range(1,S+1):
  out={}
  for j,v in ser[-1].items():
   for a in range(1,7):out[j+a]=out.get(j+a,0)+v
  ser.append(out)
 psi.append(ser)

def make_num(h,V,cols,j):
 nu=[0]*(S+1)
 for i,e in enumerate(F):nu=add(nu,mul(V[i],L[j+e-h]))
 if 4 in cols:
  cb=[0]*(S+1)
  for ui,u in enumerate(F):
   for vi,v in enumerate(F):
    if j==h+u-v:cb=add(cb,mul(mul(A[ui],A[vi]),L[h-v]))
  nu=add(nu,neg(mul(V[cols.index(4)],cb)))
 return nu

def get_terms(h,V,cols,rr):
 terms=[]
 for j in range(8,h+8):
  nu=make_num(h,V,cols,j);ps=[psi[rr][k].get(j,0)for k in range(S+1)];ss=mul(nu,ps)
  if any(ss):terms.append((j,ss))
 return terms

def coefficient_terms(terms,smod,k):
 out=0
 for j,aa in terms:
  delta=(smod-j+6)//6 # ceil((smod-j+1)/6)
  cval=next((i for i,x in enumerate(aa)if x),999)
  depth=k+delta-cval
  if depth<0:continue
  ds=[den(smod,j,delta+i)for i in range(depth+1)]
  iv=[1/ds[0]]
  for m in range(1,depth+1):iv.append(s.cancel(-sum(ds[i]*iv[m-i]for i in range(1,m+1))/ds[0]))
  out+=sum(aa[k+delta-i]*iv[i]for i in range(depth+1))
 return s.factor(out)

if __name__=='__main__':
 h=int(sys.argv[1]);sm=int(sys.argv[2])if len(sys.argv)>2 else 0
 cols,cc,val,ker=orig(h);print('h',h,'s',sm,'cols',cols,'pivot',cc,val,'ker',len(ker),flush=True)
 for ii,V in enumerate(ker):
  print('kernel',ii,[(cols[i],v[:7])for i,v in enumerate(V)],flush=True)
  for rr in range(3):
   terms=get_terms(h,V,cols,rr)
   for k in range(8):
    co=coefficient_terms(terms,sm,k)
    if co!=0:print('moment',rr,'k',k,'coefficient',co,flush=True);break
