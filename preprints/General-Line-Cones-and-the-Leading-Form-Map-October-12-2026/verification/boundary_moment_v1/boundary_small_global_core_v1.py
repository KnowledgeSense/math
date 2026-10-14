from pathlib import Path
from boundary_symbolic_core_v1 import *
@lru_cache(None)
def invden(sm,j,depth):
 delta=(sm-j+6)//6;ds=[den(sm,j,delta+i)for i in range(depth+1)];iv=[1/ds[0]]
 for k in range(1,depth+1):iv.append(s.cancel(-sum(ds[i]*iv[k-i]for i in range(1,k+1))/ds[0]))
 return delta,iv
@lru_cache(None)
def ratio_den(sm,m,j,k):
 dm=(sm-m+6)//6;dj=(sm-j+6)//6;depth=k-dm+dj
 if depth<0:return s.Integer(0)
 _,iv=invden(sm,j,depth)
 return s.factor(sum(den(sm,m,dm+i)*iv[depth-i]for i in range(depth+1)))
def divint(num,denom,k):
 v=next(i for i,x in enumerate(denom)if x);depth=k+v
 if depth<0:return 0
 iv=[s.Rational(1,denom[v])]
 for m in range(1,depth+1):iv.append(-sum(denom[v+i]*iv[m-i]for i in range(1,m+1))/denom[v])
 return sum(num[depth-i]*iv[i]for i in range(depth+1))

def moment_unscaled(h,V,cols,rr,sm,k,project=False):
 total=0;terms=[]
 # Fourier indices beyond this cannot affect order k, since ratio valuation >=-2.
 for j in range(0,14+6*(k+3)):
  if project and j==8:continue
  ps=([psi[rr][ell].get(j,0)for ell in range(S+1)] if rr<3 else [psi[1][ell].get(j,0)-psi[0][ell].get(j,0)for ell in range(S+1)] if rr==3 else [psi[2][ell].get(j,0)-2*psi[1][ell].get(j,0)+psi[0][ell].get(j,0)for ell in range(S+1)])
  if project:
   # rr=1 minus psi_1(8)/psi_0(8) times row0
   rat=[divint([psi[1][ell].get(8,0)for ell in range(S+1)],[psi[0][ell].get(8,0)for ell in range(S+1)],ell)for ell in range(S+1)]
   ps=add(ps,neg(mul(rat,[psi[0][ell].get(j,0)for ell in range(S+1)])))
  vv=next((i for i,x in enumerate(ps)if x),999)
  if j<=7:
   num=make_num(h,V,cols,j);num=mul(ps,num);val=divint(num,L[j],k)
  else:
   assert j-h>=8 or project and j>8 or h==0
   val=0
   for ii,e in enumerate(F):
    npoly=mul(ps,V[ii]);nv=next((i for i,x in enumerate(npoly)if x),999)
    if nv>k+2:continue
    val+=sum(npoly[ell]*ratio_den(sm,j-h+e,j,k-ell)for ell in range(nv,min(S,k+2)+1))
  if val!=0:terms.append((j,val))
 return s.factor(sum(v for j,v in terms))

def h1kernel():
 cols,cc,val,ker=orig(1)
 C=[]
 for V in ker[:2]:C.append(make_num(1,V,cols,8))
 good=[add(mul(ker[0][i],C[1]),neg(mul(ker[1][i],C[0])))for i in range(6)]
 vv=min(next((i for i,x in enumerate(v)if x),999)for v in good);good=[v[vv:]+[0]*vv for v in good]
 assert not any(make_num(1,good,cols,8)[:S-vv+1])
 return cols,good

def h0kernels():
 cols=[1,2,3,4,5];M=[]
 for j in[1,3]:
  row=[L[j+e]for e in F[1:]];cb=[0]*(S+1)
  for ui,u in enumerate(F):
   for vi,v in enumerate(F):
    if u-v==j:cb=add(cb,mul(mul(A[ui],A[vi]),L[-v]))
  row+=[add(neg(cb),[s.Rational(x,2)for x in L[j]]),[-s.Rational(x,2)for x in L[j]]];M.append(row)
 best=None
 for cc in itertools.combinations(range(5),2):
  dd=determinant([[row[k]for k in cc]for row in M]);vv=next((i for i,x in enumerate(dd)if x),999)
  if best is None or vv<best[0]:best=(vv,cc,dd)
 val,cc,dd=best;out=[]
 for free in range(5):
  if free in cc:continue
  V=[[0]*(S+1)for k in range(5)];V[free]=dd
  for i,k in enumerate(cc):V[k]=neg(determinant([[row[free]if q==i else row[c]for q,c in enumerate(cc)]for row in M]))
  vv=min(next((i for i,x in enumerate(row)if x),999)for row in V);V=[row[vv:]+[0]*vv for row in V]
  # reinsert z0=0 so common make_num applies.
  out.append([[0]*(S+1)]+V)
 return [0,1,2,3,4,5],cc,val,out

if __name__=='__main__':
 h=int(sys.argv[1]);sm=int(sys.argv[2])if len(sys.argv)>2 else 0
 if h==1:
  cols,V=h1kernel();print('kernel',[(cols[i],v[:7])for i,v in enumerate(V)],flush=True)
  for k in range(-2,5):
   co=moment_unscaled(1,V,cols,1,sm,k,True);print('h1',sm,k,co,flush=True)
   if co!=0:break
 else:
  cols,cc,val,ker=h0kernels();print('piv',cc,val,flush=True);entries={}
  for k in range(-2,4):
   for rr in range(3):
    for ii,V in enumerate(ker):
     co=moment_unscaled(0,V,cols,rr,sm,k);entries[rr,ii,k]=co
     if co:print('entry',rr,ii,k,co,flush=True)
