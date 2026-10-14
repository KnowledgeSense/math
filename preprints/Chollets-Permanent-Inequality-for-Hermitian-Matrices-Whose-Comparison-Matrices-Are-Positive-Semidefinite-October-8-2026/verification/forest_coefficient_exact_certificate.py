import sympy as S
from itertools import permutations,combinations
from math import factorial
import json

def permanent(A):
 n=A.rows
 return S.expand(sum(S.prod(A[i,p[i]] for i in range(n)) for p in permutations(range(n))))
def squareabs(z):return S.simplify(z*S.conjugate(z))
def edgepatterns(E,m):
 def rec(i,left,mu):
  if i==E:yield tuple(mu);return
  for v in range(left+1):yield from rec(i+1,left-v,mu+[v])
 yield from rec(0,m,[])

def one_case(m,edges,d,z,a):
 B=S.diag(*d);E=[]
 for i,j,w,phase in edges:
  h=S.zeros(m,1);h[i]=1;h[j]=S.conjugate(phase)
  B+=w*h*h.conjugate().T;E.append((i,j,S.Rational(w),h))
 z=S.Matrix(z);t=S.symbols('t',real=True)
 direct=S.Poly(permanent(B+t*z*z.conjugate().T/a),t)
 sums=[S.Integer(0)]*(m+1);seen={'all':0,'overfull':0,'admissible':0,'repeated_edges':0,'unicyclic_components':0,'zero_mass_patterns':0};maxsum=S.Integer(0)
 for mu in edgepatterns(len(E),m):
  seen['all']+=1;parent=list(range(m))
  def find(i):
   while parent[i]!=i:i=parent[i]
   return i
  def union(i,j):parent[find(i)]=find(j)
  for e,c in enumerate(mu):
   if c:union(E[e][0],E[e][1])
  comps={}
  for i in range(m):comps.setdefault(find(i),[]).append(i)
  W=S.prod(E[e][2]**c/S.Integer(factorial(c)) for e,c in enumerate(mu));Dprod=S.Integer(1);rr=[];good=True
  if any(c>1 for c in mu):seen['repeated_edges']+=1
  for verts in comps.values():
   inds=[e for e,c in enumerate(mu) if c and E[e][0] in verts]
   cols=[E[e][3][verts,:] for e in inds for _ in range(mu[e])]
   if len(cols)>len(verts):seen['overfull']+=1;good=False;break
   ET=S.Matrix.hstack(*cols) if cols else S.zeros(len(verts),0)
   if len(cols)==len(verts):
    seen['unicyclic_components']+=1;W*=squareabs(permanent(ET));continue
   assert len(cols)==len(verts)-1
   DT=sum(d[i] for i in verts)
   if DT==0:
    assert all(z[i]==0 for i in verts);seen['zero_mass_patterns']+=1;good=False;break
   for k in range(len(verts)):
    co=ET.copy();co.row_del(k);assert squareabs(permanent(co))==1
   RT=squareabs(permanent(ET.row_join(z[verts,:])))/a
   rr.append(S.cancel(RT/DT));Dprod*=DT
  if not good:continue
  seen['admissible']+=1;rs=sum(rr);assert rs<=1;maxsum=max(maxsum,rs)
  ek=[S.Integer(1)]+[sum(S.prod(rr[i] for i in I) for I in combinations(range(len(rr)),k)) for k in range(1,len(rr)+1)]
  for k,v in enumerate(ek):sums[k]+=W*Dprod*factorial(k)*v
  for k in range(1,len(ek)):assert factorial(k)*ek[k]<=ek[1]<=1
 checks=[S.simplify(sums[k]-direct.nth(k))==0 for k in range(m+1)]
 assert all(checks)
 beta=[S.simplify(direct.nth(k)) for k in range(m+1)]
 assert all(0<=q<=beta[1]<=beta[0] for q in beta[1:])
 return {'m':m,'edge_count':len(edges),'beta':[str(q) for q in beta],'coefficient_identities':checks,'patterns':seen,'max_component_mass':str(maxsum)}

# Complex phases, slack, triangles, 4-cycles and repeated-edge terms.
r=[]
r.append(one_case(4,[(0,1,2,1),(0,2,5,S.Rational(3,5)+S.Rational(4,5)*S.I),(0,3,1,-1),(1,2,3,S.I),(1,3,2,-S.I),(2,3,5,-S.Rational(3,5)+S.Rational(4,5)*S.I)],[6,3,2,1],[3+4*S.I,2*S.I,-1,1],9))
# Zero diagonal-root mass, zero first-row entries and nonnegative slack.
r.append(one_case(3,[(0,1,2,-1),(1,2,1,S.I)],[0,2,1],[0,1,1],2))
print(json.dumps({'status':'PASS','scope':'Exact rational/complex verification of the forest coefficient identity and scalar mass bounds; analytic proof is separate','cases':r},indent=2))
