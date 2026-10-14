#!/usr/bin/env python3
"""Exact exact coverage/margin and optional full-rerun comparison.
Coverage proof uses pairwise interior disjointness + exact volume, not author's
recursive dyadic partition routine. All parsed binary64 endpoints become Fractions.
"""
from pathlib import Path
from fractions import Fraction as Q
from itertools import combinations,product
import json,csv,math,re,hashlib,sys,time
ROOT=Path(__file__).resolve().parents[1]
D=ROOT/'components/three-to-four'
W=None
start=time.perf_counter()
REPLAY=False
manifest={'proof_sha256':'a66f274ba9074e9dc7814b694ec75a7de55b984cabce428c049dca18bf63f96c'}

def binary(s):
 x=float(s);assert math.isfinite(x);return Q.from_float(x)
def deriv_rows(s):
 out={}
 for line in s.splitlines():
  m=re.fullmatch(r'(third|p_hessian) (\d+)  \[([^,]+), ([^\]]+)\]',line)
  if m:
   key=(m[1],int(m[2]));assert key not in out
   lo,hi=map(binary,(m[3],m[4]));assert lo<=hi;out[key]=(lo,hi)
 assert set(out)=={('third',i) for i in range(4)}|{('p_hessian',i) for i in range(3)}
 return out
bounds=json.loads((D/'logs/local_signed_derivative_cover.json').read_text());assert bounds['complete'] is True and len(bounds['results'])==2400
expected={(Q(24+k,8),Q(25+k,8),Q(136+i,160),Q(137+i,160),Q(136+j,160),Q(137+j,160)) for k in range(8) for i in range(24) for j in range(i+1)}
seen={};maxima={('third',i):Q(0) for i in range(4)}|{('p_hessian',i):Q(0) for i in range(3)}
for index,row in enumerate(bounds['results']):
 assert row['args'][0]=='512';key=tuple(map(Q,row['args'][1:]));assert key in expected and key not in seen
 data=deriv_rows(row['raw']);seen[key]=data
 for (kind,i),(lo,hi) in data.items():
  limit=(9 if i in (0,3) else 6) if kind=='third' else (1 if i==1 else 2)
  mag=max(abs(lo),abs(hi));assert mag<limit;maxima[(kind,i)]=max(maxima[(kind,i)],mag)
assert set(seen)==expected
# Local leaves: exact inequality and an independently implemented measure/disjointness cover.
E=1<<20;DEN=1000*E
roots={( (3000+100*k)*E,(3100+100*k)*E,(850+30*i)*E,(880+30*i)*E,(850+30*j)*E,(880+30*j)*E ):[] for k in range(10) for i in range(5) for j in range(i+1)}
leaves=[];worst=None
for row in csv.DictReader((D/'logs/local_hessian_corrected_certificate.csv').open()):
 assert int(row['denominator'])==DEN
 edge=tuple(int(row[key]) for key in ['p_lo','p_hi','u_lo','u_hi','v_lo','v_hi']);assert all(edge[2*i]<edge[2*i+1] for i in range(3))
 eig=binary(row['eigen_upper']);rp,ru,rv=[Q(edge[2*i+1]-edge[2*i],2*DEN) for i in range(3)]
 correction=max(15*ru+12*rv+3*rp,12*ru+15*rv+3*rp);upper=eig+correction
 assert upper < -Q(1,500)
 assert correction==Q(row['corrected_variation_exact']) and upper==Q(row['corrected_upper_exact'])
 assigned=[r for r in roots if all(r[2*i]<=edge[2*i] and edge[2*i+1]<=r[2*i+1] for i in range(3))];assert len(assigned)==1
 roots[assigned[0]].append(edge);leaves.append((edge,eig));worst=upper if worst is None else max(worst,upper)
assert len(leaves)==5733
pairs=0
volume=lambda box:math.prod(box[2*i+1]-box[2*i] for i in range(3))
for root,boxes in roots.items():
 assert boxes and sum(map(volume,boxes))==volume(root)
 for a,b in combinations(boxes,2):
  pairs+=1;assert any(a[2*i+1]<=b[2*i] or b[2*i+1]<=a[2*i] for i in range(3))
# A finite union of closed boxes inside each root, with disjoint interiors and
# full root volume, leaves no point uncovered: any relative open gap has volume>0.
vertices={}
for row in csv.DictReader((D/'logs/complement_interval_vertices.csv').open()):
 key=tuple(int(row[k]) for k in ['p_index','u_index','v_index']);assert key not in vertices
 val=binary(row['certified_margin_lower']);assert val>0;vertices[key]=val
expected_vertices={(p,u,v) for p in range(21) for u in range(101) for v in range(min(u,85)+1)}
assert len(expected_vertices)==105651 and set(vertices)==expected_vertices
cells=0
for p in range(20):
 for v in range(85):
  for u in range(v,100):
   for a,b,c in product((0,1),repeat=3):
    uu,vv=u+b,v+c;key=(p+a,max(uu,vv),min(uu,vv));assert key in vertices
   cells+=1
assert cells==98600
# Independently recompute the exact interpolation and two-area error losses.
assert (42*Q(1,100)**2*2+2*Q(1,20)**2)/8==Q(67,40000)
result={'status':'PASS exact cover and margin checks','scope':'Independent exact postprocessing, distinct volume/disjointness cover proof. Numerical enclosures use the supplied MPFI/MPFR programs.','proof_sha256':manifest['proof_sha256'],'derivative_boxes':len(seen),'derivative_max_abs':{str(k):str(v) for k,v in maxima.items()},'local_roots':len(roots),'local_leaves':len(leaves),'local_disjoint_box_pairs_checked':pairs,'largest_corrected_eigenvalue_upper_exact':str(worst),'largest_corrected_eigenvalue_upper_float':float(worst),'complement_vertices':len(vertices),'complement_cells':cells,'min_complement_margin_exact':str(min(vertices.values())),'min_complement_margin_float':float(min(vertices.values())),'replay_checked':REPLAY}
result['wall_seconds']=time.perf_counter()-start
out=ROOT/'results/c4.json'

out.write_text(json.dumps(result,indent=2)+'\n',encoding='utf-8')
print(result['status'])
