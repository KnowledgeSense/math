#!/usr/bin/env python3
"""Exact certificate verifier: rooted dyadic tilings, exact matrix tests, fixed-reference losses.
No imports from author checkers. The MPFI enclosure semantics are a separate audit.
"""
from pathlib import Path
from fractions import Fraction as F
from itertools import product
import argparse,csv,json,math,hashlib,datetime,time
D=1000*2**20

def read(p):
 with p.open() as f:return list(csv.DictReader(f))
def rat(s):
 x=float(s);assert math.isfinite(x);return F(*x.as_integer_ratio())
def box(r):return tuple(int(r[f'{a}_{b}']) for a in ('p','u','v') for b in ('lo','hi'))
def contains(outer,inner):return all(outer[2*a]<=inner[2*a]<inner[2*a+1]<=outer[2*a+1] for a in range(3))
def scaled(q):return tuple(int(x*D) for x in q)
def intervals(seq):return list(zip(seq,seq[1:]))
def geometry_roots():
 local={}
 for typ,ps,us,vs in [('D',[F(i,10) for i in range(40,52)],[F(9,10),F(19,20),F(1)],[F(9,10),F(19,20),F(1)]),('T',[F(i,10) for i in range(49,61)],[F(19,20),F(1)],[F(0),F(1,20),F(1,10)])]:
  for idx,trip in enumerate(product(intervals(ps),intervals(us),intervals(vs))):local[typ,idx]=scaled(sum(trip,()))
 # The independent domain test uses containment in the two mathematical rectangles.
 rectangles=[scaled((F(4),F(51,10),F(9,10),F(1),F(9,10),F(1))),scaled((F(49,10),F(6),F(19,20),F(1),F(0),F(1,10)))]
 pt=[F(4),F(49,10),F(5),F(51,10),F(6)];uv=[F(0),F(1,10),F(9,10),F(19,20),F(1)]
 complement=[];atoms=local_atoms=0
 for pr,ur,vr in product(intervals(pt),intervals(uv),intervals(uv)):
  # If u and v intervals have distinct indices, ordering admits just the lower triangle.
  # Same-interval squares contain their entire diagonal triangle.
  if ur[0]<vr[0]:continue
  atoms+=1;b=scaled(pr+ur+vr)
  local_cover=any(contains(r,b) for r in rectangles)
  if local_cover:local_atoms+=1
  else:complement.append((b,'D' if pr[1]<=5 else 'T'))
 assert len(local)==66 and len(complement)==28 and atoms==40
 # Local prescribed roots partition each full rectangle, checked by disjoint volume.
 for typ,rect in zip(('D','T'),rectangles):
  roots=[b for (t,i),b in local.items() if t==typ]
  assert all(contains(rect,b) for b in roots)
  vol=lambda b:math.prod(b[2*a+1]-b[2*a] for a in range(3))
  assert sum(map(vol,roots))==vol(rect)
  for i,b in enumerate(roots):
   for c in roots[:i]:assert any(max(b[2*a],c[2*a])>=min(b[2*a+1],c[2*a+1]) for a in range(3))
 return local,complement,{'chart_atoms':atoms,'local_atoms':local_atoms,'complement_atoms':len(complement),'closed_boundaries':True}

def partition(rows,root,branch=None):
 index={box(r):r for r in rows};assert len(index)==len(rows)
 seen=set();pending=[(root,0)];leaves={};splits=0
 while pending:
  b,depth=pending.pop();assert b not in seen and b in index;seen.add(b)
  r=index[b];assert int(r['depth'])==depth
  assert all(b[2*a]<b[2*a+1] for a in range(3))
  if branch is not None:assert r['branch']==branch
  if r['decision']=='PASS':assert int(r['axis'])==-1;leaves[b]=depth
  else:
   assert r['decision']=='SPLIT';axis=int(r['axis']);assert axis in (0,1,2)
   total=b[2*axis]+b[2*axis+1];assert total%2==0
   mid=total//2;assert b[2*axis]<mid<b[2*axis+1]
   left=list(b);right=list(b);left[2*axis+1]=mid;right[2*axis]=mid
   pending.extend([(tuple(left),depth+1),(tuple(right),depth+1)]);splits+=1
 assert seen==set(index);assert len(rows)==2*len(leaves)-1;assert splits+1==len(leaves)
 return leaves

def check_local(base,roots):
 count=nodes=0;mindet=None;worst=F(-1);maxint=0;allsha={}
 for (typ,idx),b in roots.items():
  leafpath=base/'logs/local_full'/f'{typ}_{idx:02d}.csv';treepath=base/'logs/local_full'/f'{typ}_{idx:02d}_tree.csv'
  tr=read(treepath);lr=read(leafpath)
  assert all(int(r['root'])==idx for r in tr+lr)
  actual=partition(tr,b);cert={box(r):r for r in lr};assert len(cert)==len(lr) and set(cert)==set(actual)
  for q,r in cert.items():
   assert int(r['depth'])==actual[q] and int(r['denominator'])==D
   maxint=max(maxint,*(abs(x) for x in q),*(abs(q[2*a]+q[2*a+1]) for a in range(3)),2*D)
   radius={a:F(q[2*j+1]-q[2*j],2*D) for j,a in enumerate('puv')}
   H={a:(rat(r['h'+a+'_lo']),rat(r['h'+a+'_hi'])) for a in ('11','12','22')}
   ds=[(rat(r[f'd{j}_lo']),rat(r[f'd{j}_hi'])) for j in range(7)]
   assert all(x<=y for x,y in list(H.values())+ds)
   bounds=[max(map(abs,x)) for x in ds]
   # Coordinates are p,u,v; Hessian derivative tensors are separately mapped.
   tensor={'11':{'p':4,'u':0,'v':1},'12':{'p':5,'u':1,'v':2},'22':{'p':6,'u':2,'v':3}}
   err={a:sum(radius[c]*bounds[tensor[a][c]] for c in 'puv') for a in tensor}
   assert all(0<=err[a]<=rat(r['err'+a]) for a in err)
   aa=H['11'][1]+err['11']+F(1,1000);cc=H['22'][1]+err['22']+F(1,1000)
   bb=max(map(abs,H['12']))+err['12'];det=aa*cc-bb*bb
   assert aa<0 and cc<0 and bb>=0 and det>0
   mindet=det if mindet is None else min(mindet,det)
   reported=rat(r['eigen_upper']);assert reported<-F(1,1000);worst=max(worst,reported)
  count+=len(lr);nodes+=len(tr)
  for p in (leafpath,treepath):allsha[str(p.relative_to(base))]=hashlib.sha256(p.read_bytes()).hexdigest()
 assert count==9780 and nodes==19494 and maxint<2**53
 return {'roots':len(roots),'leaves':count,'nodes':nodes,'minimum_Schur_determinant':str(mindet),'worst_displayed_eigen_upper':str(worst),'max_integer_converted_to_double':maxint,'all_integer_double_inputs_exact':True,'data_sha256':allsha}

def check_complement(base,roots):
 logs=base/'logs';vr=read(logs/'complement_full_vertices.csv');values={};maxint=2*D
 for r in vr:
  key=tuple(int(r[a]) for a in ('p','u','v'));assert key not in values and int(r['denominator'])==D
  lo,hi=rat(r['area_lower']),rat(r['area_upper']);assert 0<lo<=hi
  assert hi-lo>=F(120,512**2) # both signs of explicit midpoint error retained
  values[key]=lo,hi;maxint=max(maxint,*map(abs,key))
 tr=read(logs/'complement_full_tree.csv');lr=read(logs/'complement_full_leaves.csv')
 assert {int(r['root']) for r in tr}==set(range(28))=={int(r['root']) for r in lr}
 count=0;worst=None;used=set();allnodes=0
 for idx,(initial,branch) in enumerate(roots):
  tree=[r for r in tr if int(r['root'])==idx];leaf=[r for r in lr if int(r['root'])==idx]
  actual=partition(tree,initial,branch);cert={box(r):r for r in leaf}
  assert len(cert)==len(leaf) and set(cert)==set(actual)
  for b,r in cert.items():
   assert r['branch']==branch and int(r['depth'])==actual[b] and int(r['denominator'])==D
   assert (b[1]<=5*D if branch=='D' else b[0]>=5*D)
   # The SAME branch is used at every corner of a leaf, even at p=5.
   corners=list(product(b[0:2],b[2:4],b[4:6]));gaps=[]
   for k,u,v in corners:
    reference=(k,D,D if branch=='D' else 0);key=k,u,v
    assert reference in values and key in values;used.update((reference,key))
    gaps.append(values[reference][0]-values[key][1])
   width=[F(b[2*a+1]-b[2*a],D) for a in range(3)]
   loss=sum(c*h*h for c,h in zip((1,84,84),width))/8
   margin=min(gaps)-loss
   assert loss<=rat(r['interpolation_loss_upper'])
   assert margin>F(1,100000) and rat(r['margin_lower'])>F(1,100000)
   worst=margin if worst is None else min(worst,margin)
   maxint=max(maxint,*map(abs,b),*(abs(b[2*a]+b[2*a+1]) for a in range(3)))
  allnodes+=len(tree);count+=len(leaf)
 assert count==16370 and allnodes==32712 and len(values)==21391 and maxint<2**53
 return {'roots':28,'leaves':count,'nodes':allnodes,'vertices':len(values),'vertices_used_by_accepted_leaves':len(used),'minimum_exact_margin':str(worst),'target':'1/100000','max_integer_converted_to_double':maxint,'data_sha256':{p.name:hashlib.sha256(p.read_bytes()).hexdigest() for p in logs.glob('complement_full_*.csv')}}

def main():
 parser=argparse.ArgumentParser();parser.add_argument('base',type=Path);parser.add_argument('output',type=Path);args=parser.parse_args();t=time.monotonic();start=datetime.datetime.now(datetime.timezone.utc).isoformat()
 local,comp,geom=geometry_roots();result={'start_utc':start,'input_base':str(args.base),'geometry':geom,'local':check_local(args.base,local),'complement':check_complement(args.base,comp),'status':'EXACT COVER/DEFINITENESS/INTERPOLATION PASS'}
 result.update(end_utc=datetime.datetime.now(datetime.timezone.utc).isoformat(),seconds=time.monotonic()-t,checker_sha256=hashlib.sha256(Path(__file__).read_bytes()).hexdigest());args.output.write_text(json.dumps(result,indent=2)+'\n');print(json.dumps({k:v for k,v in result.items() if k not in ('local','complement')},indent=2));print('local',result['local']['leaves'],'complement',result['complement']['leaves'],'minimum margin',result['complement']['minimum_exact_margin'])
if __name__=='__main__':main()
