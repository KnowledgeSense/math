#!/usr/bin/env python3
"""Independent exact certificate audit: tree edges, pairwise disjoint leaves,
exact volumes and a rational matrix comparison. No transcendental evaluation."""
from pathlib import Path
from fractions import Fraction as F
from itertools import combinations
import argparse,csv,json,math,hashlib,datetime,copy
R=Path(__file__).resolve().parents[1]; DEN=1000*2**20; SHIFT=F(1,1000)
def require(test,msg):
 if not test:raise ValueError(msg)
def numeric(s):
 x=float(s);require(math.isfinite(x),'nonfinite bound');return F(*x.as_integer_ratio())
def geometry(row):return tuple(int(row[f'{n}_{e}']) for n in ('p','u','v') for e in ('lo','hi'))
def expected(root):
 k=root//4;i=(root//2)%2;j=root%2
 return tuple(x*2**20 for x in (2000+100*k,2100+100*k,900+50*i,950+50*i,900+50*j,950+50*j))
def vol(box):return math.prod(box[2*k+1]-box[2*k] for k in range(3))
def load(folder,ids=range(40)):
 result={}
 for root in ids:
  with (folder/f'D_{root:02d}_tree.csv').open() as f:nodes=list(csv.DictReader(f))
  with (folder/f'D_{root:02d}.csv').open() as f:leaves=list(csv.DictReader(f))
  result[root]=(nodes,leaves)
 return result

def check(data,full=True):
 require((set(data)==set(range(40))) if full else bool(data),'root set mismatch')
 rows=[];determinants=[];evals=[];totalvolume=F(0);minddiag=None;maxdepth=0
 for root,(nodes,leaves) in sorted(data.items()):
  require(0<=root<40,'invalid root')
  nd={geometry(n):n for n in nodes};ld={geometry(l):l for l in leaves}
  require(len(nd)==len(nodes) and len(ld)==len(leaves),'duplicate geometry')
  require(expected(root) in nd,'missing root')
  incoming={b:0 for b in nd};terminals=set()
  for b,n in nd.items():
   require(int(n['root'])==root,'node root label')
   require(all(b[2*k]<b[2*k+1] for k in range(3)),'nonpositive width')
   require(all(expected(root)[2*k]<=b[2*k]<b[2*k+1]<=expected(root)[2*k+1] for k in range(3)),'node outside root')
   depth=int(n['depth']);require(depth>=0,'negative depth');maxdepth=max(maxdepth,depth)
   if n['decision']=='PASS':require(int(n['axis'])==-1,'terminal axis');terminals.add(b)
   else:
    require(n['decision']=='SPLIT','unknown or failed decision');axis=int(n['axis']);require(0<=axis<3,'invalid split axis')
    x,y=b[2*axis:2*axis+2];require((x+y)%2==0,'nonintegral split');mid=(x+y)//2;require(x<mid<y,'empty split')
    left=list(b);right=list(b);left[2*axis+1]=mid;right[2*axis]=mid
    for child in (tuple(left),tuple(right)):
     require(child in nd,'missing child');incoming[child]+=1;require(int(nd[child]['depth'])==depth+1,'bad child depth')
  require(int(nd[expected(root)]['depth'])==0,'root depth')
  require(incoming[expected(root)]==0 and all(n==1 for b,n in incoming.items() if b!=expected(root)),'parent connectivity')
  require(terminals==set(ld),'leaf record mismatch')
  # A second coverage argument deliberately ignores the split structure.
  for a,b in combinations(ld,2):
   require(any(min(a[2*k+1],b[2*k+1])<=max(a[2*k],b[2*k]) for k in range(3)),'overlapping interiors')
  volume=sum(vol(b) for b in ld);require(volume==vol(expected(root)),'leaf volume mismatch');totalvolume+=F(volume,DEN**3)
  for box,l in ld.items():
   require(int(l['root'])==root and int(l['depth'])==int(nd[box]['depth']),'leaf label mismatch')
   require(int(l['denominator'])==DEN,'denominator mismatch')
   center_intervals=[tuple(numeric(l[f'h{name}_{e}']) for e in ('lo','hi')) for name in ('11','12','22')]
   derivative_intervals=[tuple(numeric(l[f'd{k}_{e}']) for e in ('lo','hi')) for k in range(7)]
   require(all(a<=b for a,b in center_intervals+derivative_intervals),'reversed interval')
   abs_derivative=[max(abs(x),abs(y)) for x,y in derivative_intervals]
   radii=[F(box[2*k+1]-box[2*k],2*DEN) for k in range(3)]
   # Gradient indices for (p,u,v), in the physical Hessian entry order.
   errors=[sum(abs_derivative[j]*radii[k] for k,j in enumerate(indices)) for indices in ((4,0,1),(5,1,2),(6,2,3))]
   for e,name in zip(errors,('11','12','22')):require(e<=numeric(l[f'err{name}']),'understated error')
   a=center_intervals[0][1]+errors[0];c=center_intervals[2][1]+errors[2];b=max(abs(x) for x in center_intervals[1])+errors[1]
   # LDL pivots of the negated shifted comparison matrix.
   first=-(a+SHIFT);second=-(c+SHIFT)
   require(first>0 and second>0,'nonnegative shifted diagonal')
   determinant=first*second-b*b;require(determinant>0,'nonpositive Schur determinant');determinants.append(determinant)
   z=numeric(l['eigen_upper']);require(z<-SHIFT,'reported eigen bound fails')
   require(z>=max(a,c) and (z-a)*(z-c)>=b*b,'reported eigen upper understated');evals.append(z)
   minddiag=min(first,second) if minddiag is None else min(minddiag,first,second)
  rows.append(dict(root=root,nodes=len(nodes),leaves=len(leaves),volume=str(F(volume,DEN**3))))
 if full:require(totalvolume==F(1,100),'full domain volume')
 return dict(status='EXACT PASS',roots=len(data),nodes=sum(x['nodes'] for x in rows),leaves=sum(x['leaves'] for x in rows),max_depth=maxdepth,total_volume=str(totalvolume),minimum_schur_determinant=str(min(determinants)),minimum_shifted_diagonal_margin=str(minddiag),worst_reported_eigen_upper=str(max(evals)),root_details=rows)

def mutation_tests(data):
 base={0:copy.deepcopy(data[0])};tests=[]
 def trial(name,mut,full=False):
  x=copy.deepcopy(base);mut(x)
  try:check(x,full=full)
  except (ValueError,KeyError,OverflowError) as e:tests.append(dict(test=name,result='REJECTED',error=str(e)));return
  raise RuntimeError('MUTATION WAS ACCEPTED: '+name)
 trial('incomplete full root set',lambda x:None,True)
 trial('duplicate tree row',lambda x:x[0][0].append(copy.deepcopy(x[0][0][0])))
 trial('duplicate leaf row',lambda x:x[0][1].append(copy.deepcopy(x[0][1][0])))
 trial('missing tree root',lambda x:x[0][0].pop(0))
 trial('missing leaf',lambda x:x[0][1].pop())
 trial('wrong node root',lambda x:x[0][0][0].update(root='1'))
 trial('wrong leaf root',lambda x:x[0][1][0].update(root='1'))
 trial('nonpositive width',lambda x:x[0][0][0].update(p_hi=x[0][0][0]['p_lo']))
 trial('failed decision',lambda x:x[0][0][0].update(decision='FAIL'))
 trial('unknown decision',lambda x:x[0][0][0].update(decision='MAYBE'))
 trial('bad split axis',lambda x:x[0][0][0].update(axis='3'))
 trial('wrong root depth',lambda x:x[0][0][0].update(depth='1'))
 trial('wrong leaf depth',lambda x:x[0][1][0].update(depth='999'))
 trial('wrong denominator',lambda x:x[0][1][0].update(denominator='1'))
 trial('nan Hessian',lambda x:x[0][1][0].update(h11_hi='nan'))
 trial('infinite derivative',lambda x:x[0][1][0].update(d0_hi='inf'))
 trial('reversed Hessian interval',lambda x:x[0][1][0].update(h11_lo='1'))
 trial('understated entry error',lambda x:x[0][1][0].update(err11='0'))
 trial('nonnegative diagonal',lambda x:x[0][1][0].update(h11_hi='0'))
 trial('bad offdiagonal Schur',lambda x:x[0][1][0].update(h12_hi='5'))
 trial('understated displayed eigenvalue',lambda x:x[0][1][0].update(eigen_upper='-5'))
 trial('positive displayed eigenvalue',lambda x:x[0][1][0].update(eigen_upper='1'))
 return tests
if __name__=='__main__':
 ap=argparse.ArgumentParser();ap.add_argument('directory',type=Path);ap.add_argument('--out',type=Path,required=True);ap.add_argument('--mutations',action='store_true');a=ap.parse_args()
 d=load(a.directory);result=check(d);result['checked_utc']=datetime.datetime.now(datetime.timezone.utc).isoformat();result['checker_sha256']=hashlib.sha256(Path(__file__).read_bytes()).hexdigest()
 if a.mutations:result['mutation_tests']=mutation_tests(d)
 a.out.write_text(json.dumps(result,indent=2)+'\n');print(json.dumps({k:v for k,v in result.items() if k not in ('root_details','mutation_tests')},indent=2));print('Mutation rejections:',len(result.get('mutation_tests',[])))
