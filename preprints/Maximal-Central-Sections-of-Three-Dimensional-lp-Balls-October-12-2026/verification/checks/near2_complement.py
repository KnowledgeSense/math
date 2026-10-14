#!/usr/bin/env python3
"""Independent exact near2 complement verifier: full trees, disjoint-volume
coverage, all logged vertices, and recomputed tensor chord losses."""
from pathlib import Path
from fractions import Fraction as F
import argparse,csv,json,math,copy,datetime,hashlib
R=Path(__file__).resolve().parents[1];DEN=1000*2**20;TARGET=F(1,10**6)
def need(b,msg):
 if not b:raise ValueError(msg)
def num(s):
 x=float(s);need(math.isfinite(x),'nonfinite bound');return F(*x.as_integer_ratio())
def geo(r):return tuple(int(r[f'{a}_{e}']) for a in ('p','u','v') for e in ('lo','hi'))
def rootbox(i):
 k,j=divmod(i,2);return tuple(x*2**20 for x in (2000+100*k,2100+100*k,900 if j else 0,1000 if j else 900,0,900))
def volume(b):return math.prod(b[2*j+1]-b[2*j] for j in range(3))
def read(p):
 with p.open() as f:return list(csv.DictReader(f))
def load(folder,ids=range(20)):return {i:(read(folder/f'R_{i:02d}_tree.csv'),read(folder/f'R_{i:02d}_leaves.csv'),read(folder/f'R_{i:02d}_vertices.csv')) for i in ids}
def check(data,full=True):
 need(set(data)==set(range(20)) if full else bool(data),'wrong root set');details=[];mins=[];totalvol=F(0);maxdepth=0;globalvalues={};rounding_diffs=[]
 for i,(tree,leaves,vertices) in sorted(data.items()):
  need(0<=i<20,'invalid root');nodes={geo(r):r for r in tree};leafmap={geo(r):r for r in leaves};vals={tuple(int(r[k]) for k in ('p','u','v')):(num(r['area_lower']),num(r['area_upper'])) for r in vertices}
  need(len(nodes)==len(tree) and len(leafmap)==len(leaves) and len(vals)==len(vertices),'duplicate geometry/key')
  need(rootbox(i) in nodes,'missing root');need(all(int(r['denominator'])==DEN for r in vertices),'vertex denominator');need(all(x<=y for x,y in vals.values()),'reversed vertex interval')
  for key,v in vals.items():
   need(globalvalues.get(key,v)==v,'inconsistent repeated vertex');globalvalues[key]=v
  incoming={b:0 for b in nodes};terminal=set()
  for b,r in nodes.items():
   need(int(r['root'])==i and r['branch']=='D','wrong node label');need(all(b[2*k]<b[2*k+1] for k in range(3)),'nonpositive width');need(all(rootbox(i)[2*k]<=b[2*k]<b[2*k+1]<=rootbox(i)[2*k+1] for k in range(3)),'outside root');dep=int(r['depth']);need(dep>=0,'negative depth');maxdepth=max(maxdepth,dep)
   if r['decision']=='PASS':need(int(r['axis'])==-1,'terminal axis');terminal.add(b)
   else:
    need(r['decision']=='SPLIT','unknown or failed decision');k=int(r['axis']);need(k in (0,1,2),'invalid axis');s=b[2*k]+b[2*k+1];need(s%2==0,'indivisible split');mid=s//2;need(b[2*k]<mid<b[2*k+1],'empty split');a=list(b);c=list(b);a[2*k+1]=mid;c[2*k]=mid
    for child in (tuple(a),tuple(c)):
     need(child in nodes,'missing child');incoming[child]+=1;need(int(nodes[child]['depth'])==dep+1,'incorrect depth')
  need(int(nodes[rootbox(i)]['depth'])==0,'root depth');need(incoming[rootbox(i)]==0 and all(n==1 for b,n in incoming.items() if b!=rootbox(i)),'disconnected or extra parent');need(terminal==set(leafmap),'leaf/tree mismatch')
  # Independent of the tree: p-axis sweep detects all positive-volume overlaps.
  active=[]
  for b in sorted(leafmap):
   active=[a for a in active if a[1]>b[0]]
   for a in active:need(a[3]<=b[2] or b[3]<=a[2] or a[5]<=b[4] or b[5]<=a[4],'leaf interiors overlap')
   active.append(b)
  vol=sum(volume(b) for b in leafmap);need(vol==volume(rootbox(i)),'volume deficit/excess');totalvol+=F(vol,DEN**3);used=set();localm=[]
  for b,r in leafmap.items():
   need(int(r['root'])==i and r['branch']=='D' and int(r['depth'])==int(nodes[b]['depth']),'leaf label mismatch');need(int(r['denominator'])==DEN,'leaf denominator')
   widths=[F(b[2*k+1]-b[2*k],DEN) for k in range(3)];pl=F(b[0],DEN);loss=F(56)*widths[0]**2/pl**4+F(65,4)*(widths[1]**2+widths[2]**2)/pl;need(loss<=num(r['interpolation_loss_upper']),'understated loss')
   gaps=[]
   for p in b[:2]:
    for u in b[2:4]:
     for v in b[4:6]:
      ref=(p,DEN,DEN);key=(p,u,v);need(ref in vals and key in vals,'missing required vertex');used.update((ref,key));gaps.append(vals[ref][0]-vals[key][1])
   exact=min(gaps)-loss;need(exact>TARGET,'failed exact chord margin');need(num(r['margin_lower'])>TARGET,'reported margin fails');num(r['corner_gap_lower']);mins.append(exact);localm.append(exact)
   # Displayed margin uses pre-print 80-bit values, so it need not be <= this
   # more conservative recomputation from directed binary64 vertex endpoints.
   rounding_diffs.append(num(r['margin_lower'])-exact)
  need(used==set(vals),'unused or extraneous vertex');details.append(dict(root=i,nodes=len(nodes),leaves=len(leafmap),vertices=len(vals),volume=str(F(vol,DEN**3)),minimum_exact_margin=str(min(localm))))
 if full:need(totalvol==F(9,10),'wrong total volume')
 return dict(status='INDEPENDENT EXACT COMPLEMENT PASS',roots=len(data),nodes=sum(r['nodes'] for r in details),leaves=sum(r['leaves'] for r in details),vertices_per_root_total=sum(r['vertices'] for r in details),globally_distinct_vertices=len(globalvalues),max_depth=maxdepth,total_volume=str(totalvol),minimum_exact_margin=str(min(mins)),maximum_display_minus_recomputed_margin=str(max(rounding_diffs)),details=details)
def mutations(data):
 base={0:copy.deepcopy(data[0])};out=[]
 def trial(label,mut,full=False):
  d=copy.deepcopy(base);mut(d)
  try:check(d,full)
  except (ValueError,KeyError,OverflowError) as e:out.append(dict(test=label,result='REJECTED',error=str(e)));return
  raise RuntimeError('MUTATION ACCEPTED: '+label)
 trial('incomplete root set',lambda d:None,True)
 trial('duplicate tree',lambda d:d[0][0].append(copy.deepcopy(d[0][0][0])))
 trial('duplicate leaf',lambda d:d[0][1].append(copy.deepcopy(d[0][1][0])))
 trial('duplicate vertex',lambda d:d[0][2].append(copy.deepcopy(d[0][2][0])))
 trial('missing root',lambda d:d[0][0].pop(0))
 trial('missing leaf',lambda d:d[0][1].pop())
 trial('missing vertex',lambda d:d[0][2].pop())
 trial('wrong root label',lambda d:d[0][0][0].update(root='1'))
 trial('wrong branch',lambda d:d[0][0][0].update(branch='T'))
 trial('bad root width',lambda d:d[0][0][0].update(p_hi=d[0][0][0]['p_lo']))
 trial('failed decision',lambda d:d[0][0][0].update(decision='FAIL'))
 trial('unknown decision',lambda d:d[0][0][0].update(decision='MAYBE'))
 trial('bad axis',lambda d:d[0][0][0].update(axis='3'))
 trial('wrong depth',lambda d:d[0][0][0].update(depth='1'))
 trial('wrong leaf denominator',lambda d:d[0][1][0].update(denominator='1'))
 trial('wrong vertex denominator',lambda d:d[0][2][0].update(denominator='1'))
 trial('NaN vertex',lambda d:d[0][2][0].update(area_lower='nan'))
 trial('infinite vertex',lambda d:d[0][2][0].update(area_upper='inf'))
 trial('reversed vertex bounds',lambda d:d[0][2][0].update(area_lower='100'))
 trial('bad reference bound',lambda d:d[0][2][0].update(area_lower='-100'))
 trial('understated loss',lambda d:d[0][1][0].update(interpolation_loss_upper='0'))
 trial('failed reported margin',lambda d:d[0][1][0].update(margin_lower='0'))
 return out
if __name__=='__main__':
 a=argparse.ArgumentParser();a.add_argument('directory',type=Path);a.add_argument('--out',type=Path,required=True);a.add_argument('--mutations',action='store_true');x=a.parse_args();data=load(x.directory);r=check(data)
 if x.mutations:r['mutation_tests']=mutations(data)
 r.update(completed_utc=datetime.datetime.now(datetime.timezone.utc).isoformat(),checker_sha256=hashlib.sha256(Path(__file__).read_bytes()).hexdigest());x.out.write_text(json.dumps(r,indent=2)+'\n');print(json.dumps({k:v for k,v in r.items() if k not in ('details','mutation_tests')},indent=2));print('Mutation rejections',len(r.get('mutation_tests',[])))
