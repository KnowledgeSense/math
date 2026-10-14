"""Canonical, fail-closed formats and exact domain/partition checks. No assertions."""
import hashlib,json,re,math
from pathlib import Path
ORDERS_SHA='f9dd4318c6136d78d1d59011d67a2ce75d384d07fb83a96fd54cd8880257d60b'
HEADER='q,characteristic,degree,phi_q_minus_1,omega_q_minus_1,W_q_minus_1'
CERT_HEADER='q\tp\tdegree\tg\tK\tpolynomial\tuncovered_file\textra_file'
FIXED=(8,9,11,13,16,25,27,31,43,49,81,101,125,211,4096,2042041,4084081,13123111,17160991,18888871)
def need(ok,message):
 if not ok:raise ValueError(message)
def integer(s):
 need(isinstance(s,str) and re.fullmatch(r'0|[1-9][0-9]*',s) is not None,'noncanonical unsigned integer')
 need(len(s)<=10,'integer too long')
 return int(s)
def lines(path,empty=False):
 raw=Path(path).read_bytes();need(len(raw)<=20_000_000,'text input too large')
 need(raw==b'' and empty or raw.endswith(b'\n'),'missing final newline or empty file')
 need(all(c in (9,10) or 32<=c<=126 for c in raw),'noncanonical control/non-ASCII byte')
 text=raw.decode('ascii');rows=text[:-1].split('\n') if raw else []
 need(all(rows),'blank line');return rows
def unique_json(path):
 def pairs(items):
  d={}
  for k,v in items:need(k not in d,'duplicate JSON key');d[k]=v
  return d
 return json.loads(Path(path).read_text(),object_pairs_hook=pairs,parse_constant=lambda _:(_ for _ in ()).throw(ValueError('nonfinite JSON')))
def orders(path):
 raw=Path(path).read_bytes();ls=lines(path);need(ls[0]==HEADER,'order CSV header')
 rows={}
 for line in ls[1:]:
  values=line.split(',');need(len(values)==6,'order CSV column count');q,p,f,phi,omega,W=map(integer,values)
  need(q not in rows,'duplicate order');need(8<=q<=25_000_000 and 2<=p<=q and 1<=f<=12 and p**f==q,'order encoding')
  need(W==2**omega and 2<=phi<q,'order arithmetic metadata');rows[q]=(p,f)
 need(list(rows)==sorted(rows),'order CSV not sorted')
 need(len(rows)==2693,'residual order count');need(hashlib.sha256(raw).hexdigest()==ORDERS_SHA,'audited order CSV hash mismatch')
 return rows
def parse_certificates(path,expected):
 ls=lines(path);need(ls[0]==CERT_HEADER,'certificate TSV header');rows={}
 for line in ls[1:]:
  fields=line.split('\t');need(len(fields)==8,'certificate TSV column count')
  q,p,f,g,K=map(integer,fields[:5]);need(q in expected,'extra field');need(q not in rows,'duplicate field')
  need((p,f)==expected[q],'characteristic/degree differs from audited order')
  poly=list(map(integer,fields[5].split(',')));need(len(poly)==f+1 and poly[-1]==1 and all(c<p for c in poly),'polynomial encoding')
  need(f!=1 or poly==[0,1],'prime field polynomial encoding')
  need(0<g<q and 0<=K<=min(1024,q-1 if p==2 else (q-1)//2),'generator/witness range')
  need(fields[6]==f'uncovered_{q}.txt','uncovered filename')
  need(fields[7]==f'extras_{q}.tsv','extra-stage filename')
  rows[q]={'q':q,'p':p,'degree':f,'g':g,'K':K,'polynomial':poly,'uncovered_file':fields[6],'extra_file':fields[7]}
 need(set(rows)==set(expected),'missing field record')
 return rows
def write_certificates(path,rows):
 text=CERT_HEADER+'\n'
 for r in sorted(rows,key=lambda r:r['q']):
  text+='\t'.join([str(r[k]) for k in ('q','p','degree','g','K')]+[','.join(map(str,r['polynomial'])),r['uncovered_file'],r['extra_file']])+'\n'
 Path(path).write_text(text)
def allowed_extra_js(q,p):
 if p==2:return []
 m=(q-1)//2
 return [j for j in range(1,min(64,m-1)+1) if math.gcd(j,m)==1][:8][1:]
def extra_stages(path,q,p):
 ls=lines(path);need(ls[0]=='j\tprefix_length','extra-stage header');allowed=allowed_extra_js(q,p);out=[];cap=min(1024,(q-1)//2)
 need(len(ls)-1<=len(allowed),'too many extra stages')
 for index,line in enumerate(ls[1:]):
  values=line.split('\t');need(len(values)==2,'extra-stage columns');j,length=map(integer,values)
  need(j==allowed[index],'extra stages omitted, reordered or duplicated');need(1<=length<=cap,'extra-stage length out of bounds')
  if index+1<len(ls)-1:need(length==cap,'nonfinal extra-stage prefix incomplete')
  out.append([j,length])
 return out
def offsets(path,q):
 out=[integer(s) for s in lines(path,empty=True)]
 need(all(1<=a<q for a in out),'offset outside nonzero field domain')
 need(out==sorted(set(out)),'duplicate or unsorted offset')
 return out
def bind_replay(reports,rows,root):
 need(set(reports)==set(rows),'replay field set differs')
 for q,r in rows.items():
  d=reports[q];missing=offsets(Path(root)/r['uncovered_file'],q)
  need(set(d)=={'q','p','degree','K','covered','uncovered','status','uncovered_sha256','extra_stages','extra_checks','extra_sha256'},'replay output schema')
  need(d['uncovered_sha256']==hashlib.sha256((Path(root)/r['uncovered_file']).read_bytes()).hexdigest(),'verified uncovered bytes changed')
  stages=extra_stages(Path(root)/r['extra_file'],q,r['p'])
  need(d['extra_sha256']==hashlib.sha256((Path(root)/r['extra_file']).read_bytes()).hexdigest(),'verified extra-stage bytes changed')
  need(type(d['extra_checks']) is int and 0<=d['extra_checks']<=5_000_000 and type(d['extra_stages']) is int and d['extra_stages']==len(stages),'extra-stage replay counters')
  if stages:need(r['K']==min(1024,(q-1)//2),'extra stages before core exhausted')
  if missing and r['p']!=2:
   need(len(stages)==len(allowed_extra_js(q,r['p'])) and all(length==min(1024,(q-1)//2) for j,length in stages),'missing coverage with unexhausted extra family')
  need(d['status']=='PASS' and (d['q'],d['p'],d['degree'],d['K'])==(q,r['p'],r['degree'],r['K']),'replay encoding')
  need(type(d['covered']) is int and type(d['uncovered']) is int and d['uncovered']==len(missing) and d['covered']+d['uncovered']==q-1,'offset partition counts')
def bind_extra_counts(generation,replays):
 need(set(generation)==set(replays),'extra-count field set differs')
 for q,g in generation.items():
  v=replays[q]['extra_checks']
  need(type(g) is int and type(v) is int and 0<=g<=5_000_000 and 0<=v<=5_000_000,'extra-count per-field bound')
  need(g==v,'generation/scalar extra-check count disagreement')
 total=sum(generation.values());need(total<=25_000_000,'extra-count global bound');return total
def bind_fallback(data,rows,root):
 need(isinstance(data,list),'fallback list required');expected=set()
 for q,r in rows.items():
  missing=offsets(Path(root)/r['uncovered_file'],q)
  need(not missing or q<=125,'uncovered large field requires HOLD')
  expected.update((q,a) for a in missing)
 seen=set()
 for record in data:
  need(isinstance(record,dict) and set(record)=={'q','a0','status','nodes','cycle'},'fallback record schema')
  q,a=record['q'],record['a0'];need(type(q) is int and type(a) is int,'fallback integer type')
  key=q,a;need(key in expected,'extra fallback offset');need(key not in seen,'duplicate fallback offset');seen.add(key)
  need(type(record['nodes']) is int and 0<=record['nodes']<=1_000_000,'fallback node count')
  if record['status']=='accepted_negative':need(key==(11,2) and record['cycle'] is None,'unaccepted negative certificate')
  else:need(record['status']=='positive_cycle' and isinstance(record['cycle'],list),'unresolved fallback')
 need(seen==expected,'missing fallback offset')
 return seen
