"""Separate direct-order small-field certificate replay; no search, no asserts."""
import json,sys
from pathlib import Path
from strict_io import need,unique_json,parse_certificates,bind_fallback

def model(p,f,mod):
 def dec(x):
  a=[]
  for _ in range(f):a.append(x%p);x//=p
  return a
 def enc(a):return sum(v*p**i for i,v in enumerate(a))
 def add(x,y):return enc([(a+b)%p for a,b in zip(dec(x),dec(y))])
 def mul(x,y):
  if f==1:return x*y%p
  result=0
  for digit in dec(y):
   for _ in range(digit):result=add(result,x)
   a=dec(x);lead=a[-1];a=[0]+a[:-1];x=enc([(a[i]-lead*mod[i])%p for i in range(f)])
  return result
 q=p**f;primitive=set()
 for a in range(1,q):
  v=1;order=None
  for k in range(1,q):
   v=mul(v,a)
   if v==1:order=k;break
  need(order is not None,'nonunit in small field')
  if order==q-1:primitive.add(a)
 return add,mul,primitive

def verify(root):
 root=Path(root);expected={int(q):tuple(pf) for q,pf in unique_json(root/'SELECTED_ORDERS.json').items()}
 rows=parse_certificates(root/'CERTIFICATES.tsv',expected);data=unique_json(root/'FALLBACK_RESULTS.json');bind_fallback(data,rows,root);cache={};positive=negative=0
 for record in data:
  q,a=record['q'],record['a0'];r=rows[q]
  if q not in cache:cache[q]=model(r['p'],r['degree'],r['polynomial'])
  add,mul,primitive=cache[q]
  if record['status']=='positive_cycle':
   cycle=record['cycle'];need(all(type(v) is int for v in cycle),'cycle integer type')
   need(len(cycle)==q-1 and set(cycle)==set(range(1,q)),'cycle permutation')
   need(all(add(a,mul(cycle[i],cycle[(i+1)%(q-1)])) in primitive for i in range(q-1)),'cycle edge/closing edge');positive+=1
  else:
   adj=lambda u:{v for v in range(1,q) if u!=v and add(a,mul(u,v)) in primitive}
   need((q,a)==(11,2) and adj(2)==adj(9)=={3,8},'negative forced-cycle certificate');negative+=1
 return {'status':'PASS','instances':len(data),'positive_cycles':positive,'accepted_negative':negative}
if __name__=='__main__':print(json.dumps(verify(sys.argv[1])))
