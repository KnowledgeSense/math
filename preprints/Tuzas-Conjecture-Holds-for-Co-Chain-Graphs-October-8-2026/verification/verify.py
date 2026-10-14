"""Standard-library proof verification for Tuza's inequality in co-chain graphs.
All paths are relative to this script. This script never writes its inputs/results.
"""
from pathlib import Path
from itertools import combinations,combinations_with_replacement
from collections import Counter
import json,runpy,time
import sys
sys.dont_write_bytecode=True
if sys.flags.optimize:
 raise RuntimeError('Run Python without -O or -OO: assertions are required for verification.')
from packing_bounds import C,J,sparse,dense
D=Path(__file__).resolve().parent

def graph(a,b,d):
 assert len(d)==a and all(0<=v<=b for v in d) and all(d[i]>=d[i+1] for i in range(a-1))
 return set(combinations(range(a),2))|set(combinations(range(a,a+b),2))|{(i,a+j) for i,v in enumerate(d) for j in range(v)}

def check_packing(E,P):
 used=set()
 for tri in P:
  assert len(tri)==3 and len(set(tri))==3
  edges=set(combinations(sorted(tri),2))
  assert edges<=E and not edges&used
  used|=edges

def initial_lower(a,b,d):
 L=C(a)+C(b)
 for aa,bb,dd in ((a,b,d),(b,a,tuple(sum(v>=j for v in d) for j in range(1,b+1)))):
  for k in range(bb+1):
   p=sum(v>=k for v in dd) if k else aa
   L=max(L,C(aa)+J(p,k)+J(k,bb-k),C(p+k)+J(p,aa-p)+J(k,bb-k))
 return L

def cut_upper(a,b,d):
 m=a*(a-1)//2+b*(b-1)//2+sum(d);U=m
 for i in range(a+1):
  for j in range(b+1):
   q=sum(max(0,v-j) if h<i else min(v,j) for h,v in enumerate(d))
   U=min(U,m-i*(a-i)-j*(b-j)-max(q,sum(d)-q))
 return U

started=time.time()
runpy.run_path(str(D/'verify_dense_algebra.py'))
# Small complete graphs; the proof treats every larger order analytically.
for n in range(5):assert n*(n-1)//2-n*n//4<=2*C(n)
# Every small positive-part parity-relevant profile, not just the residual tuples.
small=json.loads((D/'small_exception_certificates.json').read_text())
sc={(z['a'],z['b'],tuple(z['degrees'])):z for z in small}
assert len(sc)==len(small)==11
small_counts=Counter();small_keys=set()
for n in range(2,13):
 for a in range(1,n//2+1):
  b=n-a
  if a%2==b%2==0:continue
  for inc in combinations_with_replacement(range(b+1),a):
   d=tuple(reversed(inc));small_keys.add((a,b,d))
   L=initial_lower(a,b,d);U=cut_upper(a,b,d)
   if U<=2*L:small_counts['constructive_bound']+=1
   else:
    rec=sc[(a,b,d)];E=graph(a,b,d);check_packing(E,rec['packing'])
    cover={tuple(e) for e in rec['cover']};assert cover<=E and len(cover)<=2*len(rec['packing'])
    for tri in combinations(range(n),3):
     edges=set(combinations(tri,2))
     if edges<=E:assert edges&cover
    small_counts['explicit_witness']+=1
assert len(small_keys)==2861 and small_counts=={'constructive_bound':2850,'explicit_witness':11}
# Sparse scalar reduction and all uniform-transfer witnesses.
sparse_table=json.loads((D/'sparse_scalar_failures.json').read_text())
sparse_fail=[];sparse_count=0;sparse_skipped=0
for a in range(1,114):
 for b in range(a,114-a):
  if a%2==b%2==0:continue
  r=(a+1)//2;t=(b+1)//2
  if 3*(r*r+t*t)>=84*(r+t):sparse_skipped+=1;continue
  for x in range(r):
   for y in range(t):
    sparse_count+=1;T,L,_,_=sparse(a,b,x,y)
    if T>2*L:
     T,L,_,_=sparse(a,b,x,y,True)
     if T>2*L:sparse_fail.append((a,b,x,y,T,L))
assert sparse_fail==[(z['a'],z['b'],z['x'],z['y'],z['T'],z['L']) for z in sparse_table['fail']]
assert sparse_count==374409 and sparse_skipped==929 and len(sparse_fail)==82
sparse_certs=json.loads((D/'sparse_canonical_certificates.json').read_text())
sparse_bykey={(z['a'],z['b'],z['x'],z['y']):z for z in sparse_certs}
assert len(sparse_bykey)==len(sparse_certs)==61
for rec in sparse_certs:
 a,b,x,y=(rec[k] for k in ('a','b','x','y'));r=(a+1)//2;t=(b+1)//2
 d=[t]*x+[y]*(r-x)+[0]*(a-r);assert d==rec['degrees']
 E=graph(a,b,d);check_packing(E,rec['packing']);T=sparse(a,b,x,y)[0]
 assert T==rec['T'] and T<=2*len(rec['packing']) and len(rec['packing'])==rec['packing_size']
for a,b,x,y,T,L in sparse_fail:
 if a+b>12:assert (a,b,x,y) in sparse_bykey
# Dense scalar reduction. e is eliminated by exact integer intervals.
dense_table=json.loads((D/'dense_scalar_failures.json').read_text())
dense_fail=[];dense_count=0;dense_e_count=0
for a in range(1,175):
 for b in range(a,175):
  r=(a+1)//2;t=(b+1)//2
  if r+t>=88:break
  if a%2==b%2==0:continue
  for x in range(r,a+1):
   for y in range(t,b+1):
    dense_count+=1;lo,hi,T0,P,S0,_=dense(a,b,x,y)
    if lo<=hi:
     lo,hi,T0,P,S0,_=dense(a,b,x,y,True)
     if lo<=hi:
      dense_fail.append((a,b,x,y,lo,hi,T0,P,S0));dense_e_count+=hi-lo+1
assert dense_fail==[(z['a'],z['b'],z['x'],z['y'],z['e_lo'],z['e_hi'],z['T0'],z['P'],z['S0']) for z in dense_table['fail']]
assert dense_count==3785892 and len(dense_fail)==70 and dense_e_count==73
dense_certs=json.loads((D/'dense_canonical_certificates.json').read_text())
dense_bykey={(z['a'],z['b'],z['x'],z['y'],z['e']):z for z in dense_certs}
assert len(dense_bykey)==len(dense_certs)==30
required=set()
for a,b,x,y,lo,hi,T0,P,S0 in dense_fail:
 if a+b<=12:continue
 r=(a+1)//2;t=(b+1)//2;w=x-r;z=y-t
 for e in range(lo,hi+1):
  assert e in (0,w*z) # entire residual Ferrers shape is thereby forced
  key=(a,b,x,y,e);required.add(key);rec=dense_bykey[key]
  d=[y]*r+([y]*w if e else [t]*w)+[0]*(a-x)
  assert d==rec['degrees']
  E=graph(a,b,d);check_packing(E,rec['packing'])
  assert rec['T']==T0+e<=2*len(rec['packing']) and len(rec['packing'])==rec['packing_size']
  assert sum(max(0,v-t) for v in d[r:])==e
assert required==set(dense_bykey)
summary={'passed':True,'small_profiles':len(small_keys),'small_profile_methods':dict(small_counts),'sparse_scalar_tuples':sparse_count,'sparse_analytically_skipped_size_pairs':sparse_skipped,'sparse_scalar_exceptions':len(sparse_fail),'sparse_packing_certificates_checked':len(sparse_certs),'dense_scalar_tuples':dense_count,'dense_scalar_exceptions':len(dense_fail),'dense_residual_e_values':dense_e_count,'dense_packing_certificates_checked':len(dense_certs),'verification_seconds':round(time.time()-started,3)}
print(json.dumps(summary,indent=2))
