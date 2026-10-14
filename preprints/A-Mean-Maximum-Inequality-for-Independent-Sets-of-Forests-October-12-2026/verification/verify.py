"""Exact verification of the mean--maximum inequality for forests.
Author: Knowledge Sense. Standard library only.

Run: python verify.py INPUT_DIRECTORY OUTPUT_JSON
INPUT_DIRECTORY contains cone_certificate.json and upper_witness_certificate.json.
The cone proof uses exact Fraction Gauss-Jordan elimination and direct reconstruction.
The upper witness uses root-absent/root-present counts and size sums.
"""
from fractions import Fraction
from pathlib import Path
from collections import Counter
from datetime import datetime, timezone
import json, math, hashlib, sys, time

sys.set_int_max_str_digits(0)
started=time.monotonic()
source=Path(sys.argv[1]); output=Path(sys.argv[2])
def require(test,message):
    if not test:raise ValueError(message)
def hashed(name,expected):
    data=(source/name).read_bytes()
    require(hashlib.sha256(data).hexdigest()==expected,'hash '+name)
    return json.loads(data)
d=hashed('cone_certificate.json','9fe1b777cfb6ba95a4fffdbb55bdaea356103b076f9db4d1b647e8224bdb4f3a')
require(d['c']==[47,100],'constant')
G={int(k):v for k,v in d['generators'].items()}
require(set(G)=={0,1} and [len(G[i]) for i in (0,1)]==[32,331],'generator counts')
for f,gs in G.items():
    require(len({tuple(v) for v in gs})==len(gs),'duplicates')
    for v in gs:require(len(v)==4 and all(type(x)==int for x in v) and math.gcd(*v)==1,'primitive integer generator')
    require([0,0,1,0] in gs and [0,0,0,1] in gs,'recession rays')
require(G[0][d['empty_generator']]==[1,1,0,0],'empty vector')
inverse_cache={};used=set()
def get_inverse(f,index):
    key=f,index
    if key in inverse_cache:return inverse_cache[key]
    indices=d['bases'][str(f)][index]
    require(len(indices)==4 and len(set(indices))==4 and all(type(i)==int and 0<=i<len(G[f]) for i in indices),'basis indices')
    original=[[G[f][indices[j]][i] for j in range(4)] for i in range(4)]
    a=[[Fraction(x) for x in row]+[Fraction(i==j) for j in range(4)] for i,row in enumerate(original)]
    for k in range(4):
        pivot=next((i for i in range(k,4) if a[i][k]),None)
        require(pivot is not None,'singular basis')
        a[k],a[pivot]=a[pivot],a[k]
        z=a[k][k];a[k]=[x/z for x in a[k]]
        for i in range(4):
            if i!=k:
                z=a[i][k];a[i]=[x-z*y for x,y in zip(a[i],a[k])]
    inv=[row[4:] for row in a]
    require(all(sum(inv[i][k]*original[k][j] for k in range(4))==int(i==j) for i in range(4) for j in range(4)),'inverse identity')
    rows=[]
    for row in inv:
        denom=math.lcm(*(x.denominator for x in row))
        rows.append((denom,[int(x*denom) for x in row]))
    inverse_cache[key]=(indices,rows)
    return indices,rows
# Also inspect every supplied basis, including bases not referenced by operations.
for f in (0,1):
    for index in range(len(d['bases'][str(f)])):get_inverse(f,index)
counts=Counter();ops=Counter();max_bits=0;minimum_root=None
def membership(v,f,record):
    global max_bits
    require(type(record)==list and len(record)>0 and type(record[0])==int and record[0] in range(4),'record type')
    typ=record[0];counts[typ]+=1
    max_bits=max(max_bits,*(abs(x).bit_length() for x in v))
    if typ==3:
        require(record==[3] and v==[0,0,0,0],'zero record');return
    require(len(record)==2 and type(record[1])==int,'record shape')
    index=record[1]
    if typ==2:
        require(0<=index<len(d['bases'][str(f)]),'basis range')
        indices,rows=get_inverse(f,index);used.add((f,index))
        coefficients=[Fraction(sum(a*b for a,b in zip(row,v)),den) for den,row in rows]
        require(all(x>=0 for x in coefficients),'negative basis coefficient')
        require(all(sum(coefficients[j]*G[f][indices[j]][i] for j in range(4))==v[i] for i in range(4)),'basis reconstruction')
    else:
        require(0<=index<len(G[f]),'generator range');g=G[f][index]
        if typ==0:
            scale=math.gcd(*v);require(scale>0 and all(x==scale*y for x,y in zip(v,g)),'multiple')
        else:
            require(v[0]>0 and g[0]>0,'positive scale')
            scale=Fraction(v[0],g[0])
            residual=[Fraction(x)-scale*y for x,y in zip(v,g)]
            require(residual[0]==residual[1]==0 and residual[2]>=0 and residual[3]>=0,'ray residual')
roots=d['operations']['roots'];require(set(roots)=={'0','1'},'root keys')
for f in (0,1):
    require(len(roots[str(f)])==len(G[f]),'root coverage')
    for (p,q,x,y),record in zip(G[f],roots[str(f)]):
        b=1-f;v=[100*(p+q),100*p,100*(x+y)+(100-47*b)*q-47*b*p,100*x-47*b*p]
        require(v[2]>=0,'negative root output')
        minimum_root=v[2] if minimum_root is None else min(minimum_root,v[2])
        membership(v,1-f,record);ops['root'+str(f)]+=1
products=d['operations']['products'];require(set(products)=={'00','01','11'},'product keys')
for label in ('00','01','11'):
    f,g=map(int,label);records=products[label]
    require(len(records)==len(G[f])*len(G[g]),'product coverage')
    for i,(p,q,x,y) in enumerate(G[f]):
        for j,(r,s,u,v) in enumerate(G[g]):
            membership([p*r,q*s,x*r+p*u,y*s+q*v],max(f,g),records[i*len(G[g])+j]);ops['product'+label]+=1
require(sum(counts.values())==121540,'total coverage')

w=hashed('upper_witness_certificate.json','a569d412c59356d4923ad4e78653ea04b6bc30f3f1e5d775dccc6a28afb5f89c')
# A,B: counts with root absent/present. U,V: sum of sizes. a,b: maximal sizes.
# n,degree,rootdegree follow the explicit fresh-root construction.
def R(*children):
    A,B,U,V,a,b,n,degree,rootdegree=1,1,0,1,0,1,1,len(children),len(children)
    for C,D,W,X,e,f,m,deg,rdeg in children:
        A,U,B,V=A*(C+D),U*(C+D)+A*(W+X),B*C,V*C+B*W
        a,b,n=a+max(e,f),b+e,n+m
        degree=max(degree,deg,rdeg+1)
    return A,B,U,V,a,b,n,degree,rootdegree
leaf=R()
def F(q):return R(leaf,R(q))
def M(q):
    u=R(q);v=R(u,u,u)
    return R(leaf,R(v,v,v,v,v,v,v))
q=F(R(leaf,leaf));sizes=[q[6]]
for j in range(3):q=F(M(q));sizes.append(q[6])
A,B,U,V,a,b,n,degree,rd=q;Z,S,alpha=A+B,U+V,max(a,b)
require((n,degree,alpha)==(71308,8,48619),'witness metadata')
require(Z==int(w['Z']) and S==int(w['total_cardinality']),'full witness integers')
require(a==w['root_absent_alpha'] and b==w['root_present_alpha'],'conditional alpha')
margin=473403*alpha*Z-1000000*S
require(margin>0,'strict witness upper bound')
from decimal import Decimal, localcontext
with localcontext() as ctx:
    ctx.prec=55; ratio=str(Decimal(S)/Decimal(alpha*Z)); gap=str(Decimal(margin)/Decimal(1000000*alpha*Z))
result={'author':'Knowledge Sense','completed_at_utc':datetime.now(timezone.utc).isoformat(),
        'elapsed_seconds':time.monotonic()-started,'checker_sha256':hashlib.sha256(Path(__file__).read_bytes()).hexdigest(),
        'method':'exact Fraction Gauss-Jordan inverse and direct vector reconstruction; root occupation dynamic programming for the witness',
        'cone':{'generators':[32,331],'operation_counts':dict(ops),'record_types':dict(counts),'operations':sum(counts.values()),'all_basis_count':len(inverse_cache),'used_basis_count':len(used),'minimum_root_third_coordinate':minimum_root,'maximum_generator_bits':max(abs(x).bit_length() for gs in G.values() for v in gs for x in v),'maximum_operation_image_bits':max_bits,'all_exact_checks_satisfied':True},
        'upper_witness':{'sizes_Q0_to_Q3':sizes,'vertices':n,'maximum_degree':degree,'alpha':alpha,'root_absent_alpha':a,'root_present_alpha':b,'Z_bits':Z.bit_length(),'S_bits':S.bit_length(),'ratio':ratio,'gap_to_0.473403':gap,'positive_integer_margin_bits':margin.bit_length(),'full_integers_match':True,'strict_upper_inequality':True}}
output.parent.mkdir(parents=True,exist_ok=True);output.write_text(json.dumps(result,ensure_ascii=False,indent=2)+'\n',encoding='utf-8')
print(json.dumps(result,ensure_ascii=False,indent=2))
