"""Finite-jet verification for generator strata with values <10,11,34,46,58>.
Author: Knowledge Sense. Contact: math@knowledgesense.jp.
Requires Python 3.12 and SymPy 1.14.0.
"""
import json, itertools, hashlib, time, random, sys, argparse
from pathlib import Path
from sympy.polys.rings import ring
from sympy.polys.domains import QQ

parser=argparse.ArgumentParser(description=__doc__)
parser.add_argument('--output-dir',type=Path,default=Path('results'))
args=parser.parse_args()
args.output_dir.mkdir(parents=True,exist_ok=True)

start=time.perf_counter()
weights=(10,11,34,46,58)
names=('x','h','z','w','u')
reach={0}
for n in range(1,220):
    if any(n-v in reach for v in weights): reach.add(n)
gaps=[n for n in range(60) if n not in reach]
assert len(gaps)==33 and 59 not in reach and all(n in reach for n in range(60,220))
tails=[[g for g in gaps if g>v] for v in weights]
variables=[f'{name}{g}' for name,gs in zip(names,tails) for g in gs]
P,*gens=ring(','.join(variables),QQ)
syms=dict(zip(variables,gens)); zero=P.zero; one=P.one
def mul(a,b):
    c={}
    for i,ai in a.items():
        for j,bj in b.items():
            if i+j<60: c[i+j]=c.get(i+j,zero)+ai*bj
    return {i:v for i,v in c.items() if v}
def sub(a,b):
    c=a.copy()
    for i,v in b.items(): c[i]=c.get(i,zero)-v
    return {i:v for i,v in c.items() if v}
normal=[{v:one,**{g:syms[f'{name}{g}'] for g in gs}} for name,v,gs in zip(names,weights,tails)]
exps=[]
for a in itertools.product(*[range(60//v+1) for v in weights]):
    wt=sum(i*v for i,v in zip(a,weights))
    if wt<60: exps.append((wt,a))
group={}
for wt,a in exps: group.setdefault(wt,[]).append(a)
repeats={wt:aa for wt,aa in group.items() if len(aa)>1}
assert set(repeats)=={44,54,55,56}
chosen={wt:min(aa,key=lambda a:tuple(reversed(a))) for wt,aa in group.items()}
chosen.update({44:(1,0,1,0,0),54:(2,0,1,0,0),55:(1,1,1,0,0),56:(1,0,0,1,0)})
cache={tuple([0]*5):{0:one}}
def mon(a):
    if a not in cache:
        i=next(i for i,e in enumerate(a) if e)
        b=list(a);b[i]-=1
        cache[a]=mul(normal[i],mon(tuple(b)))
    return cache[a]
basis={wt:mon(a) for wt,a in chosen.items()}
def reduce(poly):
    r=poly.copy();quot={}
    for wt in sorted(basis):
        if wt==0: continue
        coef=r.get(wt,zero)
        if coef:
            quot[wt]=coef
            r=sub(r,{n:coef*v for n,v in basis[wt].items()})
    return r,quot
F=sub(mon((0,4,0,0,0)),mon((1,0,1,0,0)))
G=sub(mon((0,2,1,0,0)),mon((1,0,0,1,0)))
rf,qf=reduce(F);rg,qg=reduce(G)
assert set(rf)=={47,48,49,59} and set(rg)=={59}
eqs=[rf[47],rf[48],rg[59],rf[49],rf[59]]
elim=['z37','z38','w49','z39','z49']
checks=[]
for k,(eq,var) in enumerate(zip(eqs,elim)):
    assert eq.diff(syms[var])==-one
    assert all(not eq.diff(syms[v]) for v in elim[k+1:])
    checks.append({'variable':var,'coefficient':-1,'later_variables_absent':True,'expanded_terms':len(eq),'sha256':hashlib.sha256(str(eq).encode()).hexdigest()})
D=qf[45];A=qf[46];C=qf[58];E=qg[57];B=qg[58]
h12,h13,z35,z36,x12,w47,w48=[syms[v] for v in ['h12','h13','z35','z36','x12','w47','w48']]
assert D==4*h12-z35
assert A==4*h13+6*h12**2-z36-x12-D*(z35+h12)
assert E==2*h12+z35-w47
assert B==2*h13+h12**2+2*h12*z35+z36-w48-x12-E*(w47+h12)
assert A.diff(syms['z36'])==-one and not A.diff(syms['w48']) and not A.diff(syms['z48'])
assert B.diff(syms['w48'])==-one and not B.diff(syms['z48'])
assert C.diff(syms['z48'])==-one and not C.diff(syms['z49'])
assert all(not eq.diff(syms['z48']) for eq in eqs[:4])
symbolic={'semigroup_generators':weights,'conductor':60,'gaps':gaps,'tail_counts':list(map(len,tails)),
 'monomials_under_60':len(exps),'canonical_basis_dimension':len(group),'repeated_weights':repeats,
 'elimination':checks,'A_B_C_triangular_coordinate_checks':True,'C_expanded_terms':len(C)}
(args.output_dir/'ri10_symbolic.json').write_text(json.dumps(symbolic,ensure_ascii=False,indent=2),encoding='utf-8')
print('symbolic checks complete',json.dumps({'elapsed_seconds':time.perf_counter()-start,'equation_terms':[len(e) for e in eqs]}),flush=True)

# A separate implementation over prime fields verifies full algebra multiplication.
def vmul(a,b,p):
    c=[0]*60
    for i,v in enumerate(a):
        if v:
            for j,w in enumerate(b[:60-i]):
                if w:c[i+j]=(c[i+j]+v*w)%p
    return c
def row_reduce(rows,p):
    piv={}
    for row in rows:
        r=row[:]
        for j in sorted(piv):
            c=r[j]
            if c:r=[(v-c*w)%p for v,w in zip(r,piv[j])]
        j=next((i for i,c in enumerate(r) if c),None)
        if j is not None:
            inv=pow(r[j],-1,p);piv[j]=[(v*inv)%p for v in r]
    return piv
def numeric(coords,p):
    gs=[]
    for name,v,ts in zip(names,weights,tails):
        row=[0]*60;row[v]=1
        for n in ts:row[n]=coords[f'{name}{n}']%p
        gs.append(row)
    nc={tuple([0]*5):[1]+[0]*59}
    def nmon(a):
        if a not in nc:
            i=next(i for i,e in enumerate(a) if e);b=list(a);b[i]-=1
            nc[a]=vmul(gs[i],nmon(tuple(b)),p)
        return nc[a]
    nb={wt:nmon(a) for wt,a in chosen.items()}
    def nreduce(a):
        r=a[:];q={}
        for wt in sorted(nb):
            if not wt:continue
            q[wt]=r[wt];r=[(v-r[wt]*w)%p for v,w in zip(r,nb[wt])]
        return r,q
    f=[(v-w)%p for v,w in zip(nmon((0,4,0,0,0)),nmon((1,0,1,0,0)))]
    g=[(v-w)%p for v,w in zip(nmon((0,2,1,0,0)),nmon((1,0,0,1,0)))]
    fr,fq=nreduce(f);gr,gq=nreduce(g)
    return gs,nb,nmon,fr,gr,(fq.get(46,0),gq.get(58,0),fq.get(58,0))
random.seed(10122026)
num=[]
for p in [2,3,5,101]:
    for sample in range(24):
        coords={v:random.randrange(p) for v in variables}
        for var,which,n in [('z37',0,47),('z38',0,48),('w49',1,59),('z39',0,49),('z49',0,59)]:
            coords[var]=0
            gs,nb,nmon,fr,gr,abc=numeric(coords,p)
            coords[var]=(fr if which==0 else gr)[n]
        gs,nb,nmon,fr,gr,abc=numeric(coords,p)
        assert not any(fr) and not any(gr)
        allrows=[nmon(a) for wt,a in exps]
        positive=[nmon(a) for wt,a in exps if wt]
        square=[nmon(a) for wt,a in exps if sum(a)>=2]
        assert len(row_reduce(allrows,p))==27
        edim=len(row_reduce(positive,p))-len(row_reduce(square,p))
        a,b,c=abc;rank=2 if a*b%p else int(bool(a or b or c))
        assert edim==5-rank
        # All 27 by 27 products are tested, including the identity.
        for v,w in itertools.product(nb.values(),repeat=2):
            row=vmul(v,w,p)
            for wt in sorted(nb):
                coeff=row[wt]
                if coeff:row=[(x-coeff*y)%p for x,y in zip(row,nb[wt])]
            assert not any(row)
    num.append({'prime':p,'full_parameter_samples':24,'closure_products_per_sample':729,'all_passed':True})
family=[]
for p in [2,3,5,7]:
    counts={3:0,4:0,5:0}
    for s,d,e in itertools.product(range(p),repeat=3):
        coords={v:0 for v in variables};coords.update(z36=s,z38=s*d,z48=e,w48=d)
        gs,nb,nmon,fr,gr,(a,b,c)=numeric(coords,p)
        assert not any(fr) and not any(gr)
        assert (a,b,c)==((-s)%p,(s-d)%p,(-e)%p)
        edim=len(row_reduce([nmon(q) for wt,q in exps if wt],p))-len(row_reduce([nmon(q) for wt,q in exps if sum(q)>=2],p))
        counts[edim]+=1
    family.append({'prime':p,'triples':p**3,'exact_embedding_dimension_counts':counts})
result={'symbolic':symbolic,'finite_full_parameters':num,'finite_closed_family':family,'elapsed_seconds':time.perf_counter()-start,
 'status':'all asserted identities and finite checks passed','scope':'Universal proof is the mathematical argument; finite fields supplement it.'}
(args.output_dir/'ri10_independent_results.json').write_text(json.dumps(result,ensure_ascii=False,indent=2),encoding='utf-8')
print(json.dumps(result,ensure_ascii=False,indent=2))
