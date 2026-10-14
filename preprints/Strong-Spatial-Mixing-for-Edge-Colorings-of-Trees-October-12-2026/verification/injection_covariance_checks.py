"""Exact checks for weighted injection covariance identities. Author: Knowledge Sense."""
from fractions import Fraction as F
from itertools import permutations
from pathlib import Path
import random, json, math, hashlib

rng=random.Random(20261012)
def diag(v): return [[x if i==j else F(0) for j in range(len(v))] for i,x in enumerate(v)]
def outer(v): return [[x*y for y in v] for x in v]
def add(a,b,scale=1): return [[x+scale*y for x,y in zip(aa,bb)] for aa,bb in zip(a,b)]
def scale(a,t): return [[x*t for x in row] for row in a]
def mm(a,b): return [[sum((x*y for x,y in zip(row,col)),F(0)) for col in zip(*b)] for row in a]
def block(p,k): return scale(add(diag([x*x for x in p]),outer(p),-1),F(1,k))

def moments(W):
    k,q=len(W),len(W[0]); n=k*q
    atoms=[]; Z=F(0)
    for cs in permutations(range(q),k):
        wt=math.prod((W[i][c] for i,c in enumerate(cs)),start=F(1))
        if wt: atoms.append((tuple(i*q+c for i,c in enumerate(cs)),wt)); Z+=wt
    assert Z>0
    p=[F(0)]*n; moment=[[F(0)]*n for _ in range(n)]
    for ids,wt in atoms:
        for x in ids:
            p[x]+=wt/Z
            for y in ids: moment[x][y]+=wt/Z
    cov=add(moment,outer(p),-1)
    return atoms,Z,p,cov

results=[]
for k in (2,3,4):
    q=k+4
    for rep in range(4):
        W=[]
        for i in range(k):
            while True:
                row=[F(rng.randrange(4),3) for _ in range(q)]
                if sum(row)>k: break
            W.append(row)
        atoms,Z,p,cov=moments(W); n=k*q
        s=min(map(sum,W))-k; t=s+1
        lower=W; checked=0
        for c in range(q):
            ids=[i*q+c for i in range(k)]; pc=[p[x] for x in ids]; rc=sum(pc)
            A=block(pc,k)
            EA=[[F(0)]*k for _ in range(k)]; Epp=[[F(0)]*k for _ in range(k)]
            for x,px in enumerate(p):
                if not px: continue
                # Conditional moments obtained from atom enumeration, then remove the pinned row.
                child=[sum((wt for cells,wt in atoms if x in cells and u in cells),F(0))/(Z*px) if u//q != x//q else F(0) for u in ids]
                expected=[pc[i]+cov[u][x]/px-(F(1) if x==u else F(0)) for i,u in enumerate(ids)]
                assert child==expected
                Epp=add(Epp,scale(outer(child),px/k))
                EA=add(EA,scale(block(child,k-1),px/k))
            Q=[[sum((cov[u][x]*cov[v][x]/p[x] for x in range(n) if p[x]),F(0)) for v in ids] for u in ids]
            assert Epp==add(outer(pc),scale(add(Q,diag(pc),-1),F(1,k)))
            G=[[F(0)]*k for _ in range(k)]
            for x,px in enumerate(p):
                if not px or x%q==c: continue
                z=[cov[u][x] if i!=x//q else F(0) for i,u in enumerate(ids)]
                G=add(G,scale(outer(z),1/px))
            inverse=diag([F(k)/x if x else F(0) for x in pc])
            lhs=add(add(scale(EA,k-1),scale(A,-(k-2))),mm(mm(A,inverse),A))
            rhs=scale(add(diag([pc[i]**2*(rc-pc[i])+G[i][i] for i in range(k)]),G,-1),F(1,k))
            assert lhs==rhs
            V=F(q)*(k+s)/t**2
            assert all(G[i][i]<=4*V*(k-1)*pc[i]/t**2 for i in range(k))
            assert 1-rc>=s/(k+s)
            checked+=1
        for x,px in enumerate(p):
            i,c=divmod(x,q)
            assert W[i][c]*t/(q*(k+s))<=px<=W[i][c]/t
        results.append({'k':k,'q':q,'s':str(s),'W':[[str(x) for x in row] for row in W],'states':len(atoms),'exact_identity_color_blocks':checked})

# An exact obstruction to the tempting noncommuting-product shortcut.
Sigma=[[F(1,2),F(1,2)],[F(1,2),F(1,2)]]; R=diag([F(1),F(1,4)])
gap=add(R,mm(mm(Sigma,R),Sigma),-1)
det=gap[0][0]*gap[1][1]-gap[0][1]*gap[1][0]
assert det==F(-9,64)
out={'seed':20261012,'exact_instances':results,'identity_blocks':sum(r['exact_identity_color_blocks'] for r in results),'shortcut_counterexample_determinant':str(det),'all_checks_pass':True,'scope':'Finite exact diagnostics; universal theorem follows from the analytic proof.'}
path=Path(__file__).with_name('injection_covariance_checks_results.json'); path.write_text(json.dumps(out,ensure_ascii=False,indent=2),encoding='utf-8')
print(json.dumps({k:v for k,v in out.items() if k!='exact_instances'},ensure_ascii=False,indent=2))
