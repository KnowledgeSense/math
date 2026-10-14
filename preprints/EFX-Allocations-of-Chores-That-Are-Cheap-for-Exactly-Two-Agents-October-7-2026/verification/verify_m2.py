"""Independent finite checks of the supplied M2 existence proof.

Constructive implementation with an independent affine EFX checker.
Finite checks corroborate the proof and do not prove its universal quantifier.
"""
from collections import Counter, deque
from itertools import combinations, combinations_with_replacement, product
from pathlib import Path
import hashlib, json, random, time

ROOT = Path(__file__).resolve().parent
PACKET = ROOT / 'data'
coverage = Counter()
comparisons = 0

class Flow:
    def __init__(self, size): self.g = [[] for _ in range(size)]
    def add(self, u, v, c):
        a = [v, c, len(self.g[v])]; b = [u, 0, len(self.g[u])]
        self.g[u].append(a); self.g[v].append(b)
        return a
    def run(self, s, t):
        result = 0
        while True:
            parent = [None] * len(self.g); parent[s] = (-1, -1)
            queue = deque([s])
            while queue and parent[t] is None:
                u = queue.popleft()
                for k, a in enumerate(self.g[u]):
                    if a[1] and parent[a[0]] is None:
                        parent[a[0]] = (u, k); queue.append(a[0])
            if parent[t] is None: return result
            delta = 10**9; v = t
            while v != s:
                u, k = parent[v]; delta = min(delta, self.g[u][k][1]); v = u
            v = t
            while v != s:
                u, k = parent[v]; a = self.g[u][k]
                a[1] -= delta; self.g[v][a[2]][1] += delta; v = u
            result += delta

def allocation_flow(allowed, quota):
    m, n = len(allowed), len(quota)
    net = Flow(m+n+2); source = m+n; sink = source+1; arcs = []
    for e, choices in enumerate(allowed):
        net.add(source, e, 1)
        arcs.append([(v, net.add(e, m+v, 1)) for v in choices])
    for v, q in enumerate(quota): net.add(m+v, sink, q)
    if net.run(source, sink) != m: return None
    X = [[] for _ in quota]
    for e, choices in enumerate(arcs):
        owner = next(v for v, arc in choices if arc[1] == 0)
        X[owner].append(e)
    return X

def balanced(allowed, n, m):
    q, s = divmod(m, n)
    for long in combinations(range(n), s):
        quota = [q + (v in long) for v in range(n)]
        X = allocation_flow(allowed, quota)
        if X is not None: return X
    raise AssertionError('No balanced permitted allocation')

def cheap(E, X, v): return sum(v in E[e] for e in X)
def high(E, X, v): return len(X) - cheap(E, X, v)
def bad(E, X, S):
    return [(v,w) for v in sorted(S) for w in sorted(S)
            if v != w and cheap(E,X[v],v)>0
            and high(E,X[v],v)>high(E,X[w],v)]

def minimum(E, X, S):
    """Enumerate endpoint splits by edge type; uniform fillers are interchangeable."""
    vertices = sorted(S); quota = {v:len(X[v]) for v in S}
    available = sorted(e for v in S for e in X[v])
    types = {}; anchors = {v:[] for v in S}; fillers = []
    for e in available:
        endpoints = set(E[e]) & S
        if len(endpoints)==2: types.setdefault(E[e],[]).append(e)
        elif len(endpoints)==1: anchors[next(iter(endpoints))].append(e)
        else: fillers.append(e)
    best = None; best_bundles = None
    for split in product(*(range(len(ids)+1) for ids in types.values())):
        candidate = {v:anchors[v][:] for v in S}
        for ((u,v),ids), k in zip(types.items(),split):
            candidate[u].extend(ids[:k]); candidate[v].extend(ids[k:])
        residual = {v:quota[v]-len(candidate[v]) for v in S}
        if any(k<0 for k in residual.values()): continue
        current = [a[:] for a in X]; position = 0
        for v in vertices:
            current[v] = candidate[v] + fillers[position:position+residual[v]]
            position += residual[v]
        assert position == len(fillers)
        key = (sum(residual[v]**2 for v in S), len(bad(E,current,S)))
        if best is None or key<best: best, best_bundles = key, current
    assert best_bundles is not None
    return best_bundles

def validate_normal(E, X, S):
    B = bad(E,X,S); endpoints = []
    for i,j in B:
        L = high(E,X[j],j)
        assert high(E,X[i],i)==L+1
        assert all(E[e]==tuple(sorted((i,j))) for e in X[i] if i in E[e])
        assert all(E[e]==tuple(sorted((i,j))) for e in X[j] if j in E[e])
        assert cheap(E,X[j],j)>=2
        endpoints.extend([i,j])
        for v in (i,j):
            assert all(high(E,X[k],v)>=L+1 for k in S-{i,j})
    assert len(endpoints)==len(set(endpoints))
    return B

def verify(E, X):
    global comparisons
    assert sorted(e for bundle in X for e in bundle)==list(range(len(E)))
    for i, bundle in enumerate(X):
        a=cheap(E,bundle,i); b=len(bundle)-a
        ta,tb=(a-1,b) if a else (0,max(0,b-1))
        for j,target in enumerate(X):
            if i==j: continue
            c=cheap(E,target,i); d=len(target)-c
            alpha,beta=c-ta,d-tb
            assert beta>=0 and alpha+2*beta>=0, (i,j,alpha,beta,E,X)
            comparisons+=1

def construct(E,n,initial=None,initial_S=None,use_divisible=True):
    m=len(E); q,s=divmod(m,n); N=set(range(n))
    if m<n:
        coverage['q=0']+=1
        return [[v] if v<m else [] for v in range(n)]
    def deficiency(U): return m*len(U)-n*sum(bool(set(e)&U) for e in E)
    S=max((set(v for v in range(n) if mask>>v&1) for mask in range(1<<n)),
          key=lambda U:(deficiency(U),-len(U)))
    if initial_S is not None:
        assert deficiency(initial_S)==deficiency(S)
        S=set(initial_S)
    if deficiency(S)<=0:
        coverage['endpoint flow']+=1
        return balanced([list(e) for e in E],n,m)
    H=N-S
    allowed=[]
    for edge in E:
        p=set(edge)
        allowed.append(sorted((p|S) if p<=H else (p&S)))
    X=minimum(E,balanced(allowed,n,m),S) if initial is None else [bundle[:] for bundle in initial]
    if initial is not None:
        assert all(v in allowed[e] for v,bundle in enumerate(X) for e in bundle)
        Y=minimum(E,X,S)
        assert (sum(high(E,X[v],v)**2 for v in S),len(bad(E,X,S))) == (sum(high(E,Y[v],v)**2 for v in S),len(bad(E,Y,S)))
    B=validate_normal(E,X,S)
    if not B:
        coverage['minimum has no bad pair']+=1
        return X
    def find(v,predicate): return next(e for e in X[v] if predicate(e))
    def pair_edge(v,w): return find(v,lambda e:E[e]==tuple(sorted((v,w))))
    def filler(v): return find(v,lambda e:set(E[e])<=H)
    def move(e,v,w): X[v].remove(e); X[w].append(e)
    def swap(e,v,f,w): move(e,v,w); move(f,w,v)
    def reverse(i,j): swap(filler(i),i,pair_edge(j,i),j)
    def walk(v,w):
        visited=set()
        while True:
            assert v not in visited; visited.add(v)
            swap(filler(v),v,pair_edge(w,v),w)
            outgoing=[(a,b) for a,b in bad(E,X,S) if a==w]
            if not outgoing: return
            v,w=outgoing[0]
    def neutral(i,j,k,L):
        swap(filler(i),i,pair_edge(k,i),k)
        current=bad(E,X,S)
        if not current:
            coverage['neutral without replacement pair']+=1; return
        outgoing=[(a,b) for a,b in current if a==k]
        assert len(outgoing)==len(current)
        for _,w in outgoing:
            if any(k in E[e] and E[e]!=tuple(sorted((k,w))) for e in X[k]):
                walk(k,w); coverage['neutral followed by nonpure walk']+=1; return
        assert len(outgoing)==1
        _,w=outgoing[0]
        validate_normal(E,X,S)
        swap(pair_edge(j,i),j,pair_edge(w,k),w)
        coverage['neutral followed by cross exchange']+=1
    if s==0 and use_divisible:
        thin=[]; thick=[]
        for i,j in B:
            (thin if cheap(E,X[i],i)==1 else thick).append((i,j))
        if len(thick)%2:
            recipient=thick.pop()
            if thin:
                donor=thin.pop(); move(filler(donor[0]),donor[0],recipient[1])
            else:
                edge=filler(recipient[0]); move(edge,recipient[0],E[edge][0])
        for a,b in zip(thick[::2],thick[1::2]): move(filler(a[0]),a[0],b[1])
        for i,j in thin: move(pair_edge(i,j),i,j)
        coverage['divisible repair']+=1; return X
    special=[(i,j) for i,j in B if high(E,X[j],j)==q-1]
    ordinary=[p for p in B if p not in special]
    for i,j in special: move(pair_edge(i,j),i,j)
    if not ordinary:
        coverage['special pairs only']+=1; return X
    if len(ordinary)>=2:
        operations=[]
        for t,(i,j) in enumerate(ordinary):
            nxt=ordinary[(t+1)%len(ordinary)][0]
            operations.append((pair_edge(j,i),j,filler(nxt),nxt))
        for e,v,f,w in operations: swap(e,v,f,w)
        coverage['multiple ordinary pairs']+=1; return X
    i,j=ordinary[0]; L=high(E,X[j],j); P={i,j}; U=S-P
    if special:
        z=special[0][0]; swap(pair_edge(j,i),j,filler(z),z)
        coverage['ordinary plus special pair']+=1; return X
    if not U:
        if s==0: return construct(E,n,initial=X,initial_S=S,use_divisible=True)
        C=sum(set(e)==P for e in E)
        T=2*q+1 if C%2 else (2*q if 2*s<n else 2*q+2)
        hlist=sorted(H); collapsed=len(hlist); index={v:k for k,v in enumerate(hlist)}
        ca=[[collapsed] if set(e)==P else sorted([index[v] for v in e]+[collapsed]) for e in E]
        longs=m-T-q*len(H); assert 0<=longs<=len(H)
        for long in combinations(range(len(H)),longs):
            Y=allocation_flow(ca,[q+(v in long) for v in range(len(H))]+[T])
            if Y is not None: break
        else: raise AssertionError('Parity flow failed')
        X=[[] for _ in range(n)]
        for v,k in index.items(): X[v]=Y[k]
        small=[e for e in Y[-1] if set(E[e])==P]; large=[e for e in Y[-1] if set(E[e])!=P]
        assert len(large)%2==0
        X[i]=small[:C//2]+large[:len(large)//2]
        X[j]=small[C//2:]+large[len(large)//2:]
        coverage['isolated pair parity flow']+=1; return X
    donors=[v for v in sorted(U) if high(E,X[v],v)>0]
    if not donors:
        incident=[(v,k) for v in (i,j) for k in sorted(U)
                  if any(E[e]==tuple(sorted((v,k))) for e in X[k])]
        if incident:
            v,k=incident[0]
            if v==j: reverse(i,j); i,j=j,i
            assert L==0
            neutral(i,j,k,L); return X
        k=min(U); swap(pair_edge(j,i),j,X[k][0],k)
        X=minimum(E,X,U); residual=validate_normal(E,X,U)
        if residual:
            k,w=residual[0]; swap(filler(i),i,pair_edge(w,k),w)
            coverage['no donor with residual pair']+=1
        else: coverage['no donor without residual pair']+=1
        return X
    k=donors[0]
    if all(high(E,X[k],v)>=L+2 for v in P):
        swap(pair_edge(j,i),j,filler(k),k)
        coverage['direct buffer']+=1; return X
    if high(E,X[k],i)!=L+1: reverse(i,j); i,j=j,i
    assert high(E,X[k],i)==L+1
    if high(E,X[k],k)==L:
        neutral(i,j,k,L); return X
    assert high(E,X[k],k)==L+1
    if L==q-2:
        if len(X[k])==q:
            swap(filler(i),i,pair_edge(k,i),k); coverage['boundary short donor']+=1
        else:
            move(pair_edge(k,i),k,i)
            move(pair_edge(j,i),j,i); move(filler(i),i,j)
            coverage['boundary long donor']+=1
        return X
    assert L<=q-3
    original={v:high(E,X[v],v) for v in U}
    e=filler(i); f=pair_edge(j,i); g=pair_edge(k,i)
    move(e,i,j); move(f,j,k); move(g,k,i)
    v=k; visited={k}
    while True:
        targets=[w for w in sorted(U-{v}) if high(E,X[w],v)<original[v]+1]
        if not targets: break
        w=targets[0]; assert w not in visited
        assert original[w]<=original[v]
        swap(f,v,pair_edge(w,v),w); visited.add(w); v=w
    coverage['token chain']+=1
    return X

def main():
    started=time.monotonic(); tested=0; novel_region=0
    witness=json.loads((PACKET/'branch_cases.json').read_text())
    for record in witness['records']:
        E=[tuple(e) for e in record['edges']]; n=record['n']; S=set(record['S'])
        X=record['initial']; M=minimum(E,X,S)
        assert (sum(high(E,X[v],v)**2 for v in S),len(bad(E,X,S))) == (sum(high(E,M[v],v)**2 for v in S),len(bad(E,M,S)))
        validate_normal(E,X,S); verify(E,record['final']); verify(E,construct(E,n))
        verify(E,construct(E,n,initial=X,initial_S=S,use_divisible=False))
    witness_count=len(witness['records'])
    # A separately specified token-branch instance, with q=3 and L=0.
    token_bundles=[[(0,1),(0,1),(3,4)],[(0,1)]*3,[(0,2),(0,2),(3,4)],[(3,4)]*3,[(3,4)]*3]
    E=[]; X=[]
    for bundle in token_bundles:
        ids=[]
        for edge in bundle: ids.append(len(E)); E.append(edge)
        X.append(ids)
    verify(E,construct(E,5,initial=X,initial_S={0,1,2},use_divisible=False))
    exhaustive={}
    for n,max_m in [(2,12),(3,10),(4,10),(5,5)]:
        pairs=list(combinations(range(n),2)); count=0
        for m in range(max_m+1):
            for multiset in combinations_with_replacement(range(len(pairs)),m):
                E=[pairs[k] for k in multiset]
                verify(E,construct(E,n)); count+=1; tested+=1
        exhaustive[str(n)]={'max_m':max_m,'instances':count}
        print(json.dumps({'stage':'exhaustive','n':n,'instances':count}),flush=True)
    rng=random.Random(20261007); random_count=4000
    for run in range(random_count):
        n=rng.randrange(5,10); m=rng.randrange(n,7*n+1)
        pairs=list(combinations(range(n),2))
        mode=run%5
        if mode==0: weights=[1 for _ in pairs]
        elif mode==1: weights=[50 if u>=n-3 else 1 for u,v in pairs]
        elif mode==2: weights=[50 if (u,v)==(n-2,n-1) else rng.choice([0,0,1,2]) for u,v in pairs]
        elif mode==3: weights=[rng.choice([0,0,0,1,1,8]) for _ in pairs]
        else: weights=[30 if (u,v) in ((0,1),(2,3),(n-2,n-1)) else rng.choice([0,0,1]) for u,v in pairs]
        if not any(weights): weights[-1]=1
        E=rng.choices(pairs,weights=weights,k=m)
        try: verify(E,construct(E,n))
        except Exception:
            (ROOT/'failure.json').write_text(json.dumps({'n':n,'edges':E,'run':run},indent=2)); raise
        tested+=1; novel_region+=int(n>=5 and m>2*n)
        if run%500==499: print(json.dumps({'stage':'random','completed':run+1}),flush=True)
    result={'status':'PASS','reference_proof_sha256':'34cf6d5d9973164ba9fbb784387f9486ccb5ffb6ea46467db9c660e606960b97',
            'exhaustive_labeled_multigraphs':exhaustive,'random_seed':20261007,'random_instances':random_count,
            'random_n_range':[5,9],'random_m_upper_bound':'7*n','random_new_region_n_ge_5_m_gt_2n':novel_region,
            'whole_construction_instances':tested+2*witness_count+1,'author_witnesses_independently_checked':witness_count,
            'ordered_affine_inequalities':comparisons,'validity_of_checked_outputs':'all real r>=2',
            'construction_branch_coverage':dict(coverage),'elapsed_seconds':round(time.monotonic()-started,3),
            'limitation':'Finite testing is supporting evidence; it does not prove arbitrary n,m.'}
    (ROOT/'independent_results.json').write_text(json.dumps(result,indent=2)+'\n')
    print(json.dumps(result,indent=2),flush=True)

if __name__=='__main__': main()
