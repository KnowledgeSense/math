"""Exact arithmetic checks for generic valuation semigroups.
Author: Knowledge Sense. Contact: math@knowledgesense.jp.
Uses only the Python standard library.
"""
import argparse, functools, itertools, json, math, pathlib, time

def exponent_vectors(r,limit):
    def rec(i,remaining,prefix):
        if i==len(r):
            yield tuple(prefix);return
        for a in range((remaining-1)//r[i]+1):
            yield from rec(i+1,remaining-a*r[i],prefix+[a])
    yield from rec(0,limit,[])

def greedy_enumeration(r):
    limit=4*sorted(r)[0]*sorted(r)[1]
    weights=sorted(sum(a*b for a,b in zip(alpha,r)) for alpha in exponent_vectors(r,limit))
    values=[];prev=-1
    for w in weights:
        prev=max(w,prev+1)
        if prev>=limit:break
        values.append(prev)
    gaps=sorted(set(range(limit))-set(values))
    D=max(w-j for j,w in enumerate(weights))
    c=gaps[-1]+1 if gaps else 0
    assert len(gaps)==D
    return D,c,gaps

def compute(r):
    """Compute genus and conductor by integer DP, distinguishing coordinate variables."""
    if len(r)<2 or any(a<1 for a in r):raise ValueError('Requires d>=2 and positive integer orders')
    r=tuple(sorted(r));limit=4*r[0]*r[1]
    if r[0]==1:return {'r':r,'genus':0,'conductor':0,'gaps':[],'minimal_generators':[1],'cutoff':limit}
    p=[0]*limit;p[0]=1
    for a in r:
        for n in range(a,limit):p[n]+=p[n-a]
    M=0;D=0;c=0
    for n,count in enumerate(p):
        F=n-M
        if F>D:D,c=F,n
        M+=count
    pending=0;gaps=[]
    for n,count in enumerate(p):
        pending+=count
        if pending:pending-=1
        else:gaps.append(n)
    assert len(gaps)==D and (gaps[-1]+1 if gaps else 0)==c
    vals=set(range(c+r[0]))-set(gaps)
    gens=[n for n in sorted(vals) if n>0 and not any(n-a in vals for a in vals if 0<a<n)]
    return {'r':r,'genus':D,'conductor':c,'gaps':gaps,'minimal_generators':gens,'cutoff':limit}

def normalize(v):
    g=functools.reduce(math.gcd,v)
    if g:v=[a//g for a in v]
    first=next((a for a in v if a),0)
    return [-a for a in v] if first<0 else v

def pivot_orders(columns,N):
    basis={}
    for col in columns:
        v=normalize(col)
        for i in sorted(basis):
            if v[i]:
                b=basis[i];v=normalize([b[i]*a-v[i]*z for a,z in zip(v,b)])
        pivot=next((i for i,a in enumerate(v) if a),None)
        if pivot is not None:basis[pivot]=v
    return sorted(basis)

def witness(r,N):
    alphas=list(exponent_vectors(r,N))
    eps=[(N+1)**i for i in range(len(r))]
    spread=max(sum(a*b for a,b in zip(alpha,eps)) for alpha in alphas)
    C=spread+1;lams=[C*a+b for a,b in zip(r,eps)]
    facts=[math.factorial(i) for i in range(N)]
    columns=[];weights=[]
    for alpha in alphas:
        w=sum(a*b for a,b in zip(alpha,r));la=sum(a*b for a,b in zip(alpha,lams))
        columns.append([0 if n<w else facts[n]//facts[n-w]*la**(n-w) for n in range(N)])
        weights.append(w)
    target=[];prev=-1
    for w in sorted(weights):
        prev=max(w,prev+1)
        if prev>=N:break
        target.append(prev)
    actual=pivot_orders(columns,N)
    assert actual==target,(r,N,actual,target)
    return {'r':r,'cutoff':N,'columns':len(columns),'pivot_orders':actual}

def determinant(a):
    a=[row[:] for row in a];n=len(a);den=1;sgn=1
    for k in range(n-1):
        if not a[k][k]:
            j=next((j for j in range(k+1,n) if a[j][k]),None)
            if j is None:return 0
            a[k],a[j]=a[j],a[k];sgn=-sgn
        pivot=a[k][k]
        for i in range(k+1,n):
            for j in range(k+1,n):a[i][j]=(a[i][j]*pivot-a[i][k]*a[k][j])//den
            a[i][k]=0
        den=pivot
    return sgn*a[-1][-1] if n else 1

def audit(output):
    start=time.perf_counter();minor_count=positive=0
    for q in range(1,5):
        for orders in itertools.combinations_with_replacement(range(5),q):
            for rows in itertools.combinations(range(7),q):
                nodes=[2*j+1 for j in range(q)]
                a=[[0 if u<v else math.factorial(u)//math.factorial(u-v)*la**(u-v) for v,la in zip(orders,nodes)] for u in rows]
                det=determinant(a);admissible=all(u>=v for u,v in zip(rows,orders))
                assert (det>0 if admissible else det==0),(orders,rows,det)
                minor_count+=1;positive+=admissible
    vectors=list(itertools.combinations_with_replacement(range(1,11),2))+list(itertools.combinations_with_replacement(range(1,8),3))+list(itertools.combinations_with_replacement(range(1,6),4))
    for r in vectors:
        result=compute(r);D,c,gaps=greedy_enumeration(r)
        assert (result['genus'],result['conductor'],result['gaps'])==(D,c,gaps)
        vals=set(range(2*c+max(r)+1))-set(gaps)
        assert all(x+y in vals for x in vals if x<=c for y in vals if y<=c)
    plane_cases=0
    for a in range(2,31):
        for b in range(a,31):
            z=compute((a,b));e=math.gcd(a,b)
            expected_genus=((a-1)*(b-1)+e-1)//2
            assert z['genus']==expected_genus and z['conductor']==2*expected_genus,(a,b,z)
            plane_cases+=1
    cases=[(1,1),(1,7),(2,2),(2,4),(3,3),(3,6),(4,6),(4,4,4),(6,8,10),(4,6,9),(3,3,3,3),(4,5,7,8),(7,9,11)]
    witnesses=[witness(r,min(80,compute(r)['conductor']+min(r)+2)) for r in cases]
    examples=[compute(r) for r in [(2,2),(4,6),(6,8,10),(20,22,24),(4,4,4),(3,3,3,3)]]
    asym=[]
    for l in [10,30,100,300]:
        z=compute((2*l,2*l+2,2*l+4));z={k:v for k,v in z.items() if k not in {'gaps','minimal_generators'}}
        z['ell']=l;z['genus_over_ell_1_5']=z['genus']/l**1.5;z['difference_divided_by_ell']=(z['genus']-8*l**1.5/3)/l;asym.append(z)
    oldgens=(6,8,10,17,19);reach={0}
    for n in range(1,60):
        if any(n-a in reach for a in oldgens):reach.add(n)
    oldgaps=sorted(set(range(60))-reach)
    result={'minor_checks':minor_count,'positive_admissible_minors':positive,'combinatorial_vectors':len(vectors),'classical_plane_cases':plane_cases,'exact_integer_witnesses':witnesses,'examples':examples,'asymptotic_examples':asym,'old_2022_predicted_generators':oldgens,'old_2022_predicted_semigroup_gaps':oldgaps,'old_2022_predicted_semigroup_genus':len(oldgaps),'old_2022_claimed_genus_at_m_3':9,'old_2022_counterexample':{'order':21,'generic_coefficient':'2*a3-2*a1-a2','polynomial':'f3^2-f1^2*f2'},'seconds':time.perf_counter()-start}
    pathlib.Path(output).write_text(json.dumps(result,ensure_ascii=False,indent=2),encoding='utf-8')
    print(json.dumps({k:v for k,v in result.items() if k not in {'exact_integer_witnesses','examples'}},ensure_ascii=False,indent=2))

if __name__=='__main__':
    p=argparse.ArgumentParser(description=__doc__);p.add_argument('orders',type=int,nargs='*');p.add_argument('--audit',action='store_true');p.add_argument('--output',default='results.json');args=p.parse_args()
    if args.audit:audit(args.output)
    else:print(json.dumps(compute(args.orders),ensure_ascii=False,indent=2))
