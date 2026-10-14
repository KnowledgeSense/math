"""Finite reproducibility checks for positive anti-recurrences. The general proof is given in the paper "A uniform discrepancy bound for anti-recurrence sequences" (Knowledge Sense).
Run with Python 3: python verify_bound.py
No external packages or network access required.
"""
import bisect, datetime, hashlib, itertools, json, random
from pathlib import Path

def audit(a, count):
    k, tau = len(a), sum(a)
    kap, A, B, occupied, cursor = k*tau+1, [], [], set(), 1
    blocks, holes, ranks = [], [], []
    for n in range(1, count+1):
        block = []
        for j in range(k):
            while cursor in occupied: cursor += 1
            block.append(cursor)
            cursor += 1
        value = sum(x*y for x,y in zip(a,block))
        assert value > block[-1] and value not in occupied
        if A: assert value-A[-1] >= k*tau
        occupied.add(value)
        A.append(value); B.extend(block)
        b = block[0]
        h = bisect.bisect_left(A, b)
        eps = [v-b-j for j,v in enumerate(block)]
        assert set(eps) <= {0,1} and eps[0] == 0
        delta = sum(x*y for x,y in zip(a,eps))
        assert 0 <= delta <= tau
        assert b == k*(n-1)+1+h and 0 <= h <= n-1
        assert value == k*tau*n+tau*h+A[0]-k*tau+delta
        if n >= 3: assert h <= n-2
        blocks.append(block); holes.append(delta); ranks.append(h)
    D = [0]+[v-kap*n for n,v in enumerate(A,1)]
    c, K = A[0]-k*tau, (k+1)*tau-A[0]+1
    max_previous = max(abs(D[1]),abs(D[2]))
    assert abs(D[1]) <= 2*kap and abs(D[2]) <= 2*kap
    for n in range(3,count+1):
        h=ranks[n-1]
        assert k*(D[n]-c+tau+1) >= 1-D[h+1]
        assert k*(D[n]-c-tau+1) <= -D[h]
        assert k*abs(D[n]) <= k*K+max_previous
        assert abs(D[n]) <= 2*kap
        max_previous=max(max_previous,abs(D[n]))
    first_outside=next((n for n,v in enumerate(A,1) if not kap*(n-1)+1<=v<=kap*n),None)
    return {'coefficients':a,'n_checked':count,'kappa':kap,'A1':A[0],
            'A1_bounded':A[0]<=(k-1)*tau+2,
            'discrepancy_min':min(D[1:]),'discrepancy_max':max(D[1:]),
            'first_outside_published_fixed_interval':first_outside,
            'A1741':A[1740] if count>=1741 else None,
            'first_terms':A[:12]}

def main():
    cases=[]
    for k, ceiling in [(2,15),(3,6),(4,4),(5,3),(6,2)]:
        cases.extend((list(a),2000) for a in itertools.product(range(1,ceiling+1),repeat=k))
    rng=random.Random(55)
    for _ in range(96):
        k=rng.randrange(2,17)
        cases.append(([rng.randrange(1,1000001) for _ in range(k)],3000))
    special=[[1,1],[1,2],[2,1],[1,3],[1,4],[1,1000000],[1000000,1],
             [1,1,1000000],[1000000,1,1],[1]*20,[1]*19+[1000000]]
    cases.extend((a,50000 if a==[1,4] else 10000) for a in special)
    results=[audit(a,n) for a,n in cases]
    out={'theorem':'positive anti-recurrence discrepancy','checked_at_utc':datetime.datetime.now(datetime.timezone.utc).isoformat(),
         'seed':55,'coefficient_vectors':len(results),'total_indices_checked':sum(x['n_checked'] for x in results),
         'verdict':'all_assertions_passed','interpretation':'Exact-integer checks of the stated identities, inequalities and final bound for finitely many coefficient vectors and indices.',
         'special_cases':results[-len(special):],'all_cases':results}
    p=Path(__file__).with_name('checks.json')
    p.write_text(json.dumps({k:v for k,v in out.items() if k!='all_cases'},ensure_ascii=False,indent=2),encoding='utf-8')
    print(json.dumps({k:v for k,v in out.items() if k!='all_cases'},ensure_ascii=False,indent=2))

if __name__=='__main__': main()
