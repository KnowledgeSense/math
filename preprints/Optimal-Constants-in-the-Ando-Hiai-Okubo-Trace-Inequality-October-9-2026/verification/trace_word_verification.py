"""Finite checks accompanying Optimal constants for alternating trace words.

Python 3, standard library for exact tests; mpmath for two numerical examples.
Run: python trace_word_verification.py
Outputs: verification_results.json in the same directory.
"""
from fractions import Fraction as Q
from itertools import combinations
from pathlib import Path
import json
import mpmath as mp


def compositions(total, k):
    for bars in combinations(range(1, total), k-1):
        marks = (0, *bars, total)
        yield tuple(Q(marks[i+1]-marks[i], total) for i in range(k))


def criterion(p, q):
    c = [Q(0)]
    for i in range(1, len(p)):
        c.append(c[-1]+p[i]-q[i-1])
    lo = max(max(-x, y-x-Q(1, 2)) for x,y in zip(c,q))
    hi = min(min(Q(1, 2)-x, y-x) for x,y in zip(c,q))
    if lo > hi:
        return None
    a = tuple(lo+x for x in c)
    b = tuple(q[i]-a[i] for i in range(len(p)))
    assert all(0 <= x <= Q(1,2) for x in a+b)
    assert all(a[i]+b[i]==q[i] and a[i]+b[i-1]==p[i] for i in range(len(p)))
    return a,b


def min_cut(p, q):
    k = len(p)
    best = None
    for smask in range(1<<k):
        for tmask in range(1<<k):
            s = tuple(i for i in range(k) if smask>>i&1)
            t = tuple(i for i in range(k) if tmask>>i&1)
            edges = sum(int(i in s)+int((i+1)%k in s) for i in t)
            theta = 2-sum(p[i] for i in s)-sum(q[i] for i in t)
            item = (theta+Q(edges,2), theta, edges, s, t)
            if best is None or item[0] < best[0]:
                best = item
    return best


def split_chart(p, q, a, b):
    pp = (a[0], *p[1:], b[-1])
    qq = (*q, Q(0))
    for j in range(len(pp)):
        alpha = sum(pp[:j+1])-sum(qq[:j])
        assert alpha == (a[j] if j<len(p) else 0)
        assert 0 <= alpha <= Q(1,2)
        if j < len(p):
            beta = sum(qq[:j+1])-sum(pp[:j+1])
            assert beta == b[j] and 0 <= beta <= Q(1,2)


def number(x):
    return mp.mpf(x.numerator)/x.denominator if isinstance(x,Q) else mp.mpf(x)


def example(p,q,n,target):
    cut,theta,edges,s,t = min_cut(p,q)
    assert cut < 1 and edges in (0,1)
    h = (theta/(2-edges)+Q(1,2))/2
    delta = (2-edges)*h-theta
    c = Q(1,4**(2*len(p)))
    cap = 2*len(p)*n*2**(2*len(p)-1)
    mp.mp.dps = 800
    hh,dd,cc = number(h),number(delta),number(c)
    eps = min(mp.mpf(1),mp.power(8,-1/hh),
              mp.power(cc/(2*cap),1/(1+dd)),
              mp.power(cc/(2*(n+9)*(target+1)),1/dd))/2
    eta = mp.power(eps,(2*hh+1)/number(min(p+q)))
    z = mp.power(eps,hh)
    rt = mp.sqrt(2)
    u = mp.matrix([[1,-1,rt],[-1,1,rt],[rt,rt,0]])/2
    rot = mp.matrix([[1-z*z,0,-2*z],[0,1+z*z,0],[2*z,0,1-z*z]])/(1+z*z)
    v3 = rot*u
    v = mp.eye(n)
    for i in range(3):
        for j in range(3):
            v[i,j] = v3[i,j]
    ev = [eps+eta,eta,1+eta]+[eta]*(n-3)
    def power_a(r):
        return v*mp.diag([mp.power(x,number(r)) for x in ev])*v.T
    def power_b(r):
        return mp.diag([mp.power(x,number(r)) for x in ev])
    trace = lambda mat: sum(mat[i,i] for i in range(n))
    word = mp.eye(n)
    for a,b in zip(p,q):
        word = word*power_a(a)*power_b(b)
    ratio = trace(word)/trace(power_a(Q(1))*power_b(Q(1)))
    bound = cc*mp.power(eps,-dd)/(2*(n+9))
    assert ratio >= bound > target
    return dict(p=list(map(str,p)),q=list(map(str,q)),dimension=n,target=target,
                cut_capacity=str(cut),theta=str(theta),edges=edges,
                h=str(h),delta=str(delta),epsilon=mp.nstr(eps,40),
                eta=mp.nstr(eta,40),ratio=mp.nstr(ratio,40),
                proved_lower_bound=mp.nstr(bound,40))


def main():
    counts = {'rational_vectors':0,'AHO_splits':0,'cuts':0,'cyclic_rotations':0}
    for denominator in range(1,9):
        for k in range(1,min(5,denominator)+1):
            vectors = list(compositions(denominator,k))
            for p in vectors:
                for q in vectors:
                    counts['rational_vectors'] += 1
                    ab = criterion(p,q)
                    cut = min_cut(p,q)
                    counts['cuts'] += 1
                    assert (ab is not None) == (cut[0] >= 1)
                    if ab is not None:
                        split_chart(p,q,*ab)
                        counts['AHO_splits'] += 1
                    for shift in range(k):
                        assert (criterion(p[shift:]+p[:shift],q[shift:]+q[:shift]) is not None) == (ab is not None)
                        counts['cyclic_rotations'] += 1
    plevnik = 0
    for den in range(2,81):
        for num in range(1,den):
            t = Q(num,den)
            assert (criterion((t,1-t),(1-t,t)) is not None) == (Q(1,4)<=t<=Q(3,4))
            plevnik += 1
    p = (Q(4,5),Q(1,10),Q(1,10))
    q = (Q(1,3),)*3
    cut = min_cut(p,q)
    assert cut[0] == cut[1] == Q(13,15) and cut[2] == 0
    examples = [example((Q(3,5),Q(1,5),Q(1,5)),(Q(1,5),Q(3,5),Q(1,5)),3,10),
                example((Q(4,5),Q(1,5)),(Q(1,5),Q(4,5)),5,100)]
    result = dict(exact_checks=counts,plevnik_slice_vectors=plevnik,
                  furuichi_cut_capacity=str(cut[0]),numerical_examples=examples,
                  numerical_precision_digits=mp.mp.dps,
                  scope='Finite illustrations of the analytic proof. No finite computation supplies the arbitrary-length theorem.')
    Path(__file__).with_name('verification_results.json').write_text(json.dumps(result,indent=2),encoding='utf-8')
    print(json.dumps(result,indent=2))


if __name__=='__main__':
    main()
