"""Finite verification for spherical tree independence polynomials. Author: Knowledge Sense. Python 3.12+, standard library only.

Run: python verify.py [output_json]
Finite exact arithmetic checks support, but do not replace, the asymptotic proof.
"""
from decimal import Decimal, localcontext
from fractions import Fraction
from functools import lru_cache
from math import comb
from pathlib import Path
import hashlib
import json
import sys


def add(a, b):
    out = [0] * max(len(a), len(b))
    for j, v in enumerate(a): out[j] += v
    for j, v in enumerate(b): out[j] += v
    return out


def mul(a, b):
    out = [0] * (len(a) + len(b) - 1)
    for i, v in enumerate(a):
        for j, w in enumerate(b): out[i+j] += v*w
    return out


def path_poly(n):
    return [comb(n+1-j, j) for j in range((n+1)//2+1)]


def spherical_graph(m, n):
    core_count = 2**(m+1)-1
    edges = [(i, (i-1)//2) for i in range(1, core_count)]
    nv = core_count
    for leaf in range(2**m-1, core_count):
        parent = leaf
        for _ in range(n):
            edges.append((parent, nv))
            parent = nv
            nv += 1
    adj = [0]*nv
    for a, b in edges:
        adj[a] |= 1 << b
        adj[b] |= 1 << a
    return adj


def graph_coefficients(adj):
    # Arbitrary induced graph deletion recurrence, independent of binary-tree formula.
    @lru_cache(None)
    def solve(mask):
        if not mask: return (1,)
        bit = mask & -mask
        v = bit.bit_length()-1
        absent = solve(mask ^ bit)
        present = (0,) + solve((mask ^ bit) & ~adj[v])
        return tuple(add(absent, present))
    full = (1 << len(adj))-1
    return list(solve(full)), list(solve(full ^ 1)), [0]+list(solve((full ^ 1) & ~adj[0]))


def binary_formula(m, n):
    absent, present = path_poly(n), [0]+path_poly(n-1)
    for _ in range(m):
        absent, present = mul(add(absent, present), add(absent, present)), [0]+mul(absent, absent)
    return add(absent, present), absent, present


def finite_exact():
    records = []
    cases = [(0,n) for n in (1,3,5,7,9)] + [(1,n) for n in (1,3,5,7)] + [(2,n) for n in (1,3)] + [(3,1)]
    for m,n in cases:
        adj = spherical_graph(m,n)
        actual, c0, c1 = graph_coefficients(adj)
        proposed, p0, p1 = binary_formula(m,n)
        assert (actual,c0,c1) == (proposed,p0,p1)
        k = (n-1)//2
        alpha = ((3*k+5)*2**m - (2 if m%2 == 0 else 1))//3
        assert (3*k+5)*2**m - (2 if m%2 == 0 else 1) == 3*alpha
        assert len(actual)-1 == alpha
        assert len(adj) == (n+2)*2**m-1
        assert max(a.bit_count() for a in adj) <= 3
        for coeffs in (c0,c1):
            support = [j for j,a in enumerate(coeffs) if a]
            assert support == list(range(min(support),max(support)+1))
            # Root-required path n=1 at depth 0 is a degenerate exception outside the theorem.
            if n >= 3 or m >= 1: assert len(support) >= 2
        activity = Fraction(7,3)
        unnormalised = [Fraction(a)*activity**j for j,a in enumerate(actual)]
        partition = sum(unnormalised)
        probs = [a/partition for a in unnormalised]
        for j in range(1,alpha):
            coeff_det = actual[j-1]*actual[j+1]-actual[j]**2
            mass_det = probs[j-1]*probs[j+1]-probs[j]**2
            assert mass_det == Fraction(coeff_det)*activity**(2*j)/partition**2
            dp,dm = probs[j+1]-probs[j],probs[j]-probs[j-1]
            assert mass_det == probs[j]*(dp-dm)-dp*dm
        records.append({'m':m,'n':n,'vertices':len(adj),'alpha':alpha,'coefficients':actual,'root_supports':[[j for j,a in enumerate(c) if a] for c in (c0,c1)]})
    for k in range(1,31):
        odd,even = path_poly(2*k+1),path_poly(2*k)
        D = 4*(k+1)**2
        for j in range(k+2):
            a = comb(k+1+j,2*j)
            assert odd[k+1-j] == a
            assert a*__import__('math').factorial(2*j) <= D**j
        for j in range(k+1):
            a = Fraction(comb(k+1+j,2*j+1),k+1)
            assert Fraction(even[k-j],k+1) == a
            assert a*__import__('math').factorial(2*j) <= D**j
    return {'case_count':len(records),'all_exact_checks_passed':True,'cases':records,'reverse_polynomial_cases':30}


def reverse_series(k, y, odd):
    term,total,weighted = Decimal(1),Decimal(1),Decimal(0)
    limit = k+1 if odd else k
    for j in range(1,limit+1):
        if odd:
            term *= Decimal((k+1+j)*(k+2-j))*y/Decimal(2*j*(2*j-1))
        else:
            term *= Decimal((k+1+j)*(k+1-j))*y/Decimal((2*j+1)*2*j)
        total += term
        weighted += j*term
        if term < Decimal('1e-85'): break
    return total, weighted/total


def numeric_tuning(k=16384):
    with localcontext() as ctx:
        ctx.prec = 100
        def evaluate(r):
            activity = r*(1+r)**2
            so,mo = reverse_series(k,1/activity,True)
            se,me = reverse_series(k,1/activity,False)
            return Decimal(k+1)*se/so-r,activity,mo,me
        lo,hi = Decimal(k)/2,Decimal(k)*2
        assert evaluate(lo)[0] > 0 and evaluate(hi)[0] < 0
        for _ in range(300):
            mid=(lo+hi)/2
            if evaluate(mid)[0] > 0: lo=mid
            else: hi=mid
        r=(lo+hi)/2
        residual,activity,mo,me=evaluate(r)
        p=r/(1+r); gamma=2*p; pi=p/(1+p)
        kappa=mo-me-1/(1+gamma)
        rho=Decimal(k+1)+pi-(1-pi)*mo-pi*me
        astar=Decimal(k)+Decimal(5)/3
        q=rho/astar
        exponent=gamma.ln()/Decimal(2).ln()
        assert abs(residual) < Decimal('1e-75')
        assert kappa < Decimal('-0.25')
        assert astar-rho > Decimal(1)/6
        # Exact subtree message formula evaluated at the numerical crossing.
        odds=r
        for _ in range(20): odds=activity/(1+odds)**2
        assert abs(odds-r) < Decimal('1e-65')
        values={'k':k,'n':2*k+1,'r':r,'lambda':activity,'p':p,'gamma':gamma,'pi_occ':pi,'mu_o':mo,'mu_e':me,'kappa':kappa,'run_exponent':exponent,'center_ratio_q':q,'one_minus_q':1-q,'A_star_minus_rho_star':astar-rho,'boundary_residual':residual}
        return {'arithmetic':'Decimal, precision 100; approximate illustration, no certified asymptotic threshold','values':{key:str(value) for key,value in values.items()}}


def martingale_check():
    records=[]
    for p in (Fraction(9,10),Fraction(99,100)):
        gamma=2*p; pi=p/(1+p)
        for root in (0,1):
            var=Fraction(0); occupation=Fraction(root)
            for h in range(1,13):
                # 2^h children, each stochastic only when its parent is absent.
                increment=Fraction(2**h)*(1-occupation)*p*(1-p)/gamma**(2*h)
                var += increment
                occupation=p*(1-occupation)
            assert 0 < var <= p*(1-p)/(2*p*p-1) <= 2*(1-p)
            mean=Fraction(root)-pi
            records.append({'p':str(p),'root':root,'mean_M_h':str(mean),'variance_M_12':str(var),'variance_upper_bound':str(p*(1-p)/(2*p*p-1))})
    return records


if __name__ == '__main__':
    result={'scope':'Independent finite verification plus numerical parameter illustration. The main asymptotic theorem is justified by the accompanying mathematical proof.','finite':finite_exact(),'tuning':numeric_tuning(),'martingale':martingale_check()}
    result['script_sha256']=hashlib.sha256(Path(__file__).read_bytes()).hexdigest()
    out=Path(sys.argv[1]) if len(sys.argv)>1 else Path(__file__).with_name('verification.json')
    out.write_text(json.dumps(result,ensure_ascii=False,indent=2)+'\n',encoding='utf-8')
    print(json.dumps({'all_exact_checks_passed':True,'case_count':result['finite']['case_count'],'tuning':result['tuning']['values'],'output':str(out.resolve())},ensure_ascii=False))
