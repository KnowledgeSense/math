"""Reproduce the manuscript's numerical table and equal-B-exponent corollary.

Requires mpmath 1.3.0 and trace_word_verification.py in this directory.
"""
from pathlib import Path
from itertools import product
from fractions import Fraction as Q
import json
import mpmath as mp
from trace_word_verification import criterion, compositions, number


def table_ratio(exponent,n):
    mp.mp.dps=2000
    eps=mp.power(10,-exponent)
    h=Q(9,20)
    eta=mp.power(eps,mp.mpf(19)/2)
    z=mp.power(eps,number(h))
    sq=mp.sqrt(2)
    u=mp.matrix([[1,-1,sq],[-1,1,sq],[sq,sq,0]])/2
    r=mp.matrix([[1-z*z,0,-2*z],[0,1+z*z,0],[2*z,0,1-z*z]])/(1+z*z)
    v=r*u
    eig=[eps+eta,eta,1+eta]
    def a(power): return v*mp.diag([mp.power(x,number(power)) for x in eig])*v.T
    def b(power): return mp.diag([mp.power(x,number(power)) for x in eig])
    tr=lambda x:sum(x[i,i] for i in range(3))
    p=(Q(3,5),Q(1,5),Q(1,5))
    q=(Q(1,5),Q(3,5),Q(1,5))
    word=mp.eye(3)
    for pp,qq in zip(p,q): word=word*a(pp)*b(qq)
    extra=(n-3)*eta**2
    return (tr(word)+extra)/(tr(a(Q(1))*b(Q(1)))+extra)


def main():
    checks=0
    for denominator in range(2,15):
        for m in range(2,min(8,denominator)+1):
            q=(Q(1,m),)*m
            for p in compositions(denominator,m):
                interval=all(sum(p[(start+j)%m] for j in range(length))<=Q(length+1,m)
                             for start in range(m) for length in range(1,m))
                assert interval==(criterion(p,q) is not None)
                checks+=1
    # Leading spectral power of the six-factor example. An A label 0 selects v,
    # an A label 1 selects u; a B label 0 selects e_1 and 1 selects e_3.
    p=(Q(3,5),Q(1,5),Q(1,5));q=(Q(1,5),Q(3,5),Q(1,5));h=Q(9,20)
    powers=[]
    for x in product((0,1),repeat=3):
        for y in product((0,1),repeat=3):
            eigen=sum(p[i] for i in range(3) if x[i]==0)+sum(q[i] for i in range(3) if y[i]==0)
            small=sum(y[i]*(x[i]+x[(i+1)%3]) for i in range(3))
            powers.append((eigen+h*small,x,y))
    leading=min(item[0] for item in powers)
    minima=[item for item in powers if item[0]==leading]
    assert leading==Q(4,5) and len(minima)==1
    next_power=min(item[0] for item in powers if item[0]>leading)
    assert next_power==Q(1)
    assert minima[0][1:]==((1,0,0),(0,1,0))
    rows=[]
    expected=['3.11105','312.484','3.12500e+6','3.12500e+14']
    for exponent,shown in zip((20,40,80,160),expected):
        r3=table_ratio(exponent,3);r6=table_ratio(exponent,6)
        assert abs(r3/mp.mpf(shown)-1)<mp.mpf('0.000002')
        assert mp.nstr(r3,15)==mp.nstr(r6,15)
        rows.append(dict(epsilon=f'1e-{exponent}',n3_ratio=mp.nstr(r3,45),n6_ratio=mp.nstr(r6,45),paper_rounded_value=shown))
    result=dict(cyclic_interval_exact_vectors=checks,table_precision_digits=2000,
                table=rows,leading_spectral_exponent='4/5',next_spectral_exponent=str(next_power),leading_term_unique=True,
                leading_numerator_coefficient='1/16',leading_denominator_coefficient='2',
                asymptotic_ratio_coefficient='1/32',asymptotic_ratio_power='-1/10')
    Path(__file__).with_name('manuscript_additional_results.json').write_text(json.dumps(result,indent=2),encoding='utf-8')
    print(json.dumps(result,indent=2))


if __name__=='__main__': main()
