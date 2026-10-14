#!/usr/bin/env python3
"""Exact certificate verifier for the range p >= 100. Python standard library only.

The cube is reconstructed by tensor evaluation and exact Bernstein-collocation
matrix inversion, not the author's sparse expansion/conversion algorithm.
All 64 chord bounds are rederived with Fraction powers and certified floor bins.
Usage: python3 check_tail_F.py [fixed topic directory] [output JSON]
"""
from fractions import Fraction as Q
from math import comb, factorial
from pathlib import Path
import datetime, hashlib, json, sys, time

HERE = Path(__file__).resolve().parent
TOPIC = Path(sys.argv[1]) if len(sys.argv) > 1 else HERE/'fixed_inputs/components/near-two-and-large-exponents'
OUTPUT = Path(sys.argv[2]) if len(sys.argv) > 2 else HERE/'independent_exact.json'

def transpose(a):
    return list(map(list, zip(*a)))

def matrix_product(a, b):
    return [[sum((x*y for x,y in zip(row,col)), Q(0)) for col in transpose(b)] for row in a]

def inverse(a):
    n=len(a)
    aug=[list(row)+[Q(i==j) for j in range(n)] for i,row in enumerate(a)]
    for col in range(n):
        pivot=next(i for i in range(col,n) if aug[i][col])
        aug[col],aug[pivot]=aug[pivot],aug[col]
        z=aug[col][col];aug[col]=[x/z for x in aug[col]]
        for i in range(n):
            if i!=col:
                z=aug[i][col];aug[i]=[x-z*y for x,y in zip(aug[i],aug[col])]
    assert [r[:n] for r in aug]==[[Q(i==j) for j in range(n)] for i in range(n)]
    return [r[n:] for r in aug]

def polynomial_value(root,x,y):
    # Independently evaluate (T7) after the geometric maps (T8).
    if root==0:
        v=Q(1,10)+Q(2,5)*x;u=1-v+v*y
    else:
        v=Q(1,2)+x/2;u=v+(1-v)*y
    assert Q(1,10)<=v<=u<=1 and u+v>=1
    return 31*u*u*v*v-(1+u*u+v*v)*(4*u*v-(u+v-1)**2)**2

def cube_check():
    saved=json.loads((TOPIC/'logs/cube_far_bernstein.json').read_text())
    nodes=[Q(i,6) for i in range(7)]
    mat=[[comb(6,j)*x**j*(1-x)**(6-j) for j in range(7)] for x in nodes]
    inv=inverse(mat)
    assert matrix_product(mat,inv)==[[Q(i==j) for j in range(7)] for i in range(7)]
    roots=[]
    for root in range(2):
        values=[[polynomial_value(root,x,y) for y in nodes] for x in nodes]
        bern=matrix_product(matrix_product(inv,values),transpose(inv))
        assert matrix_product(matrix_product(mat,bern),transpose(mat))==values
        assert len(bern)==7 and all(len(row)==7 for row in bern)
        assert bern==[[Q(t) for t in row] for row in saved['roots'][root]['initial_bernstein']]
        # Expand the reconstructed Bernstein basis (reverse of author route).
        powers={}
        for i in range(7):
            for j in range(7):
                assert bern[i][j]>0
                for r in range(7-i):
                    for s in range(7-j):
                        key=(i+r,j+s)
                        value=bern[i][j]*comb(6,i)*comb(6,j)*comb(6-i,r)*comb(6-j,s)*(-1)**(r+s)
                        powers[key]=powers.get(key,Q(0))+value
        powers={k:v for k,v in powers.items() if v}
        assert powers=={(i,j):Q(c) for i,j,c in saved['roots'][root]['power_coefficients']}
        # Additional exact off-grid evaluations catch matrix orientation mistakes.
        for x,y in [(Q(1,11),Q(3,13)),(Q(7,17),Q(11,19)),(Q(23,29),Q(5,31))]:
            value=sum((c*x**i*y**j for (i,j),c in powers.items()),Q(0))
            assert value==polynomial_value(root,x,y)
        roots.append({'root':root,'positive_coefficients':49,'minimum':str(min(map(min,bern))),
                      'bernstein':[[str(c) for c in row] for row in bern],
                      'power_coefficients':[[i,j,str(c)] for (i,j),c in sorted(powers.items())]})
    minimum=min(Q(r['minimum']) for r in roots)
    assert minimum==Q(509,120000)==Q(saved['minimum_bernstein_coefficient'])
    assert saved['nodes']==saved['leaves']==2
    assert [r['root'] for r in saved['leaf_certificates']]==[0,1]
    for r in saved['leaf_certificates']:
        assert r['path']=='' and list(map(Q,r['box']))==[0,1,0,1]
        assert Q(r['min_coefficient'])==Q(roots[r['root']]['minimum'])
    return {'method':'exact tensor Bernstein collocation at 7x7 nodes; reverse basis expansion',
            'count':98,'minimum':str(minimum),'roots':roots}

def constants_check():
    # log 2 < 7/10 follows from exp(7/10) > its degree-3 Taylor sum > 2.
    exp_lower=sum((Q(7,10)**k/factorial(k) for k in range(4)),Q(0))
    assert exp_lower>2
    reference_squared=32*(1-Q(18,2500))**2
    assert reference_squared>31
    assert Q(728,25)<31
    assert Q(19,20)**100<Q(3,500)
    assert Q(1007,1000)**100>2
    assert 1-Q(8,500)==Q(123,125)>Q(49,50)
    assert Q(16,500)*Q(19,20)/Q(497,500)==Q(1520,49700)<Q(123,125)
    assert 1+Q(123,125)**2>Q(49,25)==Q(7,5)**2
    # 4 sqrt(2)<6, together with S0>49/25, gives 75/49.
    assert 32<36 and Q(6)/(2*Q(49,25))==Q(75,49)
    assert (Q(72,25)/Q(9,5))==Q(8,5)
    assert (Q(72,25)/Q(9,10))==Q(16,5)
    return {'exp_0_7_lower':str(exp_lower),'reference_squared_lower_at_100':str(reference_squared),
            'reference_squared_margin_over_31':str(reference_squared-31),
            'cube_first_case_squared_upper':'728/25','u_lower':'123/125',
            'R_lower':'497/500','displacement_over_R_upper':'1520/49700'}

def chord_check():
    saved=json.loads((TOPIC/'logs/tail_chord_100.json').read_text())
    assert saved['bin_count']==64 and len(saved['rows'])==64
    endpoints=[Q(19*j,1280) for j in range(65)]
    assert endpoints[0]==0 and endpoints[-1]==Q(19,20)
    total=Q(0);rows=[];largest_k=Q(0)
    for j,(lo,hi) in enumerate(zip(endpoints,endpoints[1:])):
        assert hi-lo==Q(19,1280)
        K=Q(1007,1000)*(Q(8,5)+Q(16,5)*hi/Q(497,500))
        assert 0<K<5<100
        largest_k=max(largest_k,K)
        rho=(1-K/100)**100
        assert 0<rho<1
        exact=Q(1000,1007)**3*rho/(1+rho)**2
        scaled=exact*10**8
        numerator=scaled.numerator//scaled.denominator
        kappa=Q(numerator,10**8)
        assert 0<kappa<=exact<kappa+Q(1,10**8)
        row=saved['rows'][j]
        assert [Q(row['z_lower']),Q(row['z_upper']),Q(row['K_upper'])]==[lo,hi,K]
        assert row['kappa_lower_numerator']==numerator and row['kappa_lower_denominator']==10**8
        contribution=2*kappa*(hi**3-lo**3)/3
        total+=contribution
        # Full rational exact factors are retained, not merely positivity booleans.
        rows.append({'j':j,'lo':str(lo),'hi':str(hi),'K':str(K),'rho':str(rho),
                     'curvature_factor_exact':str(exact),'kappa':str(kappa),
                     'rounding_slack':str(exact-kappa),'integral_contribution':str(contribution)})
    assert total==Q(1218353129184303,104857600000000000)
    loss=Q(7,5)*99*total;gain=Q(75,49);margin=loss-gain
    assert loss==Q(844318718524721979,524288000000000000)
    assert margin==Q(2050017207711376971,25690112000000000000)>0
    for key,val in [('kappa_integral_lower',total),('chord_loss_coefficient_lower',loss),
                    ('jacobian_increase_coefficient_upper',gain),('strict_margin',margin)]:
        assert Q(saved[key])==val
    return {'count':64,'K_max':str(largest_k),'integral':str(total),'loss':str(loss),
            'jacobian_bound':str(gain),'strict_margin':str(margin),'rows':rows}

def main():
    start=datetime.datetime.now(datetime.timezone.utc);tick=time.perf_counter()
    proof_hash=hashlib.sha256((TOPIC/'tail-component-proof.md').read_bytes()).hexdigest()
    assert proof_hash=='02d6669ccc24d275574beeb78210ffed045caeacf4bbe1ebddc3a9396997bb9d'
    result={'status':'PASS exact certificate checks','proof_sha256':proof_hash,
            'arithmetic':'Python integer and Fraction only, no floating-point proof arithmetic',
            'cube':cube_check(),'constants':constants_check(),'chords':chord_check()}
    result.update(start_utc=start.isoformat(),finish_utc=datetime.datetime.now(datetime.timezone.utc).isoformat(),
                  wall_seconds=time.perf_counter()-tick)
    OUTPUT.write_text(json.dumps(result,indent=2)+'\n')
    print(json.dumps({k:v for k,v in result.items() if k not in ['cube','chords']},indent=2))
    print('98 Bernstein coefficients and 64 full chord bins agree; positive strict margin',result['chords']['strict_margin'])

if __name__=='__main__':main()
