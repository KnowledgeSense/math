"""Arithmetic and symbolic checks for general line cones and the leading-form map.

Uses the manuscript's JSON only as data to audit, never its Python modules.
Run with SymPy 1.14; output is adjacent to this script.
"""
from pathlib import Path
import json,math,hashlib
import sympy as sp

source=Path(__file__).resolve().parent/'data'
bridge=json.loads((source/'compile_one_seed_bridge_v2.json').read_text())['rows']
assert len(bridge)==74
count=0
for index,row in enumerate(bridge):
    degree=row['d']
    assert degree==11+index and row['lower']==2*degree-8
    if index==0:
        assert row['upper']==14
        continue
    old=bridge[index-1]; e=degree-1;D=math.comb(e+2,2)
    covered=set()
    for interval in row['covering_intervals']:
        c=interval['c'];lo=interval['residual_lower'];hi=interval['residual_upper']
        assert old['lower']<=lo<=hi<=old['upper']
        assert (interval['lower'],interval['upper'])==(lo+c,hi+c)
        if interval['kind']=='extended_sparse':
            assert e>=2*c*c+2*c-3
            q=math.ceil((e+1-2*c)/c)+1
            need=(q+1)*(e-1)-q*(q+1)//2+2*e-2-2*q
            assert e+c+1<=lo and hi<=D-need
        else:
            ell=e+1-2*c;t=e+2-c
            if ell>=0:
                q=math.ceil(ell/c)+1;p=2
                need=(q+1)*(e+1)-q*(q+1)//2
            else:
                assert t>=3
                q=-ell;h0=(t-1)//2;p=(q+h0-1)//h0+2
                need=2*e+1
            assert lo>=max(e+3,p*(e+1)+p*(p+1)//2+2-c)
            assert hi<=D-need and interval['p']==p
        assert interval['q']==q and interval['required_k']==need
        covered.update(range(lo+c,hi+c+1));count+=1
    assert set(range(row['lower'],row['upper']+1))<=covered
assert count==188 and (bridge[-1]['lower'],bridge[-1]['upper'])==(160,2640)

d,s=sp.symbols('d s',integer=True,positive=True)
M=(d+1)*(d+2)/2;L=d*(d+1)*(d+2)/6
F=sp.expand(s*(M-s)-3*(L+s)+4)
assert sp.expand(F-F.subs(s,M-3-s))==0
assert sp.expand(F.subs(s,d+2)+4*(d+1))==0
assert sp.expand(F.subs(s,d+3)-(d-11)*(d+2)/2)==0
minor=sp.Matrix([[d,0,0,d*(d-1)/2],[0,d,0,d*(d-1)/2],[0,0,d,d*(d-1)/2],[d-1,0,0,(d-1)*(d-2)/2]])
determinant=sp.factor(minor.det());assert determinant==-d**3*(d-1)/2

# The analytic tail inequalities are checked as polynomials with
# nonnegative coefficients after replacing the integer threshold by x+threshold.
x=sp.symbols('x',nonnegative=True)
polynomials={
 'sparse_gap':3*d**2/8-7*d-427,
 'tail_overlap':d**2/9-sp.Rational(25,6)*d-426,
 'new_old_band_overlap':d-47,
 'c3_upper_gate':(2*(d-30)**2+88*(d-30)+1391)/9,
}
for name,poly in polynomials.items():
    shifted=sp.Poly(poly.subs(d,x+(30 if name=='c3_upper_gate' else 84)),x)
    assert all(v>=0 for v in shifted.all_coeffs()) and shifted.eval(0)>0
for poly in [(x**2-9*x+30)/2,(x**2-7*x+22)/2]:
    pp=sp.Poly(poly,x);assert sp.discriminant(pp.as_expr(),x)<0 and pp.LC()>0

# Every small-band position is reduced to a q3 endpoint with d0>=29.
for degree in range(29,201):
    for position in range(degree+3,2*degree-25):
        d0=2*degree+3-position;t=degree-d0
        assert d0>=29 and t==position-degree-3
        for j in range(1,t+1):
            e=d0+j-1;res=d0+2*j+1
            assert e+3<=res<=2*e-2
    if degree>=30:
        assert 2*degree-26>=degree+4
    if degree>=31:
        assert 2*degree-26>=degree+5
        e=degree-1;q=(e-5+2)//3+1
        need=(q+1)*(e-1)-q*(q+1)//2+2*e-2-2*q
        assert math.comb(e+2,2)-need>=3*e-56

# Summed omitted branches: O(D^2), compared with branches through degree D,
# which grow as D^3/6. This also bounds a partly included last layer.
omitted=8*d+429
assert sp.expand(omitted-(M-(M-7*d-427-(d+3)+1)))==0
examples=[]
for degree in [27,29,30,84,87,100,200]:
    leading=math.comb(degree+2,3);trace=math.comb(degree+2,2)
    rec=dict(d=degree,q3_s=degree+3,q3_r=leading+degree+3,q3_rank=3*(leading+degree+3)-4)
    if degree>=84:
        lower=degree+3;upper=trace-7*degree-427
        rec.update(s_interval=[lower,upper],r_interval=[leading+lower,leading+upper],positions=upper-lower+1)
    examples.append(rec)

record=dict(bridge_degrees=74,bridge_intervals=count,bridge_all_hypotheses_checked=True,
 polynomial_F=str(F),F_at_d_plus_2=str(sp.factor(F.subs(s,d+2))),F_at_d_plus_3=str(sp.factor(F.subs(s,d+3))),
 cartesian_minor=str(determinant),tail_symbolic_inequalities={name:str(sp.factor(poly.subs(d,x+(30 if name=='c3_upper_gate' else 84)))) for name,poly in polynomials.items()},
 small_band_integer_consistency_degrees=[29,200],omitted_per_complete_layer=str(omitted),examples=examples,
 bridge_source_sha256=hashlib.sha256((source/'compile_one_seed_bridge_v2.json').read_bytes()).hexdigest())
path=Path(__file__).with_suffix('.json');path.write_text(json.dumps(record,ensure_ascii=False,indent=2),encoding='utf-8')
print(json.dumps(record,ensure_ascii=False,indent=2))
