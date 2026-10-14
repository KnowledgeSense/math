"""Exact verification of the local quadratic bounds.

Author: Knowledge Sense
Contact: math@knowledgesense.jp
"""
from pathlib import Path
import sys
import sympy as sp
import itertools, json

out=Path(sys.argv[1]).resolve() if len(sys.argv)>1 else Path.cwd()/'audit_results'
out.mkdir(parents=True,exist_ok=True)
a,b,c,d,e=variables=sp.symbols('a b c d e',real=True)
r2=sp.sqrt(2)

def sign_exact(x):
    x=sp.expand(x)
    v=x.coeff(r2);u=sp.expand(x-v*r2)
    assert u.is_Rational and v.is_Rational,(u,v)
    if v==0:return int(bool(u>0))-int(bool(u<0))
    if u==0:return int(bool(v>0))-int(bool(v<0))
    if (u>0)==(v>0):return 1 if u>0 else -1
    diff=u*u-2*v*v
    assert diff!=0
    return (1 if u>0 else -1) if diff>0 else (1 if v>0 else -1)

def abs_exact(x):return sp.expand(x*sign_exact(x))
def greater(x,y):return sign_exact(sp.expand(x-y))>0

# Reconstruct the local Fourier formula from three shifted lambda values.
middle=2*c+sp.I*(d-b)
left=2*b+sp.I*(c-a)
right=2*d+sp.I*(e-c)
rho=sp.expand(middle**2-(1+sp.I)/(2*r2)*left**2-(1-sp.I)/(2*r2)*right**2)
R=sp.expand(sp.re(rho));J=sp.expand(-sp.im(rho))
R_paper=r2*a*a/4-r2*a*b-r2*a*c/2-(r2+1)*b*b+r2*b*c+2*b*d+(4+r2/2)*c*c+r2*c*d-r2*c*e/2-(r2+1)*d*d-r2*d*e+r2*e*e/4
J_paper=-r2*a*a/4-r2*a*b+r2*a*c/2+r2*b*b+(r2+4)*b*c-(4+r2)*c*d-r2*c*e/2-r2*d*d+r2*d*e+r2*e*e/4
assert sp.expand(R-R_paper)==0 and sp.expand(J-J_paper)==0

eps=sp.Rational(1,100)
rows=[];group_R={};boundary_J=[]
for occ in itertools.product((0,1),repeat=5):
    center=dict(zip(variables,occ));record={'occupancy':list(occ)}
    for name,Q in [('R',R),('J',J)]:
        q0=sp.expand(Q.subs(center))
        gradient=sum(abs_exact(sp.diff(Q,z).subs(center)) for z,u in zip(variables,occ) if u)
        restricted=sp.Poly(Q.subs({z:0 for z,u in zip(variables,occ) if not u}),*variables)
        remainder=sum(abs_exact(coef) for coef in restricted.coeffs())
        lower=sp.expand(q0-eps*gradient-eps**2*remainder)
        upper=sp.expand(q0+eps*gradient+eps**2*remainder)
        record[name]={'center':str(q0),'gradient_l1':str(gradient),'quadratic_coefficient_l1':str(remainder),'lower':str(lower),'upper':str(upper)}
        if name=='R':
            assert not greater(upper,sp.Rational(486,100))
            key=''.join(map(str,occ[1:4]))
            if key not in group_R or greater(upper,group_R[key]):group_R[key]=upper
        else:
            assert not greater(-8,lower) and not greater(upper,8)
            if occ[1:4]==(1,1,0):
                assert not greater(sp.Rational(527,100),lower)
                boundary_J.append({'outer':[occ[0],occ[4]],'lower':str(lower)})
    rows.append(record)

alpha=sp.Rational(99,100);beta=sp.Rational(101,100);eta=beta**2/100
margin=sp.Rational(527,100)*alpha**4-sp.Rational(486,100)*beta**4-2*sp.Rational(1286,100)*eta**2
assert margin==sp.Rational(58226264657,25000000000000)
assert margin>sp.Rational(1,500)
assert (alpha**2-sp.Rational(1,3))/beta>=sp.Rational(1,2)
assert 4/alpha+8<=13
assert 32*13**2==5408
assert 5408*500==2704000 and 6*2704000==16224000
assert 3<10**8*alpha**7
assert 2**8*10**8<=20**9

# Sanity check only: finite enumeration supplements the analytic count.
count=0
for mask in range(1,2**12):
    P={i+1 for i in range(12) if mask&(1<<i)};A=P|{-i for i in P}
    T=sum(m-t in A for m in A for t in A)
    B=sum(m-t in A and m+t not in A for m in A for t in A)
    C=sum(m-t in A and m+t in A for m in A for t in A)
    Q=sum(u+v in P for u in P for v in P)
    I=sum(u-v in A and u+v in P for u in P for v in P)
    assert T==6*Q and B==6*Q-4*I and T==B+C and C<=2*B
    count+=1

summary={'method':'Independent symbolic Fourier reconstruction; exact sign comparison in Q(sqrt(2)); all quadratic Taylor boxes; rational constants. Finite support enumeration is supplementary only.','R':str(R),'J':str(J),'all_boxes':rows,'grouped_R_upper':{k:str(v) for k,v in group_R.items()},'boundary_J_lower':boundary_J,'margin_exact':str(margin),'margin_decimal_for_display':str(sp.N(margin,18)),'combinatorial_sanity_sets':count,'checks_passed':True}
(out/'certificate.json').write_text(json.dumps(summary,ensure_ascii=False,indent=2),encoding='utf-8')
print(json.dumps({k:summary[k] for k in ['checks_passed','grouped_R_upper','boundary_J_lower','margin_exact','combinatorial_sanity_sets']},ensure_ascii=False,indent=2))
