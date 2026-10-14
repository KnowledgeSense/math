"""Independent finite audit. PYTHONPATH must contain SymPy. No network or input mutation.

Eulerian coefficients are computed using the alternating-sum formula.
This is evidence for identities and endpoint assertions; the general proof is analytic.
"""
from pathlib import Path
import sympy as s
import json,sys

x,w,z=s.symbols('x w z')
A={}
H={}
for n in range(1,19):
    # Coefficient of x^j: sum_{i=0}^{j+1} (-1)^i binom(n+1,i) (j+1-i)^n.
    A[n]=s.Poly(sum(sum((-1)**i*s.binomial(n+1,i)*(j+1-i)**n for i in range(j+2))*x**j for j in range(n)),x)
    d=(n-1)//2;e=(n-1)%2
    rem=s.Poly(s.div(A[n],s.Poly((x+1)**e,x))[0],x)
    assert s.rem(A[n],s.Poly((x+1)**e,x)).is_zero
    h=0
    for j in range(d,-1,-1):
        c=rem.nth(d+j)
        h+=c*w**j
        rem=s.Poly(s.expand(rem.as_expr()-c*x**d*(x+1/x)**j),x)
    assert rem.is_zero
    H[n]=s.Poly(h,w)
    assert s.gcd(H[n],H[n].diff()).degree()==0
    assert H[n].count_roots(-s.oo,-2)==d

# Tangent numbers from tan'=1+tan^2, independent of the Eulerian evaluations.
b=[s.Rational(0)]*21
for j in range(20):
    b[j+1]=((1 if j==0 else 0)+sum(b[i]*b[j-i] for i in range(j+1)))/s.Integer(j+1)
E={j:b[j]*s.factorial(j) for j in range(1,21,2)}
table=[]
for n in range(3,19):
    d=(n-1)//2;e=(n-1)%2;m=n//2
    lo=-s.Integer(n*(n-1));hi=-E[2*m+1]/E[2*m-1]
    assert -H[n].eval(2)/H[n-2].eval(2)==lo
    assert -H[n].eval(-2)/H[n-2].eval(-2)==hi
    assert lo<hi
    assert s.gcd(H[n],H[n-2]).degree()==0
    for val,point,mult in [(lo,1,2),(hi,-1,2+e)]:
        p=s.Poly(A[n].as_expr()+val*x*A[n-2].as_expr(),x)
        q=s.Poly(s.div(p,s.Poly((x-point)**mult,x))[0],x)
        assert s.rem(p,s.Poly((x-point)**mult,x)).is_zero
        assert q.eval(point)!=0
        assert s.gcd(q,q.diff()).degree()==0
        assert q.count_roots(-s.oo,0)==q.degree()
    table.append({'n':n,'lower':str(lo),'upper':str(hi),'lower_multiplicity':2,'upper_multiplicity':2+e,'other_endpoint_roots_simple_negative':True})

result={'status':'PASS','scope':'Independent alternating-sum construction n=1..18; endpoint checks n=3..18. Not an all-degree proof.','python':sys.version.split()[0],'sympy':s.__version__,'rows':table}
Path(__file__).with_name('independent_R30_results.json').write_text(json.dumps(result,ensure_ascii=False,indent=2)+'\n',encoding='utf-8')
print(json.dumps(result,ensure_ascii=False,indent=2))
