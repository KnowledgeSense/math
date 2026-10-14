import sympy as s,json
from pathlib import Path
N=4;m=3
xs=s.symbols('x0:12');Y=s.Matrix(N,m,xs)
K1=s.diag(1,2);K2=s.Matrix([[3]]);bs=[s.Rational(2,5),s.Rational(7,3)]
As=[Y[:,:2].T*Y[:,:2]+K1,Y[:,2:].T*Y[:,2:]+K2]
logF=bs[0]*s.log(As[0].det())+bs[1]*s.log(As[1].det())
point=dict(zip(xs,[1,2,-1, 2,-1,3, 0,1,2, 1,-2,1]));Q=s.diag(1,1,1,0);q=3
YY=Y.subs(point);AA=[a.subs(point) for a in As]
D=s.diag(bs[0]*AA[0].inv(),bs[1]*AA[1].inv())
terms=[]
for b,idx,A in zip(bs,[(0,2),(2,3)],AA):
 Z=YY[:,idx[0]:idx[1]];Ai=A.inv();H=Z.T*Q*Z;h=s.trace(Ai*H);T=Ai*H*Ai
 terms.append(2*b*((q-h)*Ai-T))
expected=s.diag(*terms)+4*D*YY.T*Q*YY*D
actual=s.zeros(m)
for a in range(3):
 grad=s.Matrix([s.diff(logF,Y[a,i]).subs(point) for i in range(m)])
 for i in range(m):
  for j in range(m):actual[i,j]+=s.diff(logF,Y[a,i],Y[a,j]).subs(point)+grad[i]*grad[j]
assert actual==expected
for k in range(1,4):assert expected[:k,:k].det()>0
# The lower-bound remainder is PSD, checked here at one rational input.
lower=s.diag(*[2*b*(q-(idx[1]-idx[0])-1)*A.inv() for b,idx,A in zip(bs,[(0,2),(2,3)],AA)])
res=expected-lower
for k in range(1,4):assert res[:k,:k].det()>0
out={'status':'PASS','matrix_identity_entries':9,'positive_leading_minors':6,'scope':'independent direct symbolic differentiation at a rational regularized 4-by-3 input; general proof is in the note'}
Path(__file__).with_name('partial_laplacian_exact_check.json').write_text(json.dumps(out,indent=2));print(out)
