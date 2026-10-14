"""Exact rational verification of the dense large-order certificate.
Uses only the Python standard library. No graph census or numerical optimization.
"""
from fractions import Fraction as F
from itertools import permutations

class Poly:
    def __init__(self,data=None): self.c={k:F(v) for k,v in (data or {}).items() if v}
    @staticmethod
    def const(v): return Poly({(0,0,0,0):v})
    @staticmethod
    def var(i):
        e=[0]*4;e[i]=1;return Poly({tuple(e):1})
    def __add__(self,other):
        if not isinstance(other,Poly):other=Poly.const(other)
        d=self.c.copy()
        for k,v in other.c.items():d[k]=d.get(k,F(0))+v
        return Poly(d)
    __radd__=__add__
    def __neg__(self):return Poly({k:-v for k,v in self.c.items()})
    def __sub__(self,other):return self+-other if isinstance(other,Poly) else self+(-F(other))
    def __rsub__(self,other):return -self+other
    def __mul__(self,other):
        if not isinstance(other,Poly):other=Poly.const(other)
        d={}
        for k,v in self.c.items():
            for l,u in other.c.items():
                e=tuple(a+b for a,b in zip(k,l));d[e]=d.get(e,F(0))+v*u
        return Poly(d)
    __rmul__=__mul__
    def __truediv__(self,other):return self*F(1,other)
    def __pow__(self,n):
        assert n>=0
        p=Poly.const(1)
        for _ in range(n):p=p*self
        return p
    def subst(self,values):
        out=Poly()
        for exp,c in self.c.items():
            p=Poly.const(c)
            for v,n in zip(values,exp):p=p*(v**n)
            out=out+p
        return out
    def zero(self):return not self.c

def det(m):
    n=len(m);v=F(0)
    for p in permutations(range(n)):
        sg=(-1)**sum(p[i]>p[j] for i in range(n) for j in range(i+1,n))
        term=F(sg)
        for i in range(n):term*=m[i][p[i]]
        v+=term
    return v
r,t,w,z=[Poly.var(i) for i in range(4)];N=r+t;h=t-r
Fc=(N+w+z)**2/3+(r-w)**2+(t-z)**2-r*r-t*t-r*t-2*w*z
Lc=(r*r+t*t)/3-r*t
D00=t*w+r*z
Q00=Fc+F(3,4)*D00+F(1,4)*Lc
rhs=F(4,3)*(z-(h+w)/2)**2+h*h/48+r*w/12+F(3,4)*h*w+w*w+r*z/12
assert (Q00-N*N/16-rhs).zero()
records=[
 (0,1,[F(5,34),F(0),F(53,136)],F(43,816),[F(0),F(67,136),F(0)],
  [[F(13,6),F(-11,8),F(1)],[F(-11,8),F(4,3),F(-2,3)],[F(1),F(-2,3),F(4,3)]],
  [F(13,6),F(575,576),F(125,144)]),
 (1,0,[F(1,2),F(5,32),F(1,16)],F(29,768),[F(-57,64),F(0),F(0)],
  [[F(35,12),F(-1),F(11,8)],[F(-1),F(4,3),F(-2,3)],[F(11,8),F(-2,3),F(4,3)]],
  [F(35,12),F(26,9),F(269,144)]),
 (1,1,[F(25,59),F(33,118),F(25,59)],F(71,354),[F(-16,59),F(0),F(16,59)],
  [[F(11,3),F(-1),F(1)],[F(-1),F(4,3),F(-2,3)],[F(1),F(-2,3),F(4,3)]],
  [F(11,3),F(35,9),F(32,9)])]
for wi,zi,p,mn,g,M,minor in records:
    D=t*(r+w if wi==0 else t)+r*(z if zi==0 else r)-r*t
    Q=(Fc+F(3,4)*D+F(1,4)*Lc).subst([r,1-r,w,z])
    vv=[r-p[0],w-p[1],z-p[2]]
    rhs=Poly.const(mn)+sum(gi*vi for gi,vi in zip(g,vv))+sum(M[i][j]*vv[i]*vv[j] for i in range(3) for j in range(3))
    assert (Q-rhs).zero(),(wi,zi)
    for k in (1,2,3):
        m=det([row[:k] for row in M[:k]])
        assert m==minor[k-1] and m>0
    assert mn>=F(29,768)
assert F(29,768)*88**2-F(10,3)*88+2==F(13,12)
assert F(29,384)*88-F(10,3)>0
print('PASS: all four dense quadratic identities, nine positive minors, and N=88 threshold are exact')
