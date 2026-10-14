"""Exact integer counts for explicit edge-disjoint constructions."""
from math import comb

def C(n):
 if n<3:return 0
 leave={0:n//2,1:0,2:n//2,3:0,4:n//2+1,5:4}[n%6]
 return (n*(n-1)//2-leave)//3

def J(s,r):return (r//2)*min(s,r-1 if r%2==0 else r) if r else 0

def sparse(a,b,x,y,extra=False):
 r=(a+1)//2;t=(b+1)//2;s=a-r;u=b-t
 assert 0<=x<r and 0<=y<t
 base=J(r,s)+J(t,u)
 H=sum(v*(v-1)//2 for v in [r,s,t,u]);T=H+t*x+r*y-x*y
 ps={
 'cliques':C(a)+C(b),
 'P13B':C(t+x)+J(x+y,r-x)+base,
 'P13A':C(r+y)+J(x+y,t-y)+base,
 'P14':J(r+t-x-y,x+y)+base,
 'P15A':C(r)+J(x,t)+base,
 'P15B':C(t)+J(y,r)+base,
 'P16A':C(a)+J(x,t)+J(t,u),
 'P16B':C(b)+J(y,r)+J(r,s),
 'P17A':C(a)+J(x,t-1)+J(t-1,u+1),
 'P17B':C(b)+J(y,r-1)+J(r-1,s+1),
 'L2B':C(x+t)+J(x,a-x)+J(t,u),
 'L2A':C(r+y)+J(y,b-y)+J(r,s),
 'nearclique':C(r+t)-(r-x)*(t-y)+base,
 }
 if extra:
  # all pivot constructions on the canonical minimum profile
  deg=[t]*x+[y]*(r-x)+[0]*s
  for flip in (0,1):
   aa,bb,dd=(a,b,deg) if not flip else (b,a,[sum(d>=k for d in deg) for k in range(1,b+1)])
   for k in range(bb+1):
    p=sum(d>=k for d in dd) if k else aa
    ps[f'L1_{flip}_{k}']=C(aa)+J(p,k)+J(k,bb-k)
    ps[f'L2_{flip}_{k}']=C(p+k)+J(p,aa-p)+J(k,bb-k)
 return T,max(ps.values()),max(ps,key=ps.get),ps


def dense(a,b,x,y,extra=False):
 r=(a+1)//2;s=a-r;t=(b+1)//2;u=b-t
 assert r<=x<=a and t<=y<=b
 w=x-r;z=y-t;base=J(r,s)+J(t,u)
 H=sum(v*(v-1)//2 for v in (r,s,t,u));T0=H+r*t
 ps={
 'cliques':C(a)+C(b),
 'P3':J(x,t)+J(z,r)+base,
 'P3T':J(y,r)+J(w,t)+base,
 'L1A':C(a)+J(x,t)+J(t,u),
 'L1B':C(b)+J(y,r)+J(r,s),
 'L2A':C(x+t)+J(x,a-x)+J(t,u),
 'L2B':C(y+r)+J(y,b-y)+J(r,s),
 'P12plus':J(t,x)+J(r,z)+J(u,t)+max(C(a-x),J(x,a-x))+max(C(b-y),J(z,b-y)),
 'P12plusT':J(r,y)+J(t,w)+J(s,r)+max(C(b-y),J(y,b-y))+max(C(a-x),J(w,a-x)),
 }
 S0=C(x+y)-w*z+J(x,a-x)+J(y,b-y)
 if extra:
  deg=[y]*r+[t]*w+[0]*(a-x)
  for flip in (0,1):
   aa,bb,dd=(a,b,deg) if not flip else (b,a,[sum(d>=k for d in deg) for k in range(1,b+1)])
   for k in range(bb+1):
    p=sum(d>=k for d in dd) if k else aa
    ps[f'L1_{flip}_{k}']=C(aa)+J(p,k)+J(k,bb-k)
    ps[f'L2_{flip}_{k}']=C(p+k)+J(p,aa-p)+J(k,bb-k)
 P=max(ps.values());lo=max(0,2*P-T0+1);hi=min(w*z,T0-2*S0-1)
 return lo,hi,T0,P,S0,max(ps,key=ps.get)
