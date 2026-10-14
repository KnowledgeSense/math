from pathlib import Path
from boundary_symbolic_core_v1 import *
records=[]
for h in[2,4,6,8,10,14]:
 cols,cc,val,ker=orig(h);V=ker[0];terms=get_terms(h,V,cols,0)
 for sm in range(6):
  for k in range(8):
   co=coefficient_terms(terms,sm,k)
   if co!=0:break
  a,b=s.fraction(co); ac=s.Poly(s.expand(a.subs(N,N+14)),N).all_coeffs();bc=s.Poly(s.expand(b.subs(N,N+14)),N).all_coeffs();assert (all(v>=0 for v in ac)or all(v<=0 for v in ac))and ac[-1]!=0 and all(v>0 for v in bc);print(h,sm,k,co,flush=True);records.append({'h':h,'s':sm,'order':k,'coefficient':str(co)})
open(Path(__file__).with_name('boundary_quadratic_certificate_v1.json'),'w').write(json.dumps(records,indent=2))
