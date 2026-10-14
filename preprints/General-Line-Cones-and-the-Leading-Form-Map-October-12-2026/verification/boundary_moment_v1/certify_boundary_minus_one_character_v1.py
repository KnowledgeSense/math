from pathlib import Path
from boundary_small_global_core_v1 import *
records=[]
cols,V=h1kernel();basecols,cc,val,ker=orig(1)
for sm in range(6):
 terms=get_terms(1,ker[0],basecols,0)
 for k in range(6):
  first=coefficient_terms(terms,sm,k)
  if first!=0:break
 assert k<=3
 first_order=k
 for k in range(-2,3):
  co=moment_unscaled(1,V,cols,1,sm,k,True)
  if co!=0:break
 assert k<=1
 for expr in[first,co]:
  aa,bb=s.fraction(expr);ac=s.Poly(s.expand(aa.subs(N,N+14)),N).all_coeffs();bc=s.Poly(s.expand(bb.subs(N,N+14)),N).all_coeffs();assert(all(v>=0 for v in ac)or all(v<=0 for v in ac))and ac[-1]!=0 and all(v>0 for v in bc)
 print(sm,first_order,first,k,co,flush=True)
 records.append({'s':sm,'first_normalized_moment_order':first_order,'first_normalized_moment_coefficient':str(first),'projected_remaining_order':k,'projected_remaining_coefficient':str(co),'nonvanishing_by_N_shift_14':True})
Path(__file__).with_name('boundary_minus_one_character_certificate_v1.json').write_text(json.dumps(records,indent=2)+'\n')
