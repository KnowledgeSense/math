from pathlib import Path
from boundary_symbolic_core_v1 import *
recs=[]
for h in list(map(int,sys.argv[1:]))or[3,5,7,9]:
 cols,cc,val,ker=orig(h)
 for sm in range(6):
  terms=[[get_terms(h,ker[ii],cols,rr)for ii in[0,1]]for rr in range(3)]
  ccfs=[[[ ]for ii in range(2)]for rr in range(3)];found=False
  for k in range(9):
   for rr in range(3):
    for ii in range(2):ccfs[rr][ii].append(coefficient_terms(terms[rr][ii],sm,k))
   for rr,ss in [(0,1),(0,2),(1,2)]:
    co=s.factor(sum(ccfs[rr][0][i]*ccfs[ss][1][k-i]-ccfs[rr][1][i]*ccfs[ss][0][k-i]for i in range(k+1)))
    if co!=0:
     aa,bb=s.fraction(co); ac=s.Poly(s.expand(aa.subs(N,N+14)),N).all_coeffs();bc=s.Poly(s.expand(bb.subs(N,N+14)),N).all_coeffs();assert (all(v>=0 for v in ac)or all(v<=0 for v in ac))and ac[-1]!=0 and all(v>0 for v in bc);print(h,sm,'rows',rr,ss,'order',k,'coefficient',co,flush=True);recs.append({'h':h,'s':sm,'rows':[rr,ss],'order':k,'coefficient':str(co)});found=True;break
   if found:break
  assert found,(h,sm)
open(Path(__file__).with_name('boundary_two_moment_certificate_v1.json'),'w').write(json.dumps(recs,indent=2))
