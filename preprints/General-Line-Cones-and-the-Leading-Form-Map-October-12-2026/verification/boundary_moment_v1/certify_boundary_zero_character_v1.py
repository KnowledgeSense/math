from pathlib import Path
from boundary_small_global_core_v1 import *
recs=[]
for sm in list(map(int,sys.argv[1:]))or range(6):
 cols,cc,val,ker=h0kernels();ker[2]=[add(ker[2][j],neg([0,0]+ker[1][j][:-2]))for j in range(len(cols))];rowweights=[0,1,1]if sm<2 else[0,0,1];colweights=[1,2,-1];mat=[]
 for rr in range(3):
  row=[]
  for ii,V in enumerate(ker):
   kk=rowweights[rr]-colweights[ii]
   for lower in range(-2,kk):assert moment_unscaled(0,V,cols,[0,3,4][rr],sm,lower)==0,(sm,rr,ii,lower)
   co=moment_unscaled(0,V,cols,[0,3,4][rr],sm,kk);row.append(co);print('entry',sm,rr,ii,kk,co,flush=True)
  mat.append(row)
 det=s.factor(s.det(s.Matrix(mat)));print('DET',sm,det,flush=True);a,b=s.fraction(det);aa=s.Poly(s.expand(a.subs(N,N+14)),N).all_coeffs();bb=s.Poly(s.expand(b.subs(N,N+14)),N).all_coeffs();assert(all(v>0 for v in aa)or all(v<0 for v in aa))and all(v>0 for v in bb),(sm,'sign');recs.append({'s':sm,'row_weights':rowweights,'column_weights':colweights,'matrix':[[str(v)for v in row]for row in mat],'determinant':str(det),'shift14_strict_sign':True})
open(Path(__file__).with_name('boundary_zero_character_certificate_v1.json'),'w').write(json.dumps(recs,indent=2))
