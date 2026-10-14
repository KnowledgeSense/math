"""Independent full-product recurrence for the credited prior example."""
from hashlib import sha256
import json
def product(groups):
    a=[1]
    for weight,count in groups:
        for _ in range(count):
            a.append(0)
            for k in range(len(a)-1,0,-1):a[k]+=weight*a[k-1]
    return a
A=product([(1,1449),(2,588)])
B=product([(1,1913),(12,39),(13,85)])
C=product([(1,2037)])
p=[a+b-c for a,b,c in zip(A,B,C)]
assert len(p)==2038 and all(v>0 for v in p)
assert sha256(json.dumps(p,separators=(',',':')).encode()).hexdigest()=='8d904b43677abb33e2b8c45b0964b74051adc9bfe474ab911216fa594a65e44a'
assert p[1094]>p[1095]<p[1096]
print(json.dumps({'status':'PASS','method':'Full exact polynomial products by repeated linear-factor recurrence','prior_base_order':2037,'prior_corona_order':4074,'full_degree':2037,'all_coefficients_positive':True,'valley':[1094,1095,1096],'digits':[len(str(p[k])) for k in (1094,1095,1096)],'coefficient_list_sha256':sha256(json.dumps(p,separators=(',',':')).encode()).hexdigest(),'source':'https://www.linkedin.com/posts/tesuji_levit-mandrescu-counterexample-activity-7487528446403768320-b1pc','credit':'Prior public example by Lucas B.; not new here'},indent=2))
