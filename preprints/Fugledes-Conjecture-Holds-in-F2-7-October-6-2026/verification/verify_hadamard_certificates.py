"""Independent positive-certificate checker: dense F2 Gaussian elimination.
No imports from search or generation programs; no clique solver required.
"""
from pathlib import Path
if not __debug__: raise RuntimeError("Run without Python -O: assertions verify certificates")
import json,math
P=Path(__file__).resolve().parent

def rank(rows):
    a=[row[:] for row in rows]
    if not a:return 0
    m,n=len(a),len(a[0]);r=0
    for c in range(n):
        piv=next((i for i in range(r,m) if a[i][c]),None)
        if piv is None:continue
        a[r],a[piv]=a[piv],a[r]
        for i in range(m):
            if i!=r and a[i][c]:a[i]=[x^y for x,y in zip(a[i],a[r])]
        r+=1
        if r==m:break
    return r

def check(H,d):
    n=len(H);r=d['r'];E=d['E'];T=d['T']
    assert all(len(row)==n and all(x in [-1,1] for x in row) for row in H)
    assert all(sum(H[i][k]*H[j][k] for k in range(n))==(n if i==j else 0) for i in range(n) for j in range(n))
    L=[[(1-H[i][j]*H[i][0]*H[0][j]*H[0][0])//2 for j in range(n)] for i in range(n)]
    assert rank(L)==r
    C=[[(e>>k)&1 for e in E] for k in range(r)]
    assert rank(C)==r and rank(L+C)==r # C and L have identical row spaces
    assert len(E)==len(set(E))==n and all(0<=e<1<<r for e in E)
    assert len(T)==len(set(T))==(1<<r)//n and all(0<=t<1<<r for t in T)
    assert len({e^t for e in E for t in T})==1<<r

def main():
    ds=json.loads((P/'spectral16_certificates.json').read_text());assert len(ds)==5
    for d in ds:
        H=[[1 if c=='+' else -1 for c in s.strip()] for s in (P/f"had.16.{d['index']}.txt").read_text().splitlines() if len(s.strip())==16 and set(s.strip())<=set('+-')]
        check(H,d)
    source={}
    for line in (P/'had32_rank_le7.txt').read_text().splitlines():
        z=line.split();source[int(z[0])]=[int(x,16) for x in z[2:]]
    assert len(source)==16
    ds=json.loads((P/'spectral32_certificates.json').read_text());assert len(ds)==32
    assert {(d['class_index'],d['transpose']) for d in ds}=={(i,b) for i in source for b in [False,True]}
    for d in ds:
        rows=source[d['class_index']]
        H=[[1 if row>>j&1 else -1 for j in range(32)] for row in rows]
        if d['transpose']:H=[list(x) for x in zip(*H)]
        check(H,d)
    exponents=[k for k in range(8) for _ in range(math.comb(7,k))]
    excluded=[]
    for m in range(4,64,4):
        if m&(m-1):
            valuation=(m//2)*((m&-m).bit_length()-1)
            assert valuation<sum(exponents[:m]);excluded.append(m)
    assert excluded==[12,20,24,28,36,40,44,48,52,56,60]
    print('VERIFIED: all 5 order16 and 32 oriented order32 certificates; all non-power cardinality exclusions')
if __name__=='__main__':main()
