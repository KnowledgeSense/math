"""Exact-integer diagnostics for caterpillar log-concavity.
Author: Knowledge Sense Contact: math@knowledgesense.jp.
"""
from itertools import product
from math import comb
from pathlib import Path
import json

C=((1,1,1),(1,0,1),(1,1,0))
B=((6,0,0),(0,0,-1),(0,-1,0))
ID=((1,0,0),(0,1,0),(0,0,1))
def mm(a,b): return tuple(tuple(sum(a[i][k]*b[k][j] for k in range(3)) for j in range(3)) for i in range(3))
def power(n):
    a=ID
    for _ in range(n): a=mm(a,C)
    return a
def convolution(a,b):
    c=[0]*(len(a)+len(b)-1)
    for i,x in enumerate(a):
        for j,y in enumerate(b): c[i+j]+=x*y
    return c
def z_coeff(word):
    state=[[1],[0],[0]]
    # The fictitious initial vacancy has compatibility 1 with every first state.
    for j in word:
        w=([0,0],[1,0],[0,1]) if j==0 else ([j*comb(j-1,k) for k in range(j)],[0]*(j-1)+[1],[1]+[0]*(j-1))
        new=[]
        for b in range(3):
            allowed=[state[a] for a in range(3) if C[a][b]]
            sums=[sum(p[k] for p in allowed) for k in range(len(state[0]))]
            new.append(convolution(sums,w[b]))
        state=new
    return [sum(p[k] for p in state) for k in range(len(state[0]))]

def kernel_checks():
    count=0; mins=[10**100]*5
    powers={q:power(q) for q in range(1,6)}
    for b in range(1,6):
        for qs in product(range(1,6),repeat=b+1):
            K=powers[qs[0]]
            for q in qs[1:]: K=mm(mm(K,B),powers[q])
            d,x,y,a,bb=K[0][0],K[0][1],K[1][0],K[1][1],K[1][2]
            w=a+bb;g=a-bb;Q=8*d-4*x-4*y+w
            assert K==((d,x,x),(y,a,bb),(y,bb,a))
            assert abs(g)==1 and d>=4 and x>=5 and y>=5 and w>=11 and Q>=3,(qs,K)
            assert 2*x<=3*d and 2*y<=3*d and w<=3*x and w<=3*y
            for eps in (-1,1):
                k=bb+g*eps
                assert k>=4 and k<=2*min(x,y) and 4*d-2*x-2*y+k>=0 and 2*d>y
            mins=[min(old,new) for old,new in zip(mins,[d,x,y,w,Q])];count+=1
    return {'count':count,'range':'1 <= number of B <= 5; every intervening C exponent in 1..5','observed_min_d_x_y_w_Q':mins,'failures':0}

def charge_positions(word):
    groups=[];M=0
    for i,j in enumerate(word):
        if j!=1:
            a=1 if j==0 else j-1
            groups.append((i,j,M,a));M+=a
    return groups,M
def bridge(i,j,removed):
    K=ID
    for k in range(i+1,j+1):
        K=mm(K,C)
        if k<j and k in removed: K=mm(K,B)
    return K
def lvec(i,removed):
    K=ID
    for k in range(i): K=mm(mm(K,B if k in removed else ID),C)
    return tuple(sum(K[k][a] for k in range(3)) for a in range(3))
def rvec(i,n,removed):
    K=ID
    for k in range(i+1,n): K=mm(mm(K,C),B if k in removed else ID)
    return tuple(sum(K[a]) for a in range(3))
def prepare(word,removed):
    groups,M=charge_positions(word)
    active=[g for g in groups if g[0] not in removed]
    if not active:
        K=ID
        for i in range(len(word)):
            K=mm(K,B if i in removed else ID)
            if i+1<len(word): K=mm(K,C)
        return active,(),(),(),sum(sum(row) for row in K) if word else 1
    return active,lvec(active[0][0],removed),rvec(active[-1][0],len(word),removed),[bridge(a[0],b[0],removed) for a,b in zip(active,active[1:])],None
def multiplicity(prep,colors,taus):
    groups,left,right,kernels,scalar=prep
    if scalar is not None: return scalar
    state=None;oldopts=None
    for pos,(i,j,start,a) in enumerate(groups):
        cs=colors[i]
        if j==0: opts=[(cs[0]+1,cs[0]+1,1)]
        else:
            eta=taus[i] if j==3 else int(len(set(cs))==1)
            opts=[(0,0,j),(2-cs[0],2-cs[-1],eta)]
        if pos==0: state=[left[l]*mult for l,r,mult in opts]
        else:
            K=kernels[pos-1]
            state=[mult*sum(state[h]*K[oldopts[h][1]][l] for h in range(len(oldopts))) for l,r,mult in opts]
        oldopts=opts
    return sum(value*right[opts[h][1]] for h,value in enumerate(state))
def partial_numerator(word,taus,s,t,removed):
    prep=prepare(word,removed);active=prep[0]
    M=sum(g[3] for g in active)
    total=0
    for bits in product((0,1),repeat=M):
        colors={};p=0;weight=1
        for i,j,start,a in active:
            cs=bits[p:p+a];p+=a;colors[i]=cs
            weight*=s**cs.count(0)*t**cs.count(1)
            if j==3: weight*=1+taus[i]*int(cs[0]==cs[1])
        if weight: total+=weight*multiplicity(prep,colors,taus)
    return total*(s*t)**len(removed)
def contraction_checks():
    words=[(3,),(3,3),(3,1,3),(0,3,0),(0,3,3,0),(3,0,3),(2,3,4),(1,3,1,3,1),
           (0,3,3,3,3,3,0),(0,3,1,3,3,1,0),(4,3,3,2),(3,3,3,3),(3,0,3,0,3),
           (2,3,1,0,3,4),(0,3,2,3,0)]
    cases=0;totals=[]
    for word in words:
        sites=[i for i,j in enumerate(word) if j==3]
        partsum=0
        for signs in product((-1,1),repeat=len(sites)):
            taus=dict(zip(sites,signs));removed={i for i,sign in taus.items() if sign==-1}
            original=partial_numerator(word,taus,2,3,set())
            contracted=partial_numerator(word,taus,2,3,removed)
            assert original==contracted,(word,taus,original,contracted)
            assert contracted>=0,(word,taus,contracted)
            partsum+=contracted;cases+=1
        coeff=z_coeff(word);value=sum(c*2**(len(coeff)-1-k)*3**k for k,c in enumerate(coeff))
        assert partsum==2**len(sites)*value,(word,partsum,value)
        totals.append({'word':word,'Z_at_s2_t3':value,'all_subset_contractions_match':True})
    return {'cases':cases,'evaluations':{'s':2,'t':3},'range':'all subsets of j=3 sites in 15 selected words; all original and all surviving charge colorings summed exactly','failures':0,'words':totals}

def main():
    counts=0;max_degree=0
    for n in range(7):
        for word in product(range(6),repeat=n):
            coeff=z_coeff(word);M=len(coeff)-1
            assert coeff==coeff[::-1],word
            assert all(coeff[b]>= (coeff[b-1] if b else 0) for b in range(M//2+1)),(word,coeff)
            counts+=1;max_degree=max(max_degree,M)
    print('normalized Schur checks',counts,flush=True)
    kernels=kernel_checks();print('kernel checks',kernels['count'],flush=True)
    contraction=contraction_checks();print('contraction checks',contraction['cases'],flush=True)
    f=[1,2]
    for n in range(2,6): f.append(3*f[-1]-3*f[-2])
    assert f[-1]==-9
    result={'arithmetic':'exact Python integers; no floating point','normalized_model':{'words':counts,'range':'length 0..6, each j in 0..5; all coefficients and all Schur coefficients','max_degree':max_degree,'failures':0},'contracted_kernels':kernels,'partial_sign_contraction':contraction,'uncontracted_sign_example':{'word':[0,3,3,3,3,3,0],'internal_signs':-1,'junction_signs':1,'fixed_sign_evaluation':-9,'recurrence_values':f},'role':'bounded diagnostics accompanying the analytic proof; finite ranges do not certify arbitrary lengths'}
    Path(__file__).with_name('results.json').write_text(json.dumps(result,ensure_ascii=False,indent=2),encoding='utf-8')
    print(json.dumps({k:v for k,v in result.items() if k!='partial_sign_contraction'},ensure_ascii=False,indent=2))
if __name__=='__main__':main()
