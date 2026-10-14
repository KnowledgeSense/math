"""Exact determinant and finite-state construction checks.
Finite samples supplement the mathematical proof.
"""
from fractions import Fraction as F
from functools import lru_cache
from pathlib import Path
import json, random, time, hashlib

def det_int(mat):
    a=[list(row) for row in mat]
    n=len(a); sign=1; old=1
    for k in range(n-1):
        if a[k][k]==0:
            j=next((j for j in range(k+1,n) if a[j][k]),None)
            if j is None:return 0
            a[k],a[j]=a[j],a[k]; sign=-sign
        pivot=a[k][k]
        for i in range(k+1,n):
            for j in range(k+1,n):
                num=a[i][j]*pivot-a[i][k]*a[k][j]
                assert num%old==0
                a[i][j]=num//old
        for i in range(k+1,n):a[i][k]=0
        old=pivot
    return sign*a[-1][-1]

def matrices(N,r):
    q=1<<r; L=(N-1).bit_length()-1; top=1<<(L+1)
    values=[q*(j%top).bit_count()+j//top for j in range(2*N-1)]
    H=F(det_int([[values[i+j] for j in range(N)] for i in range(N)]),q**N)
    G=F(det_int([[values[i+j+1]-values[i+j] for j in range(N-1)]+[1] for i in range(N)]),q**(N-1))
    e=2*N-(1<<(L+1))-1
    return q**e*G,H/G,H

@lru_cache(None)
def exact(N,r):
    q=1<<r; u=1-2*q
    if N==2:return F(2*q-1),F(q,u)
    if N==3:return F(2*q-1),F(1-3*q,u)
    if N==4:return F(u*u*(1-4*q)),F(q*(3-8*q),u*(1-4*q))
    L=(N-1).bit_length()-1; s=-1 if N%2 else 1
    if N<=3*(1<<(L-1)):
        Q,R=exact((1<<(L+1))-N+1,0)
        return s*u**(2*N-(1<<(L+1))-1)*Q,-R+F(s*q,u)
    Q,R=exact(N-(1<<L),r+1)
    return u**(1<<L)*Q,R+F(s*q,u)

def terminal(N,q,P):
    u=(1-2*q)%P
    if N==2:return (2*q-1)%P,q*pow(u,-1,P)%P
    if N==3:return (2*q-1)%P,(1-3*q)*pow(u,-1,P)%P
    return u*u*(1-4*q)%P,q*(3-8*q)*pow(u*(1-4*q)%P,-1,P)%P

def by_integer(N,K):
    if N==1:return 0
    P=1<<K; q=1; a=1;b=0;g=1
    while N>=5:
        L=(N-1).bit_length()-1;u=(1-2*q)%P;s=(-1 if N%2 else 1)
        c=s*q*pow(u,-1,P)%P
        lower=N<=3*(1<<(L-1))
        exponent=(2*N-(1<<(L+1))-1) if lower else (1<<L)
        f=pow(u,exponent%P,P)*(s if lower else 1)%P
        b=(b+a*c)%P;a=a*(-1 if lower else 1)%P;g=g*f%P
        q=1 if lower else 2*q%P
        N=(1<<(L+1))-N+1 if lower else N-(1<<L)
    Q,R=terminal(N,q,P)
    return g*Q*(a*R+b)%P

def annotations(word,K):
    P=1<<K;C=max(K+1,3);c=0;v=0;out=[]
    for bit in word[::-1]:
        v=(int(bit)*(0 if c==C else pow(2,c,P))+v)%P
        c=min(c+1,C);out.append((c,v))
    return out[::-1]

def verify_annotation(word,ann,K):
    P=1<<K;C=max(K+1,3)
    for i,(c,v) in enumerate(ann):
        if not (1<=c<=C and 0<=v<P):return False
        cn,vn=ann[i+1] if i+1<len(ann) else (0,0)
        T=0 if cn==C else pow(2,cn,P)
        if c!=min(cn+1,C) or v!=(int(word[i])*T+vn)%P:return False
    return True

def by_annotation(word,K,ann=None):
    if word=='0':return 0
    P=1<<K;C=max(K+1,3)
    ann=annotations(word,K) if ann is None else ann
    assert verify_annotation(word,ann,K)
    q=1;a=1;b=0;g=1;o=0
    for i,(cap,v) in enumerate(ann):
        assert int(word[i])^o==1
        if cap<=2:
            m=0
            for bit in word[i:]:m=2*m+(int(bit)^o)
            Q,R=terminal(m+1,q,P)
            return g*Q*(a*R+b)%P
        lower=(int(word[i+1])^o)==0
        T=0 if cap==C else pow(2,cap,P)
        TL=0 if cap==C else pow(2,cap-1,P)
        m=v if o==0 else (T-1-v)%P
        s=-1 if (m+1)%2 else 1
        u=(1-2*q)%P;c=s*q*pow(u,-1,P)%P
        exp=(2*m-T+1)%P if lower else TL
        f=pow(u,exp,P)*(s if lower else 1)%P
        b=(b+a*c)%P;a=a*(-1 if lower else 1)%P;g=g*f%P
        q=1 if lower else 2*q%P;o=o^int(lower)
    raise AssertionError('missing terminal')

def main():
    start=time.perf_counter(); count=0; direct_values=[]
    for N in range(2,41):
        for r in range(9):
            Q,R,H=matrices(N,r)
            assert (Q,R)==exact(N,r),(N,r,Q,R,exact(N,r))
            assert Q.denominator==1 and Q.numerator%2 and R.denominator%2
            count+=1
            if r==0:direct_values.append(int(H))
    for K in range(1,13):
        for N,H in zip(range(2,41),direct_values):
            assert by_integer(N,K)==H%(1<<K)
    samples=0
    for K in range(1,11):
        for n in range(5001):
            assert by_annotation(bin(n)[2:],K)==by_integer(n+1,K),(n,K)
            samples+=1
    rng=random.Random(570012)
    lengths=[3,4,8,16,64,256,1024,2048]
    long_samples=0; malformed=0
    for K in (1,2,3,5,10,16):
        for length in lengths:
            words=['1'+'0'*(length-1),'1'*length,'10'+'1'*(length-2),'11'+'0'*(length-2),
                   ''.join('1' if i%2==0 else '0' for i in range(length))]
            words += ['1'+''.join(str(rng.randrange(2)) for _ in range(length-1)) for _ in range(10)]
            for word in words:
                assert by_annotation(word,K)==by_integer(int(word,2)+1,K)
                long_samples+=1
                ann=annotations(word,K); j=rng.randrange(length)
                bad=ann.copy();bad[j]=(bad[j][0],(bad[j][1]+1)%(1<<K))
                assert not verify_annotation(word,bad,K);malformed+=1
                bad=ann.copy();bad[-1]=(max(K+1,3),bad[-1][1])
                assert not verify_annotation(word,bad,K);malformed+=1
    result={'exact_weighted_pairs':count,'N_range':[2,40],'r_range':[0,8],
            'direct_modular_checks':39*12,'K_direct_range':[1,12],
            'annotation_index_checks':samples,'n_range':[0,5000],'K_annotation_range':[1,10],
            'long_input_checks':long_samples,'long_input_K':[1,2,3,5,10,16],
            'input_bit_lengths':lengths,'malformed_annotation_rejections':malformed,
            'D_1_to_16':[0]+direct_values[:15],'mismatches':0,
            'seconds':round(time.perf_counter()-start,3),
            'method':'integer Bareiss from defining matrices; rational recursion; modular integer-index and annotated-word calculations',
            'script_sha256':hashlib.sha256(Path(__file__).read_bytes()).hexdigest(),
            'limits':'Tests are finite samples. No minimal automaton or DFA state enumeration is claimed.'}
    path=Path(__file__).resolve().parent/'verification_results.json'
    path.write_text(json.dumps(result,ensure_ascii=False,indent=2),encoding='utf-8')
    print(json.dumps(result,ensure_ascii=False,indent=2))
if __name__=='__main__':main()
