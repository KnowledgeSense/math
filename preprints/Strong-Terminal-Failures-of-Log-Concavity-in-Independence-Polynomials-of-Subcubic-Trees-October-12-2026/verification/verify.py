"""Terminal log-convex runs in subcubic trees. Author: Knowledge Sense.

Independent sets are counted through their complementary vertex covers.
All assertions use integers or rational numbers, not floating point ratios.
Run: python -X utf8 verify.py
"""
from array import array
from collections import Counter
from datetime import datetime, timezone
from fractions import Fraction
from functools import lru_cache
from hashlib import sha256
from itertools import product
from math import comb
from pathlib import Path
import json, sys, time
sys.set_int_max_str_digits(0)

def convolution(a,b,limit):
    result=[0]*min(limit+1,len(a)+len(b)-1)
    for i,x in enumerate(a):
        for j in range(min(len(b),len(result)-i)):
            result[i+j]+=x*b[j]
    return result

def minimum_union(a,b,limit):
    # A state is (minimum vertex-cover size, coefficients above that size).
    minimum=min(a[0],b[0]); out=[0]*(limit+1)
    for degree,coefs in (a,b):
        shift=degree-minimum
        for j,c in enumerate(coefs):
            if shift+j<=limit: out[shift+j]+=c
    return minimum,out

def cover_product(a,b,limit):
    return a[0]+b[0],convolution(a[1],b[1],limit)

class Construction:
    def __init__(self): self.neighbors=[]
    def vertex(self):
        self.neighbors.append([]); return len(self.neighbors)-1
    def edge(self,a,b):
        self.neighbors[a].append(b);self.neighbors[b].append(a)
    def join(self,*children):
        v=self.vertex()
        for child in children:self.edge(v,child)
        return v
    def zero_gap(self,s,t):
        if s==1 and t==0:
            return self.join(self.vertex())
        if s==1:
            children=(self.zero_gap(1,t-1),self.zero_gap(1,t-1))
        else:
            children=(self.zero_gap(s//2,t),self.zero_gap(s-s//2,t))
        return self.join(self.join(*children))
    def positive_gap(self,s,t):
        # Build the zero-gap root last, and delete precisely that final vertex.
        v=self.zero_gap(s,t);child=self.neighbors[v][0]
        assert v==len(self.neighbors)-1
        self.neighbors[child].remove(v);self.neighbors.pop()
        return child
    def interface(self,s,n,t):
        left=self.positive_gap(s,t)
        right=self.join(self.positive_gap(n,t),self.positive_gap(n,t))
        return self.join(self.join(left,right))
    def complete(self,q,t):
        b=2*q*q;ends=[]
        for i in range(1,q+1):
            spine=[self.vertex() for _ in range(2*q-1)]
            for a,c in zip(spine,spine[1:]):self.edge(a,c)
            for k in range(1,q+1):
                multiplicity=1 if k in (1,q) else 2
                s=b*multiplicity+(i*i if k==1 else 0)
                self.edge(spine[2*k-2],self.interface(s,4*q*q+i,t))
                if k<q:self.edge(spine[2*k-1],self.positive_gap(2*b,t))
            ends.append((spine[0],spine[-1]))
        for i in range(q-1):
            bridge=self.join(self.vertex())
            self.edge(bridge,ends[i][1]);self.edge(bridge,ends[i+1][0])
        return 0
    def covers(self,root,limit):
        n=len(self.neighbors);parents=array('i',[-2])*n
        parents[root]=-1;order=array('i',[root])
        for v in order:
            for child in self.neighbors[v]:
                if child==parents[v]:continue
                assert parents[child]==-2, 'cycle'
                parents[child]=v;order.append(child)
        assert len(order)==n, 'disconnected'
        states=[None]*n
        for v in reversed(order):
            included=(1,[1]);excluded=(0,[1])
            for child in self.neighbors[v]:
                if parents[child]!=v:continue
                inc,exc=states[child]
                included=cover_product(included,minimum_union(inc,exc,limit),limit)
                excluded=cover_product(excluded,inc,limit)
                states[child]=None
            states[v]=(included,excluded)
        return states[root]

@lru_cache(None)
def entropy(s,t):
    if s==1 and t==0:return 1,1
    args=((1,t-1),(1,t-1)) if s==1 else ((s//2,t),(s-s//2,t))
    pairs=[entropy(*arg) for arg in args]
    d=(pairs[0][0]+1)*(pairs[1][0]+1)
    return d,d+sum(p[1] for p in pairs)

def block_checks():
    results=[]
    for t in range(3):
        a=entropy(1,t)[0]
        for s in range(1,7):
            graph=Construction();root=graph.positive_gap(s,t)
            n=len(graph.neighbors); inc,exc=graph.covers(root,n)
            mincover,ac=minimum_union(inc,exc,n)
            # Root absent in the independent set means root included in cover.
            d,w=entropy(s,t);bc=inc[1]
            assert n-mincover==2*(2**t)*s-1
            assert inc[0]==mincover+1 and ac[0]==1 and bc[0]==d
            assert a**s<=d
            assert d*a**(2*(s-1))<=a**s*(a+1)**(2*(s-1))
            assert w<=n*d
            assert all(c<=w**j for j,c in enumerate(ac))
            assert all(c<=d*w**j for j,c in enumerate(bc))
            brute=False
            if n<=13:
                histogram=Counter()
                edges=[(u,v) for u,adj in enumerate(graph.neighbors) for v in adj if u<v]
                for mask in range(1<<n):
                    if all(not((mask>>u)&1 and (mask>>v)&1) for u,v in edges):
                        histogram[mask.bit_count()]+=1
                alpha=max(histogram)
                assert [histogram[alpha-j] for j in range(alpha+1)]==ac[:alpha+1]
                brute=True
            results.append(dict(t=t,s=s,vertices=n,d=d,w=w,brute_force=brute))
    return results

def positive_model_checks():
    results=[]
    for q in range(2,9):
        a=256;b=2*q*q;M=4*q*q;K0=a**(2*b*(q-1))
        epsilon=Fraction(2*q,a**(4*q*q))+Fraction(2*3**q,a**(q*q))
        F=[1]
        for i in range(1,q+1):
            delta=a**(2*(M+i));linear=[1,delta]
            missing,present=[1],[0]
            weights=[]
            for index in range(2*q-1):
                if index%2:wa,wp=[1],[a**(2*b)]
                else:
                    k=index//2+1;s=b*(1 if k in (1,q) else 2)+(i*i if k==1 else 0)
                    wa=linear;wp=[1+a**s,delta]
                weights.append((wa,wp))
                missing,present=convolution([x+y for x,y in zip(missing+[0]*(q+1-len(missing)),present+[0]*(q+1-len(present)))],wa,q),convolution(missing,wp,q)
            J=[x+y for x,y in zip(missing+[0]*(q+1-len(missing)),present+[0]*(q+1-len(present)))]
            Fi=[comb(q,j)*delta**j for j in range(q+1)];Fi[0]+=a**(i*i)
            assert all(K0*f<=c and c*epsilon.denominator<=K0*f*(epsilon.denominator+epsilon.numerator) for c,f in zip(J,Fi))
            # Independently enumerate physical core sets for the smallest q.
            if q<=4:
                enum=[0]*(q+1)
                for bits in product((0,1),repeat=2*q-1):
                    if any(x and y for x,y in zip(bits,bits[1:])):continue
                    term=[1]
                    for bit,(wa,wp) in zip(bits,weights):term=convolution(term,wp if bit else wa,q)
                    for j,c in enumerate(term):enum[j]+=c
                assert enum==J
            F=convolution(F,Fi,q)
        assert q*epsilon<Fraction(1,4)
        D=a**sum(i*i for i in range(1,q+1));A=a**(2*M)
        for j,c in enumerate(F):
            lower=comb(q,j)*D*A**j*a**(j*j)
            assert lower<=c<=3*lower
        results.append(dict(q=q,a=a,phase_components=q,gaussian_coefficients=q+1))
    return results

def graph_check(r,H,t_override=None):
    q=r+1;Q=2**(q+10)*q**4*H;a=1;chosen=0
    while a<Q:a=(a+1)**2;chosen+=1
    t=chosen if t_override is None else t_override
    a=entropy(1,t)[0];graph=Construction();root=graph.complete(q,t)
    n=len(graph.neighbors);edges=sum(map(len,graph.neighbors))//2
    assert edges==n-1 and max(map(len,graph.neighbors))==3
    tau,c=minimum_union(*graph.covers(root,q),q);alpha=n-tau
    P=16*q**4-7*q**3+q*q+sum(i*i for i in range(1,q+1))
    assert n==4*(2**t)*P-7*q*q+4*q-2
    assert alpha==2*(2**t)*P-3*q*q+2*q-1
    strict=[c[j-1]*c[j+1]>H*c[j]*c[j] for j in range(1,q)]
    valid=t>=chosen
    bounds=None
    if valid:
        K=a**(4*q**3*(q-1));D=a**sum(i*i for i in range(1,q+1));A=a**(8*q*q)
        lower=[K*comb(q,j)*D*A**j*a**(j*j) for j in range(q+1)]
        assert all(l<=v<=2**(q+3)*l for v,l in zip(c,lower))
        assert all(strict)
        assert n<=1200*q**4*(q+H.bit_length())
        bounds=True
    example_checks=None
    if valid and r==1 and H==1 and t==chosen:
        numerator=c[0]*c[2];denominator=c[1]**2
        assert 2**35*denominator<numerator<2**36*denominator
        # Compare the exact ratio with the model a^2/4 without rounding.
        assert 100000*abs(4*numerator-a*a*denominator)<a*a*denominator
        example_checks=dict(power_bracket=True,relative_model_error_less_than_1e_5=True)
    return dict(r=r,H=H,t=t,chosen_t=chosen,theorem_parameters=valid,vertices=n,edges=edges,max_degree=3,alpha=alpha,strict_indices=strict,coefficient_bounds=bounds,exact_example_checks=example_checks,coefficient_bits=[v.bit_length() for v in c],coefficient_digest=sha256(','.join(map(str,c)).encode()).hexdigest())

def main():
    start=time.perf_counter()
    evidence=dict(method='Explicit adjacency lists; generic minimum-vertex-cover DP; exact integer and Fraction arithmetic')
    evidence['blocks']=block_checks()
    evidence['positive_models']=positive_model_checks()
    evidence['graphs']=[]
    for args in [(1,1,0),(2,1,0),(2,1,1),(1,1,None),(2,1,None),(3,1,None),(4,1,None),(1,10**6,None),(2,10**6,None)]:
        row=graph_check(*args);evidence['graphs'].append(row)
        print(json.dumps(row,ensure_ascii=False),flush=True)
    evidence['elapsed_seconds']=time.perf_counter()-start
    evidence['all_assertions_satisfied']=True
    evidence['scope']='Finite checks of the explicit construction and coefficient inequalities.'
    output=Path(__file__).resolve().with_name('verification-results.json')
    output.write_text(json.dumps(evidence,ensure_ascii=False,indent=2),encoding='utf-8')
    print(json.dumps(dict(all_assertions_satisfied=True,elapsed_seconds=evidence['elapsed_seconds'])))

if __name__=='__main__':main()
