"""Numerical density and moment checks for Apéry polynomials.

Author: Knowledge Sense.
The all-n result is established in the accompanying paper."""
import json
import math
from functools import lru_cache
from pathlib import Path

PI = math.pi

@lru_cache(None)
def gauss(n):
    pairs = []
    for i in range(1, (n + 1)//2 + 1):
        x = math.cos(PI*(i-0.25)/(n+0.5))
        for _ in range(12):
            p0, p1 = 1.0, x
            for k in range(2, n+1):
                p0, p1 = p1, ((2*k-1)*x*p1-(k-1)*p0)/k
            dp = n*(x*p1-p0)/(x*x-1)
            dx = p1/dp
            x -= dx
            if abs(dx) < 2e-15:
                break
        wt = 2/((1-x*x)*dp*dp)
        pairs.extend([(-x, wt), (x, wt)])
    return sorted(pairs)

def integral(fun, a, b, order, smooth=False):
    if b <= a:
        return 0.0
    if smooth:
        def transformed(theta):
            v = a+(b-a)*math.sin(theta)**2
            return fun(v)*(b-a)*math.sin(2*theta)
        return integral(transformed, 0.0, PI/2, order)
    mid, half = (a+b)/2, (b-a)/2
    return half*math.fsum(wt*fun(mid+half*x) for x, wt in gauss(order))

def complete_complement(kprime):
    a, b = 1.0, kprime
    if b == 0:
        return math.inf
    for _ in range(30):
        c, d = (a+b)/2, math.sqrt(a*b)
        a, b = c, d
        if abs(a-b) < 2e-15*a:
            break
    return PI/(2*a)

def spectral(c):
    return complete_complement(abs(c)/4)/(2*PI**2)

def kappa_q(q):
    if q < 4:
        return complete_complement(math.sqrt(max(0.0, (4-q)*(4+q)/16)))
    return 4/q*complete_complement(math.sqrt(max(0.0, (q-4)*(q+4)/(q*q))))

def components(w, b, order):
    tval = integral(lambda theta: spectral(w-b*math.cos(theta)),0,PI,order)/PI
    cutoff = (w-4)/b
    theta_max = PI if cutoff <= -1 else (0.0 if cutoff >= 1 else math.acos(cutoff))
    hval = integral(lambda theta: spectral(w-b*math.cos(theta)),0,theta_max,order)/PI
    # Use q=w-u directly to avoid cancellation at the logarithmic crossing q=4.
    # The sin^2 substitution removes the endpoint square-root weight.
    qend = w-b
    cuts = [0.0]+([4.0] if qend>4 else [])+[qend]
    jval = math.fsum(integral(lambda q:kappa_q(q)/math.sqrt((qend-q)*(w+b-q)),a,c,order,True) for a,c in zip(cuts,cuts[1:]))/PI**3
    return hval, tval, jval

def verify(alpha, order):
    b = 2*math.sqrt(alpha)
    B = 4+b
    qmax = (B+math.sqrt(B*B-4*alpha))/2
    qmin = math.sqrt(alpha)
    def q_at(w):
        return (w+math.sqrt(max(0.0,w*w-4*alpha)))/2
    high_cuts = sorted(set([qmin,qmax]+[q_at(w) for w in [4-b,4+b] if b < w < B]))
    low_cuts = sorted(set([0.0,14.0]+[math.acosh(w/b) for w in [4-b,4+b] if w>b]))
    moments = [0.0]*5
    for a,c in zip(high_cuts,high_cuts[1:]):
        mid, half = (a+c)/2,(c-a)/2
        for x, wt in gauss(order):
            q = mid+half*x
            h = components(q+alpha/q,b,order)[0]
            for n in range(5):
                moments[n] += half*wt*2*q**(2*n)*h
    for a,c in zip(low_cuts,low_cuts[1:]):
        mid, half = (a+c)/2,(c-a)/2
        for x, wt in gauss(order):
            z=mid+half*x
            q=qmin*math.exp(-z)
            h,t,j=components(b*math.cosh(z),b,order)
            val=2*t-h+2*j
            for n in range(5):
                moments[n] += half*wt*2*q**(2*n+1)*val
    exact=[sum(alpha**k*(math.factorial(2*n-k)/(math.factorial(k)*math.factorial(n-k)**2))**2 for k in range(n+1)) for n in range(5)]
    return {'alpha':alpha,'x':1/alpha,'order':order,'moments_D':moments,'exact_D':exact,'relative_errors':[(a-b)/b for a,b in zip(moments,exact)],'S':qmax*qmax}

if __name__=='__main__':
    output=[]
    for order in [192,384]:
        for alpha in [1.0,0.999,0.5,0.1,0.01]:
            row=verify(alpha,order)
            output.append(row)
            print(json.dumps(row),flush=True)
    Path(__file__).with_name('density_checks.json').write_text(json.dumps({'method':'double precision Gauss-Legendre; independent density quadrature, n=0..4; low q truncation at exp(-14); diagnostic only','results':output},indent=2,allow_nan=False),encoding='utf-8')
