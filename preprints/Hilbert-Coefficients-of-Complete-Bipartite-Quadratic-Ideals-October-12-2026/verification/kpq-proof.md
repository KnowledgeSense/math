# Parity classification for complete-bipartite quadratic ideals

Author: Knowledge Sense

## Theorem

Let 1 <= p <= q, n=p+q, and let k be any field. In the polynomial ring on x_1,...,x_p,y_1,...,y_q, let

    I_{p,q}=(all x_a^2, all y_b^2, all x_a y_b).

Define e_i by the eventual ordinary-power length expansion with alternating signs,

    length(S/I_{p,q}^s)=sum_{i=0}^n (-1)^i e_i binom(s+n-i-1,n-i).

Then:

1. e_i=2^(n-2i) binom(n-i,i)>0 for 0 <= i <= p.
2. For p+1 <= i <= n-1, the sign of e_i is exactly (-1)^(p+1).
3. e_n=0.

Consequently all Hilbert coefficients are nonnegative exactly when the smaller part p is odd. When p is even, there is one complete negative block e_{p+1},...,e_{n-1}, of length q-1. The assertions about an empty block have their usual vacuous meaning, so p=q=1 is included.

## 1. Exact length series for general part sizes

For a monomial, write A,B for the two total degrees and o_A,o_B for the two numbers of odd exponents. The generator-packing formula established directly in k2q-proof.md, Section 1 does not require p=2:

    nu=min(floor((A+B)/2), A+(B-o_B)/2, B+(A-o_A)/2).

Its proof exhausts the side of smaller total degree, minimizing the number of odd residual exponents on the other side. It applies word for word for all positive p,q.

At total degree >=2s, nonmembership in I^s is the disjoint union of the two strict deficiency inequalities. For deficiency on the p-variable side, set t=B, write the p exponents as 2 beta_a+epsilon_a, put k=sum epsilon_a and l=sum beta_a, and set r=s-t-l>=1. The degree condition is k>=t+2r. Thus its contribution is

    sum_{t>=0,r>=1,t+2r<=k<=p,t+r<=s}
      binom(t+q-1,q-1) binom(p,k) binom(s-t-r+p-1,p-1).

Define the polynomial

    P_{p;q}(z)=sum_{t>=0,r>=1,t+2r<=p}
      binom(t+q-1,q-1) [sum_{k=t+2r}^p binom(p,k)] z^(t+r-1).

It is zero for p=1, and has degree p-2 for p>=2. Let h_{p,q} be determined by

    sum_{s>=1} length(S/I_{p,q}^s)z^s = z h_{p,q}(z)/(1-z)^(n+1).

Then the full, exact length count is

    h_{p,q}(z)=h_{m^2,n}(z)
               +(1-z)^(q+1)P_{p;q}(z)
               +(1-z)^(p+1)P_{q;p}(z).                         (1)

As in k2q-proof.md, Section 3,

    e_i=[u^i]h_{p,q}(1+u),
    h_{m^2,n}(1+u)=A_n(u)=sum_i 2^(n-2i)binom(n-i,i)u^i.

This already proves the low-coefficient assertion and e_n=0: both correction terms start after degree p, and have degree at most n-1.

## 2. A coefficient-extraction identity

We derive a compact identity that permits a sign proof for all remaining indices. Set

    D(x)=1-2x-u x^2,
    A=x-y+xy,   B=y-x+xy.

Summing the finite polynomial above, first in the odd-coordinate count and then in p, gives for every fixed q>=1

    sum_{p>=0} P_{p;q}(1+u)x^p
      =x^2(1-x)^q/[(1-2x)(1-(2+u)x)^q D(x)].                  (2)

Here the p=0 term is defined as zero, solely for convenience. To check (2), before the binomial transform the generating series is

    w^2/[(1-w)(1-(1+u)w)^q(1-(1+u)w^2)],

and the transform is (1-x)^(-1) times its value at w=x/(1-x).

Let H(u,x,y)=sum_{p,q>=1}h_{p,q}(1+u)x^p y^q. The baseline in (1) sums to

    xy/(x-y) * {x(4+u+2ux)/D(x)-y(4+u+2uy)/D(y)}.

The first correction term sums to

    u^2 x^2 y(1-x)/[(1-2x)D(x)(1-(2+u)x+uy(1-x))],

and the second is obtained by interchanging x,y. Substitution and multiplication of denominators now give

    H=4xy/[(1-2x)(1-2y)]
      +u xy/(x-y) * {x/[(1-2x)(1-2x-uA)]
                     -y/[(1-2y)(1-2y-uB)]}.                  (3)

This is an identity of rational functions. The antisymmetric numerators are divisible by x-y; no expansion in an illegitimate unit x-y is assumed. For every i>=1, (3) implies

    E_i(x,y):=sum_{p,q>=1}e_i(I_{p,q})x^p y^q
      =xy/(x-y) * {x A^(i-1)/(1-2x)^(i+1)
                   -y B^(i-1)/(1-2y)^(i+1)}.                 (4)

For the remaining sign proof fix p<=q and p<i<=n-1, and put r=n-i-1>=0. For 1<=m<i define

    S_m(z)=sum_{j=0}^{m-1}(-1)^j binom(i-1,j)(1-z)^j,
    T_m(r)=[z^r] S_m(z)/(1-2z)^(i+1).

Coefficient extraction in (4) gives

    e_i=T_p(r)                      if p<i<=q;
    e_i=T_p(r)+T_q(r)               if p<=q<i.                 (5)

For completeness, multiply (4) by x-y and compare coefficients. With

    c_j=(-1)^j binom(i-1,j),
    t_j=[z^r](1-z)^j/(1-2z)^(i+1),

the resulting recurrence, summed from the boundary p=0, is

    e_i(p,q)=sum_{j=0}^{p-1}c_j t_j - sum_{j=q}^{i-1}c_j t_j,

where the second sum is empty for q>=i. When q<i, the complete sum over 0<=j<=i-1 equals [z^r]z^(i-1)/(1-2z)^(i+1)=0, because p<=q<i implies r<i-1. This proves (5).

## 3. Sign of every partial contribution

For 1<=m<i and every r>=0,

    (-1)^(m-1) T_m(r)>0.                                      (6)

Here is a coefficientwise proof. For integers N>=M+1 and M>=0, let

    b_M(N)=(-1)^M sum_{l=0}^M (-1/2)^l binom(N,l).

Then b_M(N)>=0. At N=M+1 its value is 2^(-N)(1+(-1)^M). For N>=M+2 the Pascal recurrence is

    b_M(N)=b_M(N-1)+(1/2)b_{M-1}(N-1),

with b_0(N)=1. These formulas prove the claim by induction. In particular the coefficient of v^a in S_m((1-v)/2), for 0<=a<=m-1, has sign (-1)^(m-1) or is zero: apart from the factor (-1)^a 2^(-a)binom(i-1,a), its remaining sum is the one above with N=i-1-a and M=m-1-a. The highest coefficient a=m-1 is nonzero.

Thus (-1)^(m-1) S_m(z) is a nonzero polynomial with nonnegative coefficients in the variable 1-2z. Dividing by (1-2z)^(i+1), all resulting denominators have positive exponent. Their coefficients at every degree r>=0 are positive. This proves (6).

If i<=q, equations (5) and (6) immediately give the required sign. If q<i and p,q have the same parity, the two contributions in (5) have the same required sign. Only opposite parity remains.

## 4. Dominance of the smaller part in the mixed-parity case

Write U_m(r)=(-1)^(m-1)T_m(r)>0 and C_m=binom(i-2,m-1). When 0<=r<i-1, the normalized quantities U_m(r)/C_m are nonincreasing in m for 1<=m<i.

Taylor's formula with integral remainder gives the polynomial identity

    S_m(z)-z^(i-1)
      =(-1)^(m-1)(i-1)C_m
         integral_0^(1-z) t^(m-1)(t+z)^(i-m-1) dt.             (7)

The integral here is an integral of a polynomial over rational coefficients; it is merely a concise algebraic identity. It places no restriction on the base field of the monomial ideal.

Since r<i-1, the z^(i-1) term does not contribute. Make the formal substitution z=w/(1+2w). For any power series f,

    [z^r]f(z)=[w^r] f(w/(1+2w))(1+2w)^(r-1).

Substituting t=(1+w)s/(1+2w) in (7) yields

    U_m(r)/C_m=(i-1)[w^r](1+2w)^(r+1)
       integral_0^1 (1+w)^m s^(m-1)
                    (s+(s+1)w)^(i-m-1) ds.                   (8)

Let F_m denote the polynomial integrand. For m<=i-2,

    F_m-F_{m+1}
      =w(1+w)^m s^(m-1)(s+(s+1)w)^(i-m-2).

This has nonnegative coefficients in s,w. Multiplication by (1+2w)^(r+1), integration and extraction preserve nonnegativity, proving the asserted monotonicity.

Now suppose p<q<i. We have r=n-i-1<i-1 and

    C_p=binom(i-2,p-1)>binom(i-2,q-1)=C_q.

Indeed the two lower indices satisfy p-1<q-1 and their sum n-2 exceeds i-2. Strict binomial unimodality and symmetry give the displayed inequality. Equation (8) and positivity give

    U_p(r)/C_p >= U_q(r)/C_q >0,

hence U_p(r)>U_q(r). If p,q have opposite parity, the sum T_p+T_q therefore has the sign of T_p, namely (-1)^(p-1)=(-1)^(p+1). This finishes the proof of the entire theorem.
