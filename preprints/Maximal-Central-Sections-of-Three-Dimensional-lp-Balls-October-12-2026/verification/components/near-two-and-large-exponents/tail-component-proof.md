# All real p >= 100

## 1. Component statement and coordinates

For every real p>=100, the largest central-plane section of B_p^3 has normal in the signed-permutation orbit of(1,1,0), and these are the only maximizers.

Write a normal as(1,u,v),0<=v<=u<=1, and let A_p(u,v) be its Euclidean section area. Put V_p=area(B_p^2), T_p=2^(1/2-1/p)V_p, S=1+u^2+v^2 and S0=1+u^2. By the graph Jacobian,

    A_p(u,v)=sqrt(S) integral_(-1)^1 W_p(u,-vz;R(z)) dz,
    R(z)=(1-|z|^p)^(1/p),                                  (T1)

where W_p(u,h;R) is the length in the y coordinate of the interval

    {y: |y|^p+|uy-h|^p <= R^p}.

At v=0 this gives

    A_p(u,0)=V_p sqrt(1+u^2)/(1+u^p)^(1/p).                 (T2)

The derivative of the logarithm of the normal factor is

    u/(1+u^2)-u^(p-1)/(1+u^p)
      =u(1-u^(p-2))/[(1+u^2)(1+u^p)].                     (T3)

Consequently A_p(u,0)<=T_p for p>2, with equality only when u=1. The value at u=0 is strictly smaller by continuity and monotonicity on(0,1).

## 2. A lower bound for the reference

Using exp(x)>=1+x and monotone integration of the nonnegative logarithmic series,

    V_p=4 integral_0^1 (1-x^p)^(1/p)dx
       >=4[1+(1/p) integral_0^1 log(1-x^p)dx]
       =4[1-(1/p) sum_(k>=1) 1/(k(pk+1))]
       >4(1-2/p^2).                                      (T4)

Indeed sum 1/k^2<2, as follows by comparison of k>=2 with1/[k(k-1)]. Since log2<7/10, for p>=100,

    T_p >=4sqrt2 [1-(log2)/p-2/p^2]
        >4sqrt2[1-18/(25p)].                               (T5)

Also T_p<=4sqrt2. At p=100 the square of the lower bound in(T5) is greater than31, an exact rational comparison; it is increasing in p. Thus T_p>sqrt31 for every p>=100.

## 3. Exact cube reduction, with a small rational certificate

Directly clipping the square in the graph x=-uy-vz gives

    A_infinity(u,v)=4sqrt(S),                         u+v<=1,
    A_infinity(u,v)=sqrt(S)[4-(u+v-1)^2/(uv)],          u+v>=1. (T6)

The second expression is used only when uv>0, with boundary values by continuity. Since B_p^3 is contained in the cube, A_p<=A_infinity.

We claim A_infinity^2<31 outside the rectangle

    N={u>=9/10, 0<=v<=1/10}

within the ordered triangle. In the first case of(T6), a point outside N must have u<=9/10, and

    S<=1+(9/10)^2+(1/10)^2=91/50,

using v<=min(u,1-u) and the monotonicity of u^2+(1-u)^2 for u>=1/2 (u<=1/2 gives S<=3/2). Hence A_infinity^2<=728/25<31.

For the second case, being outside N implies v>=1/10: if u<=9/10, u+v>=1 requires this already. The desired inequality is equivalent to positivity of

    P(u,v)=31u^2v^2-(1+u^2+v^2)[4uv-(u+v-1)^2]^2.          (T7)

Cover this closed region by the following two maps from [0,1]^2:

    (i) v=1/10+(2/5)x, u=1-v+vy;
    (ii) v=1/2+x/2,    u=v+(1-v)y.                         (T8)

After either substitution P is a rational polynomial of bidegree(6,6). Every coefficient of its Bernstein basis of degree(6,6) is strictly positive. The complete exact power and Bernstein coefficients are in `logs/cube_far_bernstein.json`; the minimum of all98 coefficients is509/120000. The basis functions binom(6,i)x^i(1-x)^(6-i) binom(6,j)y^j(1-y)^(6-j) are nonnegative and sum to1, proving P>=509/120000>0 on both squares. There is no adaptive subdivision or floating evaluation in this certificate.

The exact checker `code/check_cube_far_bernstein.py` expands precisely(T7)-(T8) and applies the identity

    b_(i,j)=sum_(a<=i,b<=j) c_(a,b)
              binom(i,a)/binom(6,a) binom(j,b)/binom(6,b).   (T9)

Only rational arithmetic is used after symbolic expansion. This small component certificate is not a claim that the full all-p optimization has been certified.

By(T5)-(T7), any point with A_p(u,v)>=T_p and p>=100 lies in N.

## 4. Sharpening the surviving neighborhood to scale1/p

Put delta=1-u, so0<=delta<=1/10 and0<=v<=1/10. If v<=delta, then S<=2 and

    4sqrt2-A_infinity
      =4(2-S)/(sqrt2+sqrt(S))
      >=sqrt2(2delta-delta^2-v^2)
      >=2sqrt2 delta(1-delta)
      >=(9/5)sqrt2 delta.

This also dominates(9/10)sqrt2 v. If v>delta, the concavity bound for sqrt and sqrt(S)/u>=sqrt2 give

    4sqrt2-A_infinity
      >=sqrt2[2delta-delta^2-v^2+(v-delta)^2/v]
       =sqrt2(1-v)(v+delta^2/v).

By v+delta^2/v>=2delta, this again dominates both(9/5)sqrt2 delta and(9/10)sqrt2 v. Therefore any possible maximizer satisfies, from(T5),

    delta <=8/(5p),       v<=16/(5p).                       (T10)

The weak inequalities suffice throughout. This reduction applies to all real p>=100, including even integers and the previously exceptional normal band.

## 5. Uniform concavity of short central chords

For every fixed u,R, W_p(u,h;R)<=W_p(u,0;R). Indeed the chord length as a function of displacement is concave on its support by the one-dimensional section form of convexity, and is even by central symmetry. This can also be proved directly by taking convex combinations of the two chord endpoints. Outside its support it is zero, so the same maximum inequality holds there.

For |z|<=19/20, p>=100 and(T10), put R=(1-|z|^p)^(1/p). Exact integer comparisons give

    R>=1-(19/20)^100 >497/500,
    2^(1/p)<=2^(1/100)<1007/1000,
    u>=1-8/(5p)>=123/125>49/50.                            (T11)

The comparisons (19/20)^100<3/500 and (1007/1000)^100>2 are included in the integer certificate. For any displacement H with |H|<=v|z|, the positive endpoint a(H)>0 satisfies

    a^p+b^p=R^p,       b=u a-H>0.

The positivity follows continuously from H=0: a=0 would require |H|=R, while b=0 would require H=uR. Both are excluded, since

    |H|/R <= (16/(5p)) (19/20)/(497/500)
            <=1520/49700 <123/125 <=u.

The derivative denominator is D=a^(p-1)+u b^(p-1)>0, and exact implicit differentiation gives

    a'=b^(p-1)/D,
    a''=-(p-1)a^(p-2)b^(p-2)R^p/D^3.                     (T12)

We bound the imbalance on a bin0<=z<=z_hi<=19/20. Since a,b<=R,

    |a-b|<=delta R+|H|
           <=(R/p)[8/5+(16/5)z_hi/(497/500)].

As max(a,b)>=2^(-1/p)R, define the rational bin bound

    K=(1007/1000)[8/5+(16/5)z_hi/(497/500)],

and obtain

    min(a,b)/max(a,b)>=1-K/p.                             (T13)

Every such K is below5, hence below100. For fixed K>0, the function (1-K/p)^p is increasing on p>K. Indeed its logarithmic derivative is log(1-K/p)+(K/p)/(1-K/p)>=0, using log(1-x)>=-x/(1-x). Thus

    [min(a,b)/max(a,b)]^p >=(1-K/100)^100=:rho.             (T14)

The number rho is a positive rational less than1. Put w=a^p/R^p. Then w(1-w)>=rho/(1+rho)^2 because r/(1+r)^2 is increasing for0<=r<=1. Hölder gives

    D<=a^(p-1)+b^(p-1)<=2^(1/p)R^(p-1).

Since0<w(1-w)<1 and p>=2, (w(1-w))^(1-2/p)>=w(1-w). It follows from(T12) that throughout this entire H interval,

    -a'' >=(p-1)/R * (1000/1007)^3 rho/(1+rho)^2.

Let kappa be any positive rational lower bound on the last factor, computed for the bin's upper endpoint. The negative endpoint of the y interval is-a(-H), so W(H)=a(H)+a(-H). It is even and satisfies W''(H)<=-2(p-1)kappa/R throughout the displacement segment. Integrating twice yields

    W(H)<=W(0)-(p-1)kappa H^2/R.                          (T15)

## 6. Sixty-four exact rational chord bins and the Jacobian

Divide[0,19/20] into64 equal bins. For each bin use its upper endpoint in(T13), and set kappa to the downward rounding of

    (1000/1007)^3 rho/(1+rho)^2

to a multiple of10^(-8). The standard-library checker `code/check_tail_chord_100.py` uses integer powers and integer floor division to compute all64 positive values, with no floating arithmetic or transcendental evaluation. The full rational bin endpoints, K bounds and kappa values are in `logs/tail_chord_100.json`.

Apply(T15) on these bins and their reflections, and the non-strict central-chord bound elsewhere in(T1). Since R<=1, the bin integration gives the exact lower bound

    I:=sum_bins 2kappa (z_hi^3-z_lo^3)/3
       =1218353129184303/104857600000000000.

Consequently

    A_p(u,v)
      <=sqrt(S/S0) A_p(u,0)-sqrt(S)(p-1)I v^2
      <=A_p(u,0)+[A_p(u,0)/(2S0)-sqrt(S)(p-1)I]v^2.        (T16)

Here sqrt(1+x)<=1+x/2 was used. By(T3),(T11),

    A_p(u,0)<=T_p<6,   S0>49/25,    sqrt(S)>7/5,

so A_p(u,0)/(2S0)<75/49. For every p>=100,

    sqrt(S)(p-1)I >=(7/5)*99*I
       =844318718524721979/524288000000000000
       >75/49.

The exact positive difference is

    2050017207711376971/25690112000000000000.               (T17)

Thus v>0 implies A_p(u,v)<A_p(u,0)<=T_p. If v=0, (T3) gives strict inequality unless u=1. Every hypothetical maximizer was already confined to(T10), so (u,v)=(1,0) is the unique maximizing ordered normal. Undoing signed coordinate permutations and nonzero scaling proves the component statement and its equality cases.
