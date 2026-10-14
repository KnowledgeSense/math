# Global interpolation bounds

## 1. Uniform two-sided bounds for the pure normal second derivatives

Write z=u cos(theta)+v sin(theta), B=|cos(theta)|^p+|sin(theta)|^p>=1/2, b=z|z|^(p-2)/Q, t=|z|^(p-2)/Q. Direct differentiation gives

(g_uu)/g = 1/S-u^2/S^2 -4(u/S)b cos(theta) +[2(p+2)b^2-2(p-1)t] cos(theta)^2.

The analogous formula holds for v.

We have |b|<=3/4. Indeed it suffices to show x^(p-1)(4-3x)<=3/2 for x>=0. For x<=1 bound x^(p-1)<=x^2 and maximize x^2(4-3x), obtaining 256/243<3/2. For 1<=x<=4/3 bound x^(p-1)<=x^3, and x^3(4-3x) is decreasing from 1. For x>=4/3 the left side is nonpositive.

Set w=|z|^p/Q in [0,1). The last bracket equals 2t[(p+2)w-(p-1)]. When positive, [(p+2)w-(p-1)]<=5w-2, since it decreases with p. Also

t=B^(-2/p)*w^(1-2/p)*(1-w)^(2/p) <= 2^(2/3)*sqrt(1-w).

The maximum of sqrt(1-w)*(5w-2) on w in [2/5,1] is 2/sqrt(5), attained at w=4/5. Hence the bracket is <=4*2^(2/3)/sqrt(5)<3. If the bracket is negative, the same upper bound is automatic.

Since u/S<=1/2, the formula gives g_uu <=(11/2)g. Every B_p^3 lies inside the Euclidean ball of radius 3^(1/4), so A<=pi*sqrt(3)<11/2. Consequently

A_uu<121/4<31, and A_vv<31.

For a lower bound, t<=1: equivalently x^(p-2)(1-x^2)<=1/2, which for 0<=x<=1 follows from x^(p-2)<=x and max x(1-x^2)=2/(3sqrt(3))<1/2; for x>=1 it is immediate. The first term 1/S-u^2/S^2 is nonnegative, the cross term is >=-3/2, and the last bracket is >=-2(p-1)t>=-6. Thus g_uu>=-(15/2)g. Integrating gives A_uu>-(15/2)*(11/2)>-42, and likewise A_vv>-42. In summary, -42<A_uu,A_vv<31. No mixed-derivative bound is claimed.

## 2. Uniform p-concavity and second derivative bound

At a fixed theta put x=(|cos(theta)|,|sin(theta)|,|z|), weights w_i=x_i^p/Q, H=-sum w_i log w_i, and V=Var_w(log w_i). Zero-weight terms use their continuous zero limits. Then

(log g)_p=2H/p^2,
g_pp/g=4H^2/p^4-4H/p^3-2V/p^3.

Here 0<=H<=log 3<11/10 and 0<=V<=sum w_i log^2(w_i)<=12/e^2<2. Thus g_pp<=0, and g_pp/g>=-(4H+2V)/p^3>=-14/45. Integration and A<11/2 give

-2 < A_pp <=0.

The p derivatives pass under the finite-angle integral because all power-log expressions have uniform integrable bounds for p in [3,4].

## 3. A simple rigorous midpoint quadrature error

Write the three linear forms in Q as l_i(theta), so l_i''=-l_i. Let

T=sum |l_i|^(p-2)*(l_i')^2/Q,
R=sum |l_i|^(p-2)*l_i*l_i'/Q.

Then R^2<=T by Cauchy–Schwarz, and

g''/g=2-2(p-1)T+2(p+2)R^2.

By Holder, T<= (Q(theta+pi/2)/Q(theta))^(2/p). The numerator is <=5 and the denominator >=1/2, so T<=10^(2/3)<5. Therefore -28<g''/g<32. Also B>=2^(1-p/2), by convexity applied to cos(theta)^2+sin(theta)^2=1. Thus Q^(-2/p)<=2^(1-2/p)<=sqrt(2) and sqrt(S)<=sqrt(3), so g<5/2 and |g''|<80.

In the first-quadrant formula A=integral_0^{pi/2}(g_plus+g_minus), the summed second derivative is bounded by 160 in absolute value. Composite midpoint quadrature with N equal cells therefore has absolute error at most

160*(pi/2)^3/(24*N^2) <26/N^2.

All statements are uniform in p,u,v, including zero coordinates. The integrands are C2 because p>=3. The midpoint values must themselves be evaluated with directed rounding; ordinary floating evaluation is not a certificate.

## 4. Verified finite-grid implication

Take c=1/1000 and F=A(p,1,1)-A(p,u,v)-c*((1-u)^2+(1-v)^2). The bounds above imply

F_uu<=42, F_vv<=42, F_pp<=2.

On a rectangular parameter box, successive one-dimensional linear interpolation therefore gives

F >= minimum(vertex values) -[42*h_u^2+42*h_v^2+2*h_p^2]/8,

where h's are full side lengths. No mixed-derivative bound is needed. This follows by applying the elementary one-dimensional lower interpolation error for f''<=M in each coordinate.

For h_u=h_v=1/100 and h_p=1/20, the interpolation loss is 0.001675. With N=384 midpoint nodes, each area error is <26/384^2; the difference of the two area errors is <52/384^2, approximately 0.000352648. Directed-rounding vertex values above the sum of these losses would rigorously prove the complement inequality.

The compact complement is 0<=v<=min(u,17/20), 0<=u<=1. Coordinate-exchange symmetry supplies the swapped vertices of cells touching u=v. The saved certificate contains all 5,031 ordered (u,v) grid nodes and all 21 p grid values, totaling 105,651 vertex triples. Every certified margin, after the interpolation and quadrature losses, is positive. The smallest lower margin is 7726427080913609/18446744073709551616.

On the near-diagonal square [17/20,1]^2, the corrected Hessian certificate proves H<=-(1/500)Id throughout the complete 150-rectangle partition. The exact checker `checks/c4.py` validates both the complementary vertex cover and every corrected local leaf. The derivations and certificate details are given in Sections 6-10 of [proof-interval.md](proof-interval.md).
