# Near-p2 complementary constants

## 1. Basic bounds

Use the original signed angular integrands

    g=sqrt(S)Q^(-2/p), S=1+u^2+v^2,
    Q=c^p+s^p+|z|^p, z=uc+epsilon vs,

where c=cos(theta),s=sin(theta),0<=theta<=pi/2. Let B=c^p+s^p>=2^(1-p/2). By norm comparison, A<=pi 3^(1-2/p)<=pi 3^(1/3)<5.

Set b=z|z|^(p-2)/Q and t=|z|^(p-2)/Q. Scaling by B^(1/p) and using x^r/(1+x^p)<=1 for0<=r<=p yields

    |b|<=B^(-1/p)<=2^(1/6)<6/5,
    t<=B^(-2/p)<=2^(1/3)<13/10.                            (N2)

Also l_i=w_i/S has |l_i|<=1/2 for w=(u,v).

## 2. p derivatives and the third p derivative

Let omega_j=|a_j|^p/Q for a=(c,s,z), with zero weights defined continuously. Put H=-sum omega log omega, V=Var_omega(log omega), and kappa3=E_omega[(log omega-Elog omega)^3]. Then

    R=g_p/g=2H/p^2,
    R_p=-(4H+2V)/p^3,
    R_pp=(12H+6V-2kappa3)/p^4.                             (N3)

The latter formulas follow from H_p=-V/p and V_p=(2V+kappa3)/p. Here0<=H<11/10 and0<=V<2. To bound the third cumulant, put X=-log omega. Then EX=H and EX^3<=81/e^3<43/10. Thus

    kappa3=-EX^3+3H EX^2-2H^3
           >=-EX^3-2H^3>-7,
    kappa3= -EX^3+3H V+H^3 <=3H V+H^3<8.                 (N4)

These use e>8/3, immediate from its positive series. The moment estimates use max_(0<x<=1) x(-log x)^r=(r/e)^r, with three weights; V<=EX^2<=12/e^2<2.

Since0<=R<11/20 and -21/20<R_p<=0, while -1<R_pp<49/20,

    g_ppp/g=R^3+3R R_p+R_pp

lies strictly between-14/5 and14/5. Integrating A<5 gives |A_ppp|<14. The same estimate applies to D as a special normal. Hence F_pp=D'''-A_ppp<28. All p derivatives pass through the angular integral continuously through p=2, since |x|^p log^r|x| has zero extension for p>=2 and fixed finite r.

## 3. The apparent logarithmic singularity has the favorable sign

For a fixed normal-coordinate index i, let d_i be c or epsilon s. Direct differentiation gives

    g_ii/g=M=1/S-w_i^2/S^2-4l_i b d_i
                 +[2(p+2)b^2-2(p-1)t]d_i^2.

The first term1/S-w_i^2/S^2 is nonnegative. Dropping also the positive b^2 term and applying(N2) gives M>=-38/5. Since R>=0 and R<=11/20, RM>=-209/50.

Let omega=|z|^p/Q, eta=log|z|-Q_p/Q=(log omega+H)/p. Then b_p=b eta and t_p=t eta. Write alpha=1-1/p>=1/2. The entropy representation gives

    |b_p| <= Q^(-1/p)/p [omega^alpha |log omega|+H omega^alpha]
           <= (6/5)/2 [2/e+11/10] <111/100.                (N5)

The exact derivative of M is

    M_p=-4l_i b_p d_i
          +{2(omega-1)t+[4(p+2)omega-2(p-1)]t eta}d_i^2.   (N6)

The possibly singular eta term cannot be bounded by its absolute value near omega=0. Instead put K=4(p+2)omega-2(p-1).

If K<0, then K log omega>=0. Dropping this favorable term, using K>=-2(p-1) and H>=0, bounds the brace in(N6) below by

    -2t-2(p-1)Ht/p >=-13/5-(4/3)(11/10)(13/10)>-13/2.

If K>=0, then KH>=0. Since K<=4(p+2)omega and log omega<=0, K log omega>=4(p+2)omega log omega. Put beta=1-2/p>=0, so t=Q^(-2/p)omega^beta. The same elementary maximum of x^a(-log x) gives

    (t/p)K log omega
       >=-Q^(-2/p)4(p+2)/[p e(beta+1)]
       = -Q^(-2/p)2(p+2)/[e(p-1)] >=-(13/10)*3.

Here2(p+2)/(e(p-1))<=8/e<3. Together with2(omega-1)t>=-13/5, the brace is again >=-13/2. Equation(N5) bounds the linear term of(N6) below by-111/50. Hence

    M_p >=-13/2-111/50=-218/25,
    g_iip=g(RM+M_p) >=-(129/10)g.

Integrating gives A_iip>-(129/10)*5=-129/2, and therefore F_ii=-A_iip<65.

## 4. Endpoint and interpolation meaning

For p>2, all required normal second derivatives of partial_p A have continuous zero extensions. The above bounds apply even when an angular z vanishes. At p=2 the second normal derivative may be unbounded at the normal coordinate axis, so a global classical C2 assertion there is not made. Fix p>2 and apply the usual one-dimensional semiconcavity/chord inequality F>=linear interpolation-65h^2/8 in each normal coordinate. Both F itself and its p endpoint values are continuous as p decreases to2, by domination of the first p derivative integrand. Taking the limit proves the same chord inequality at p=2. Apply p interpolation using the classical F_pp bound28, and then u and v interpolation with nonnegative weights. This proves the claimed closed-box interpolation loss without treating a divergent logarithm as a finite absolute derivative bound.

The bound does not prove F>0 anywhere. It only supplies fresh one-sided constants if a future complete set of strictly positive lower vertex-gap certificates and a diagonal local-neighborhood proof are obtained. The older p[4,6] constants are not used here.
