# Near-p2 quadrature bound

## Derivation

For one signed g, write the three amplitudes a=(cos theta,sin theta,u cos theta+epsilon v sin theta), Q=sum|a_j|^p, and weights omega_j=|a_j|^p/Q. All satisfy a_j''=-a_j. Almost everywhere put

    Rtheta=E_omega(a'/a),
    Utheta=E_omega((a'/a)^2),
    ell=E_omega log|a|,
    P=g_p/g=2H/p^2.

Weighted Cauchy and Holder give Rtheta^2<=Utheta<=4, exactly as in FINITE_BRIDGE_PLAN. The angular identity is

    K:=g_thetatheta/g=2-2(p-1)Utheta+2(p+2)Rtheta^2.

Thus -14<=K<=26 and |PK|<=143/10 because0<=P<=11/20. Differentiating K with respect to p yields

    K_p=2(Rtheta^2-Utheta)-2(p-1)Utheta_p
                             +4(p+2)Rtheta Rtheta_p.

Here |2(Rtheta^2-Utheta)|<=8. The covariance expression Rtheta_p=Cov_omega(a'/a,log|a|), together with Var(log|a|)=V/p^2<2/p^2, gives |Rtheta_p|<=sqrt(Utheta V)/p<3/2. Hence the last term has absolute value at most60.

The only potentially logarithmically singular part is

    Utheta_p=sum |a_j|^(p-2)(a_j')^2 log|a_j|/Q-Utheta ell.

Since Q>=2^(-1/2)>7/10, the positive part of ell is at most log(sqrt2)<7/20; the magnitude of its negative part is at most3/(epQ)<45/56<9/10. Thus |ell|<9/10 and integral |Utheta ell|<4*(9/10)*(8/5)=144/25.

For each of a1=cos theta,a2=sin theta, |a|^(p-2)<=1 and |a'|<=1, so the absolute logarithmic numerator integral is at most integral_0^(pi/2)-log(sin theta)dtheta=(pi/2)log2<11/10. For a3=r cos(theta-phi), 0<=r<=sqrt2, write its numerator as

    r^p |cos(theta-phi)|^(p-2) sin^2(theta-phi)
                          *|logr+log|cos(theta-phi)||.

For0<r<=1, r^p|logr|<=1/(ep)<3/16; for1<=r<=sqrt2 it is at most3*(7/20)<11/10. Also r^p<3, cos^(p-2)<=1, integral sin^2<=pi/2<8/5, and any shifted interval of lengthpi/2 has integral |log|cos|| at most its full-period integralpi log2<11/5. Therefore the third amplitude contributes at most

    (11/10)(8/5)+3*(11/5)=209/25.

The case r=0 has zero contribution by its limiting r^p log r value. Dividing the total numerator bound(11/5+209/25)=264/25 by Q>=7/10 gives528/35. Including Utheta ell gives

    integral |Utheta_p| <528/35+144/25 <21.               (Q3)

Finally g<=sqrt3*2^(1/3)<(7/4)(13/10)=91/40<23/10. Therefore, for one sign,

    integral |g_pthetatheta|
      <=(23/10)[(143/10+8+60)*(8/5)+4*21]
       =(23/10)*(5392/25) <500.

Adding signs proves(Q1). All inequalities apply first away from amplitude zeros. For p>2 the indicated second angular derivative of g_p extends continuously at zeros; atp2 it is integrable logarithmic. Alternatively establish the midpoint estimate forp>2 and pass to p2 by uniform convergence of the first p derivative integrand and the common integral bound. No singular point contributes an atom to the second distributional derivative because the first derivative of x^2 log|x| is continuous atzero.

## Midpoint error from an L1 second-derivative bound

On one cell of widthh, the Peano kernel for integral f-h f(mid) is t^2/2 on the left half and(h-t)^2/2 on the right half. Its maximum is h^2/8. Hence the absolute error is bounded by(h^2/8) integral_cell |f''|. Summing and using h=pi/(2N), (Q1) andpi^2<10 gives

    error <1000*pi^2/(32N^2)<(625/2)/N^2<320/N^2.

The same bound encloses the diagonal reference D' and every normal derivative value separately. A future gap lower bound must therefore include both errors, not just the target one. N is an explicit certificate input, not a fitted convergence parameter.
