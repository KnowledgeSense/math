# Near-p2 sector and differentiation identities

## Fixed endpoints and logarithmic coordinates

Use the exact three-sector area formula(E9) in ENDPOINT_ANALYSIS.md. In every summand G=uv sqrt(S)Q^(-2/p), write

    Q=(uv)^p tau0^p+v^p tau1^p+u^p tau2^p,

where(tau0,tau1,tau2) is(1,t,1-t),(t,1,1-t), or(t,1-t,1). Let alpha=logu,beta=logv, a=(u^2,v^2)/S, q_j the three summands of Q, and e_j=log(coef_j tau_j), with coef=(uv,v,u). Define

    w_i=q_(i+1)/Q, c_i=partial_p w_i,
    d_i=partial_pp w_i, i=0,1,
    E=sum(q_j e_j)/Q, E2=sum(q_j e_j^2)/Q.

All moments q_j e_j and q_j e_j^2 extend continuously to zero at tau_j=0. They are computed by factoring coef_j^p and expanding powers of log(coef_j)+log(tau_j), so no log0 is evaluated. Then

    c_i=q_(i+1)e_(i+1)/Q-w_i E,
    d_i=q_(i+1)e_(i+1)^2/Q-2E q_(i+1)e_(i+1)/Q
                     +2w_i E^2-w_i E2.                   (L1)

The special exponent vectors(1,1),(0,1),(1,0) give

    partial_i w_i=-p w_i(1-w_i),
    partial_j w_i=p w_i w_j, i!=j.                        (L2)

Here i,j are log coordinates, not the original u,v derivatives.

## Logarithmic derivatives

Let L_i=partial_i logG, L_ij=partial_ij logG, and similarly for third derivatives. Put R=partial_p logG. Directly from(L1)-(L2),

    L_i=-1+a_i+2w_i,       L_ip=2c_i,       L_ipp=2d_i,
    L_ii=2a_i(1-a_i)-2p w_i(1-w_i),
    L_ij=-2a_i a_j+2p w_i w_j  (i!=j),
    L_iip=-2w_i(1-w_i)-2p c_i(1-2w_i),
    L_ijp=2w_i w_j+2p(c_i w_j+w_i c_j),
    L_iipp=-4c_i(1-2w_i)-2p[d_i(1-2w_i)-2c_i^2],
    L_ijpp=4(c_i w_j+w_i c_j)+2p(d_i w_j+2c_i c_j+w_i d_j). (L3)

The third log-normal derivatives and their p variations are

    L_iii=4a_i(1-a_i)(1-2a_i)+2p^2 w_i(1-w_i)(1-2w_i),
    L_iij=-4a_i a_j(1-2a_i)-2p^2 w_i w_j(1-2w_i),
    L_iiip=4p w_i(1-w_i)(1-2w_i)
                      +2p^2 c_i(1-6w_i+6w_i^2),
    L_iijp=-4p w_i w_j(1-2w_i)
               -2p^2[c_i w_j(1-4w_i)+w_i c_j(1-2w_i)].    (L4)

All mixed derivatives are symmetric under index permutation. The p derivatives of logG are

    R=2logQ/p^2-2E/p,
    R_p=-4logQ/p^3+4E/p^2-2(E2-E^2)/p.                   (L5)

These formulas follow by differentiating finite positive weighted sums, with endpoint extensions handled afterward. The p2 first-variation entropy formula independently gives A_uuup=A_uuvp=A_uvvp=A_vvvp=2pi/27 at u=v=1, consistent with the recorded interval enclosures.

## Product-rule bridge to physical derivatives

Set M_ij=L_iL_j+L_ij and

    B_ijk=L_iL_jL_k+L_ijL_k+L_ikL_j+L_jkL_i+L_ijk.

Then

    G_ip=G(RL_i+L_ip),
    G_ijp=G(RM_ij+M_ij,p),
    G_ijkp=G(RB_ijk+B_ijk,p),
    G_ipp=G[(R^2+R_p)L_i+2R L_ip+L_ipp],
    G_ijpp=G[(R^2+R_p)M_ij+2R M_ij,p+M_ij,pp].            (L6)

Every derivative on the right is expanded by the ordinary product rule in the kernel. No sign of an integrand is assumed. Convert from log coordinates by

    G_uup=(G_alphalphap-G_alphap)/u^2,
    G_uvp=G_alphbetap/(uv),
    G_uuup=(G_alphalphalphap-3G_alphalphap+2G_alphap)/u^3,
    G_uuvp=(G_alphalphbetap-G_alphbetap)/(u^2 v),

and the symmetric v formulas. The pp conversions are the same second-normal conversion with p replaced by pp. Integrating the three sectors gives the Hessian of partial_p A and its seven first variations in the array order

    A_uuup,A_uuvp,A_uvvp,A_vvvp,A_uupp,A_uvpp,A_vvpp.         (L7)

## Enclosure and quadrature design

The center Hessian is integrated with a second-order t jet on128 cells. The first and last cells are evaluated directly as interval images; on all other cells, every tau is positive, so the jet(log/power) derivatives are classical and bounded. A jet stores(f,f',f''/2). The midpoint enclosure is h f(mid)+h^3 J2(cell)/12. Parameter intervals are treated as constants in this t differentiation.

Whole-parameter-box first variations are integrated directly by interval images on128 closed t cells. At a zero endpoint, t^p logt has its continuous limit0 and lies between t_hi^p log(t_hi) and0 for t_hi<=1/2,p[2,3]. Likewise t^p log^2t lies between0 and t_hi^p log^2(t_hi) when t_hi<=1/4. These inequalities follow from the derivative signs and p>=2. For a wider zero-touching interval, the safe bounds[-1,0] and[0,1] are used. All coefficient bases u,v remain strictly positive.

Take absolute upper bounds of the seven full derivative integral enclosures. For radii(rp,ru,rv), the three Hessian entry errors are

    e11=B0 ru+B1 rv+B4 rp,
    e12=B1 ru+B2 rv+B5 rp,
    e22=B2 ru+B3 rv+B6 rp.

These are ordinary mean-value bounds along coordinate segments inside the same parameter box. Add them to the center diagonal upper bounds and to the off-diagonal absolute upper bound, then certify the strict2x2 Schur criterion after adding(1/1000)I. An independently replayable closed binary partition is required before any full-neighborhood claim.
