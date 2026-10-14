# Near-p2 adaptive constants

## Third p derivative

Retain the checked entropy inequalities0<=H<11/10,V<2,-7<kappa3<8 and A<5. From R=2H/p^2, R_p=-(4H+2V)/p^3 and R_pp=(12H+6V-2kappa3)/p^4,

    g_ppp/g=R^3+3R R_p+R_pp.

Dropping the nonnegative terms for a lower bound yields

    A_ppp >-5[6*(11/10)*(42/5)/p^5+16/p^4]
            =-1386/(5p^5)-80/p^4.

Dropping the nonpositive term3R R_p for an upper bound gives, for D as well,

    D''' <5[8*(11/10)^3/p^6+(12*(11/10)+12+14)/p^4]
           =1331/(25p^6)+196/p^4.

Consequently

    F_pp <1331/(25p^6)+1386/(5p^5)+276/p^4
          <=(1331/100+693/5+276)/p^4
           =42791/(100p^4)<448/p^4.                       (A2)

Only p>=2 was used in the last step.

## Normal derivative

Keep the checked |b|<6/5,t<13/10, |l_i|<=1/2. Without replacing p by3 prematurely, the Hessian ratio obeys

    M>=-12/5-(13/5)(p-1)=-(13p-1)/5,
    RM>=-11(13p-1)/(25p^2).

The entropy bound for b_p becomes

    |b_p| <=(6/(5p))[p/(e(p-1))+11/10]
            <9/[20(p-1)]+33/(25p).

In the same sign split K=4(p+2)omega-2(p-1) as the fixed proof, the brace in M_p is bounded below by the worse of

    -13/5-143(p-1)/(50p),
    -13/5-39(p+2)/(40(p-1)).

The second is more negative on[2,3]. Clearing positive denominators reduces this to

    -377p^2+1534p-572>=0,

which follows from concavity and its positive endpoint values988 and637. Therefore

    F_ii <C(p):=5[11(13p-1)/(25p^2)
                   +9/(10(p-1))+66/(25p)
                   +13/5+39(p+2)/(40(p-1))].              (A3)

Multiplying the bracket by p, use

    (13p-1)/p<13,
    p/(p-1)<=2,
    p<=3,
    p(p+2)/(p-1)<=8.

The last inequality is equivalent to(p-2)(p-4)<=0. These bounds give

    p C(p)/5 <143/25+9/5+66/25+39/5+39/5=644/25,
    p C(p)<644/5<130.

This proves(A1) in the same one-sided sense as the checked fixed proof. On a closed p box[pl,ph], safe interpolation constants are448/pl^4 and130/pl in each normal variable. In particular the new constants never exceed the checked28,65,65. They are not inferred from observed derivative samples.
