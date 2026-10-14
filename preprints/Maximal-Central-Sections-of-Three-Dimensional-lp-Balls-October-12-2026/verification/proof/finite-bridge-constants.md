# Finite high-p error constants

## 1. Area and normal interpolation bounds

Use the graph chart A(p,u,v), S=1+u²+v², and the two-sign angular integrand g=√S Q^(-2/p), Q=c^p+s^p+|uc±vs|^p, θ∈[0,π/2]. We consider p≥6 and 0≤u,v≤1. The exact cube formula and the two-domain loss proof in the independently checked TAIL_COMPONENT_PROOF_v2 §§3–4 give A≤A∞≤4√2<6, first on the ordered triangle, then on the square by interchanging u,v.

Put z=uc±vs, b=z|z|^(p−2)/Q and t=|z|^(p−2)/Q. Since B=c^p+s^p≥2^(1−p/2), elementary scaling yields |b|≤B^(−1/p)<√2<3/2 and t≤B^(−2/p)<2. In a diagonal normal derivative, with w=u or v and d=c or ±s,

    g_ii/g = 1/S − w²/S² − 4(w/S)bd
              + [2(p+2)b² − 2(p−1)t]d².

The first and b² terms are nonnegative, |d|≤1, and w/S≤1/2. Consequently g_ii/g>−3−4(p−1)=1−4p, whence A_ii>−24p. For J(p,u,v)=T(p)−A(p,u,v),

    J_uu,J_vv <24p.                                           (B1)

## 2. p interpolation bound

For the three probabilities ω_j=|x_j|^p/Q, let H=−Σω_j logω_j and V=Var(logω_j), using the continuous zero conventions. The elementary entropy estimates H≤log3<11/10 and V<2 were proved and independently checked in NEAR2_COMPLEMENT_CONSTANTS. They are probability-simplex statements with no restriction p≤3.

The exact identity is

    g_pp/g = 4H²/p⁴ − (4H+2V)/p³.

It is nonpositive for p≥6 because H<p, and it exceeds −42/(5p³). Integration using A<6 gives A_pp>−252/(5p³)>−51/p³. The same concavity applies to the fixed reference T=A(p,1,0). Therefore

    J_pp <51/p³.                                              (B2)

On a box p∈[pl,ph], valid tensor-chord upper constants are 51/pl³,24ph,24ph. This uses the fixed T reference throughout each box, without interpolating a maximum of references.

## 3. Angular quadrature error

Let y_j=x_j' and x_j''=−x_j along θ, and define R=Σ|x_j|^(p−2)x_j y_j/Q and U=Σ|x_j|^(p−2)y_j²/Q. Weighted Cauchy gives R²≤U. Hölder gives U≤(Q_perp/Q)^(2/p), where Q_perp=Σ|y_j|^p. Here Q≥2^(1−p/2) and Q_perp≤1+2^(p/2)≤2^(1+p/2), so U≤4. Thus

    g_θθ/g = 2−2(p−1)U+2(p+2)R² ∈ [10−8p,26].

For p≥6 its absolute value is <8p. Also g≤√3 B^(−2/p)<2√3<7/2. The sum of the two signed integrands has |f_θθ|<56p. Composite midpoint integration with N equal cells on [0,π/2] has absolute error

    56p(π/2)³/(24N²) <10p/N²,                                (B3)

using π<22/7. All derivatives are continuous at absolute-value zeros for p≥6; the estimate is global. The error must be applied separately to the target and reference values. Outward interval evaluation of the midpoint sum adds rounding uncertainty independently.

## 4. Optional p≥50 far-domain reduction

From the independently checked tail volume argument V_p>4(1−2/p²) and 2^(−1/p)>1−7/(10p),

    T(p)>4√2[1−(7/10+2/p)/p].

For p≥50 this exceeds 4√2(1−37/2500)>√31; the last squared inequality is 32(2463/2500)²>31. Hence a possible competitor A≥T lies in N={u≥9/10,v≤1/10}. The cube losses on N are at least (9/5)√2(1−u) and (9/10)√2 v. Since 7/10+2/p≤37/50,

    1−u ≤74/(45p)<5/(3p),  v≤148/(45p)<10/(3p).              (B4)

This excludes the rest of the chart analytically, with strictness wherever the relaxed inequalities fail. For 50<=p<=100, the surviving shrinking rectangle is included in the verified closed cover in [bridge-proof.md](bridge-proof.md). The range p>=100 is treated in [tail-component-proof.md](tail-component-proof.md).

## 5. Scope and dependencies

For p≥6, these constants use the cube argument in [tail-component-proof.md](tail-component-proof.md), the entropy estimates in [near2-complement-constants.md](near2-complement-constants.md), and elementary differentiation, Hölder, Cauchy, and the midpoint error formula. The local concavity, closed complementary cover and equality classification for 6<=p<=100 are proved in [bridge-proof.md](bridge-proof.md), using the supplied interval certificates and the exact checks `checks/bridge_local.py` and `checks/bridge_complement.py`.
