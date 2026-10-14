# Finite high-p kernel identities

## 1. Local area Hessian and seven variations, 6≤p≤16

For each sign ε let d=(c,εs), z=u c+εv s, Q=c^p+s^p+|z|^p, S=1+u²+v², g=√S Q^(−2/p), w=(u,v), l_i=w_i/S, b=z|z|^(p−2)/Q, t=|z|^(p−2)/Q. All displayed signed integrands are integrated over θ∈[0,π/2] and summed over ε.

The normal logarithmic derivatives are

    L_i=l_i−2b d_i,
    L_ij=δ_ij/S−2w_iw_j/S²−2[(p−1)t−p b²]d_i d_j.

Set

    B=(p−1)(p−2)sign(z)|z|^(p−3)/Q
        −3p(p−1)bt+2p²b³.

Then

    L_ijk=−2(δ_ij w_k+δ_ik w_j+δ_jk w_i)/S²
             +8w_iw_jw_k/S³−2B d_i d_j d_k,
    g_ijk=g[L_iL_jL_k+L_ijL_k+L_ikL_j+L_jkL_i+L_ijk].

For the Hessian itself write

    M_ij=δ_ij/S−w_iw_j/S²
         −2b(l_i d_j+l_j d_i)
         +[2(p+2)b²−2(p−1)t]d_i d_j,
    g_ij=g M_ij.

Let ell=(c^p log c+s^p log s+|z|^p log|z|)/Q, R=2logQ/p²−2ell/p, t_p=|z|^(p−2)log|z|/Q−t ell and b_p=z t_p. Exact p differentiation gives

    (M_ij)_p=−2b_p(l_i d_j+l_j d_i)
        +[2b²+4(p+2)b b_p−2t−2(p−1)t_p]d_i d_j,
    g_ijp=g[R M_ij+(M_ij)_p].

The seven integrated variations are ordered A_uuu,A_uuv,A_uvv,A_vvv,A_uup,A_uvp,A_vvp. Their formulas are the same algebraic identities as the transition formulas, but every interval is freshly integrated over its new p/normal box.

On the full compact bridge local parameter range Q≥2^(1−16/2)=1/128. The lowest absolute-power exponent in the seven variations is p−3≥3; in the second angular derivatives of the center Hessian it is p−4≥2. Power-log factors have positive exponent≥4. Consequently the relevant normal, p and angular derivatives extend continuously at zeros and pass under the integral by compact domination. The jet implementation still treats zero-containing cells directly, so it never divides by an absolute-value zero.

## 2. Local integration and exact matrix certification

At a rational box center,128 closed angular cells cover[0,π/2]. Root cells use their full interval images, all others the second-order jet midpoint enclosure h f(mid)+h³ J2(cell)/12, J2=f''/2. The seven variations use direct128-cell interval integration over the full parameter box, followed by the maximum absolute endpoint of the integrated signed interval. This is uniform over every parameter point; it is not an unproved sign/cancellation assumption.

For parameter radii rp,ru,rv and variation bounds B0,…,B6, the three Hessian entry errors are B0ru+B1rv+B4rp, B1ru+B2rv+B5rp, B2ru+B3rv+B6rp. Coordinate-segment mean values remain inside the box. If a,c are the enlarged diagonal upper endpoints and b the enlarged absolute off-diagonal bound, the exact Schur conditions a+1/1000<0,c+1/1000<0,(a+1/1000)(c+1/1000)>b² imply Hessian A≤−I/1000, by comparing quadratic forms using absolute coordinate products.

The exact gradient of A at(1,0) vanishes: evenness gives A_v=0, while either normal-coordinate interchange plus degree-zero homogeneity, or direct differentiation of A(p,u,0), gives A_u=0. The segment from this center to every point of the chosen local rectangle stays in that rectangle. Hence a successful full local certificate implies T−A≥[(1−u)²+v²]/2000 there, with the exact equality case.

The implementation's zero power-log improvement for x∈[0,b],b≤1/2, exponentα≥2 follows from derivative sign αlogx+1<0. It uses[b^α log b,0]. Its global negative bound on a wider interval is safe because x^α log x≥−1/(eα)>−1; if the upper endpoint exceeds1, its positive value is also included by the original general branch. Zero bases with positive powers are zero; inverse/negative powers occur only at strictly positive Q or geometric denominators.

## 3. Complementary interpolation and raw area integration

The fixedT complementary integrand is the original g_++g_− without p differentiation. At each rational vertex the midpoint sum uses N=64ph, where ph is the exact integer upper p endpoint of that initial root. Its interval enclosure receives an added[−10p/N²,10p/N²]. This is a proved global midpoint bound from FINITE_BRIDGE_CONSTANTS_v1 §3, not an observed convergence rate. Reference T and target A get separate errors.

On a descendant box the chord constants are recalculated as51/pl³,24ph,24ph from its own exact p endpoints; they follow from the independently checked note for all p≥6. The minimum eight-corner reference-minus-target lower bound minus the width-squared chord losses certifies that entire closed box. No maximum of separate references is interpolated.

The cube pretest is an independent alternative leaf rule, described and proved in BRIDGE_CERTIFICATE_DESIGN_v1. It bounds A∞ on the whole normal rectangle by a rational squared expression and uses monotonicity of T in p. The exact checker reconstructs the expression and compares positive squares; it never uses a midpoint-only cube estimate. The analytic p≥50 far-region exclusion and p≥16 chord-local result are separately fixed and independently checked inputs.

## 4. Software and finite-domain obligations

Both kernels use the same published80-bit MPFI/MPFR wrappers as the the transition formulas framework.  Directed binary64 bounds printed with17 digits are treated as exact binary rationals. Adaptive decisions may use floating comparisons only after forming rigorous interval upper/lower bounds; split choices do not assert mathematical inequalities. The exact post-checkers recover every closed initial root and midpoint split and verify every Schur, cube or interpolation inequality. Failing or interrupted output is not a proof leaf.

The complete initial atlas and all-integer denominator arithmetic are given in BRIDGE_CERTIFICATE_DESIGN_v1 and logs/bridge_root_atlas.json. Empty/missing outputs, an incomplete root set, or a successful pilot alone cannot establish the bridge.
