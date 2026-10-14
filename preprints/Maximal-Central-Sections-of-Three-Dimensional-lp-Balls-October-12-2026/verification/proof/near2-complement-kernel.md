# Near-p2 complementary kernel

## 1. Exact integrands

Let p∈[2,3], u,v∈[0,1], S=1+u²+v². Write c=cosθ,s=sinθ,z_ε=uc+εvs,Q_ε=c^p+s^p+|z_ε|^p, θ∈[0,π/2]. The target first p derivative is the integral of the sum over ε=±1 of

    √S Q_ε^(−2/p) [2 log(Q_ε)/p² − 2 E_ε/(p Q_ε)],
    E_ε=c^p log c+s^p log s+|z_ε|^p log|z_ε|.

Every x^p log x is extended by zero at x=0. The denominator Q≥2^(−1/2), so these first p derivatives extend continuously throughout the closed parameter domain. At each vertex, p,u,v are exact rationals obtained from integer coordinates over 1000·2^20; their interval construction is outward.

The fixed reference is D'(p), evaluated from

    D(p)=3√3∫_0^1 [1+t^p+(1−t)^p]^(−2/p)dt

by differentiating the displayed integrand in p. The diagonal reference is never approximated by a maximum over separate candidates. The logged fields area_lower,area_upper contain p derivatives in this component, not raw areas.

## 2. Jets and direct interval cells

A jet is (f,f',f''/2) with respect to the single integration variable. Product, quotient, power and logarithm operations use exact differentiation rules applied with outward interval arithmetic. For a closed cell of length h, the midpoint enclosure

    h f(midpoint) + h³ J2(cell)/12

contains its exact integral whenever f is C² on that cell. The linear Taylor term integrates to zero; the remaining double-integral weight has integral h³/12 when J2=f''/2. Thus a signed J2 interval, not an absolute empirical error estimate, can be used.

There are N=256 angular cells. If a cosine or sine interval contains zero, or the interval for uc−vs contains zero, that cell is integrated directly by 16 equal subcells. In v4, a further optional numerical safeguard treats a cell directly when the lower absolute bound of uc−vs is at most the upper bound of (u+v)h. This includes zero-adjacent cells whose Taylor enclosure could be excessively wide. It is a quadrature choice, not an additional regularity assertion: direct interval integration is valid on any cell. Every other cell has all nonconstant power-log bases strictly positive, so its second jet is valid.

The case u=v=0 makes z identically zero. Its zero jet and power-log term are exactly zero. In direct subcells the geometric variables are constant jets carrying interval values only; no derivative of abs is formed across a zero. Near a zero, x^p log x for x∈[0,b] and b≤1/2 is enclosed by [b^p log b,0], since p≥2 and its negative minimum occurs beyond1/2. For larger b the code uses a safe global negative bound plus ordinary interval evaluation on strictly positive bases. In actual zero-containing angular subcells, b≤1/2; the branch using [−1,0] is valid for b≤1. The code's zero-containing z intervals cannot reach b>1: their width is bounded by (u+v)h/16<1, as is also true at the endpoint sine/cosine cells. Thus no positive x^p log x is suppressed by this branch.

The diagonal reference uses256 t cells, with the first and last cells directly divided into16 subcells. Other cells have t,1−t>0 and use the same Taylor formula. Differentiation under both integrals is justified by the continuous zero extensions and a positive uniform Q lower bound.

## 3. Cached quantities and output rounding

For each rational p key, the code caches c,s,c^p+s^p and c^p log c+s^p log s at the angular midpoints and full angular cells. These quantities do not depend on u,v. At the first and last full cells they are constant interval jets, because those cells always use direct evaluation. Cached midpoint jets are also constant. Cached interior full-cell jets retain the first and second derivatives. The target-dependent |uc±vs| terms are evaluated afresh. Caching changes neither the formulas nor the enclosing interval operations for reused quantities.

MPFI intervals use80-bit precision. The manual MPFR/MPFI declarations use the Linux x86_64 ABI described in [the verification instructions](../readme.md). The exact checker `checks/near2_complement.py` validates the saved closed cover, binary-rational endpoints and interpolation margins. Upper/lower binary64 endpoints are obtained by directed rounding and written with17 significant digits. Parsing those decimals back to binary64 and then Fraction.from_float recovers the exact directed rational endpoints. Arithmetic proof certificates use those rational endpoints, not approximate decimal comparisons.

## 4. Tensor interpolation and coverage

Set F=D'−partial_p A. On a box p∈[pl,ph], the independently checked one-sided/chord constants are

    F_pp≤448/pl⁴,  F_uu,F_vv≤130/pl.

For widths hp,hu,hv, the eight exact corner intervals therefore imply throughout the box

    F≥min_corners(D'_lower−A'_upper)
         −[(448/pl⁴)hp²+(130/pl)(hu²+hv²)]/8.

The target accepted margin is strictly greater than10^(−6). At p=2 the one-sided coordinate chord inequalities are obtained by continuous limits from p>2, as proved in the fixed constants note; no bounded classical normal second derivative of F is asserted at every p2-axis point.

The initial20 roots pair the ten p intervals[2+k/10,2+(k+1)/10] with normal rectangles[0,.9]² and[.9,1]×[0,.9]. Their union covers the ordered normal triangle outside[.9,1]², including all common faces. Binary splits keep both closed children. The full rational checker must consume every initial root, node and accepted leaf; finite partial output is not a global proof. Reference and target vertices are checked for every leaf with exact rational constants.
