# The interval 6 <= p <= 100

## 1. Exact conclusion

For every real p∈[6,100] and every ordered normal(1,u,v),0≤v≤u≤1, the component proves

    A(p,u,v)≤T(p):=A(p,1,0),

with equality exactly at(u,v)=(1,0). A is the ordinary Euclidean central-plane section area of the unit ℓ_p ball in R³. Signed normal-coordinate permutations cover all central planes. This is only the remaining finite bridge; the full all-p theorem also uses the separately fixed near2, [3,6], and tail components.

## 2. Geometry, regularity and fixed analytic appendices

The graph area formula is A=∫_0^(π/2)(g_++g_−)dθ, with g_ε=√S[c^p+s^p+|uc+εvs|^p]^(−2/p), S=1+u²+v². It follows by the graph surface Jacobian and radial integration, as in the transition proof. All parameter and angular derivative identities in bridge-kernel-identities.md are part of this proof. That complete four-section appendix writes out the local Hessian, seven first variations, regularity, quadrature, matrix test, fixed-reference integration and software obligations.

On the local finite range[6,16], Q≥1/128. The lowest relevant absolute-power exponent is p−4≥2, and power-log factors have positive exponents≥4. Every derivative used has its continuous zero extension, a compact uniform bound, and may be integrated. The formulas reused from the range [4,6] are algebraic identities only; all new parameter-box derivative integrals are fresh. No old the range [4,6] numerical derivative bound is extrapolated.

The complete fixed notes finite-bridge-constants.md (SHA151f51cf64dbfe1911d2627f51530359a82661e72c34de6b39b4d275cdf64260) and bridge-chord-local.md (SHAad068c7349d0a2c31cce8e49bf064c570410f44bd99180c449e1ba45aa5d7fc6) are also analytic parts of this proof.

## 3. Closed atlas and analytic far exclusion

Use the p endpoints6,7,8,10,12,16,20,30,50,75,100. For each closed slab[pl,ph] let a=1/(4ph),b=1/(2ph). Its local normal rectangle is[1−a,1]×[0,b]. If pl<50, its complementary rectangles are[0,1−a]² and[1−a,1]×[b,1]. Their closed union with the local rectangle covers the ordered normal triangle. The first rectangle overcovers unordered points but contains neither equal T corner of the whole square.

For p≥50 the independently checked cube/volume argument forces every possible competitor A≥T to satisfy1−u<5/(3p),v<10/(3p). On a slab starting at pl≥50, it is therefore enough to consider u≥umin=1−5/(3pl),v≤vmax=10/(3pl). The two complement rectangles become[umin,1−a]×[0,vmax] and[1−a,1]×[b,vmax]; vmax<1−a. Outside this larger closed candidate region strict A<T already follows analytically. This replacement covers every real p of the slab because p≥pl.

The entire atlas and its endpoint arithmetic are specified in bridge-certificate-design.md and logs/bridge_root_atlas.json. All coordinates are integers divided by100800·2^20, including each denominator4ph,2ph,3pl. Every converted integer and center sum is below2^53. There are five numerical local roots and twenty numerical complementary roots, with no open seam at16,50,75 or100.

## 4. The local rectangles

For the five slabs from6 through16 the kernel freshly integrates the area Hessian at exact rational box centers by128 angular jet cells, using direct interval images for root cells. It integrates all seven first variations over each entire parameter box by128 interval-image cells. The mean-value entry errors and exact two-dimensional Schur comparison in the derivative appendix prove Hessian A≤−I/1000 on every accepted leaf.

The full local tree has2035 nodes and1020 accepted leaves over all five roots. The minimum exact rational shifted-Schur determinant is

    19463651437470562548822427322090116659/993838070578931850773415313014784000000.

Every node, midpoint split, leaf, radius and Schur inequality passes the standard-library author exact checker. Exact normal stationarity at(1,0), from evenness and normal-coordinate interchange/homogeneity or the explicit A(p,u,0) formula, yields T−A≥[(1−u)²+v²]/2000 on each such local rectangle. Approximate numerical stationarity is not used.

For p≥16 the separately independently checked chord argument gives A(p,u,v)≤A(p,u,0)−(2/3)v² whenever1−u≤1/(4p),v≤1/(2p). The selected slab rectangle satisfies these inequalities since p≤ph. The explicit formula A(p,u,0)=V_p√(1+u²)/(1+u^p)^(1/p) is strictly increasing in u<1 for p>2, so equality A=T occurs only at(1,0). This proof covers all real p and uses no finite-p sampling or high-p numerical Hessian extension.

## 5. New complementary interpolation and midpoint inputs

Put J=T−A. FINITE_BRIDGE_CONSTANTS_v1 proves J_pp<51/p³ and J_uu,J_vv<24p on the full square for p≥6. Thus on every descendant p box[pl,ph], upper chord constants51/pl³,24ph,24ph are valid. Successive coordinate chord inequalities give the minimum eight-corner J lower bound minus[51hp²/pl³+24ph(hu²+hv²)]/8 throughout the box.

The same note proves |(g_++g_−)_θθ|<56p and the composite midpoint error<10p/N². In each initial root the kernel uses N=64 times its initial upper p endpoint, held fixed for that root. Every target and reference area is interval-evaluated at the midpoint grid and receives its own error[−10p/N²,10p/N²]. There is no cancellation assumption for these two errors. Cached cosine/sine powers depend only on the vertex p and do not change the enclosure. Only the fixedT reference is used; no maximum of vertexwise references is interpolated.

## 6. Optional whole-box cube leaves

For a normal rectangle[ul,uh]×[vl,vh], let d=(ul+vl−1)²/(uh vh) when ul+vl>1, and d=0 otherwise. Set C²=(1+uh²+vh²)(4−d)². In the first case the exact cube-section formula gives A∞≤√C² throughout the box; in the second case the global graph bound A∞≤4√S does. The bracket is positive since0≤d≤1. Thus A≤A∞≤√C².

The entropy formula gives T'(p)≥0, so a reference lower bound at the child box's lower p endpoint applies to every p in that child. If that lower bound exceeds√C²+10^(−7), the entire box is accepted directly. The exact checker reconstructs C² rationally, explicitly checks T_lower>10^(−7), and then compares(T_lower−10^(−7))²>C². It never squares an unchecked negative side. Numerical lower/upper endpoints are interpreted as exact binary rationals.

This cube rule is an alternative to interpolation within one closed binary partition. It can terminate a box without evaluating every corner; unused cached ancestor vertices have no logical role. The exact checker still consumes every tree node and actual leaf and validates the corresponding leaf rule.

## 7. Complete complementary finite certificate

All twenty roots have successful final outputs. Their complete trees contain36546 nodes, 18283 leaves, and33770 logged per-root vertices: 1129 leaves use the cube rule and17154 use tensor interpolation. All roots, exact midpoint children, positive widths, depths, labels, geometries, stored references and rational inequalities pass the full exact checker. In particular every non-cube leaf has strictly positive J margin>10^(−7); its minimum exact rational margin is

    23638152279517/132460998140127870976.

The cube leaves also have strict margin>10^(−7). These are continuum inequalities supplied by the analytic enclosure and closed coverage arguments, not sampled point signs. The source and binary hashes match their run manifests. The exact checks `checks/bridge_local.py` and `checks/bridge_complement.py` verify the supplied local and complementary certificates; the C++ generators and their directed-rounding requirements are described in [the verification instructions](../readme.md).

## 8. Global finite-bridge conclusion and equalities

Every ordered normal lies in a local rectangle, a certified complement rectangle, or, for p≥50, the analytically excluded far region. The latter two give strict A<T. The local arguments give A≤T and force(1,0) for equality. At that point equality holds by definition. Closed p slabs include all their endpoints, so no gap remains at6,7,8,10,12,16,20,30,50,75,100.
