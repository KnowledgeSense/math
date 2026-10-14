# The interval 2 < p <= 3

## 1. Precise component conclusion

Let A(p,u,v) be the Euclidean area of the section of the three-dimensional unit ℓ_p ball by x_1+u x_2+v x_3=0, and D(p)=A(p,1,1). For all real2<p≤3 and every ordered normal0≤v≤u≤1, the component proves

    D(p)−A(p,u,v) ≥ (p−2)/2000000 · [(1−u)²+(1−v)²].

Thus equality in A≤D occurs exactly at u=v=1. Signed permutations and scale invariance cover all central planes. At p=2 every section has areaπ; uniqueness is not asserted there.

## 2. Continuous derivative gap and exact stationarity

Put F(p,u,v)=D'(p)−∂pA(p,u,v). The angular formula and its exact first p derivative are specified in near2-complement-kernel.md §1. On[2,3]×[0,1]² the denominators satisfy Q≥2^(−1/2)>0, and x^p log^r x has a continuous zero extension for each fixed r used. Compact domination proves continuity of F, including the entire p=2 face, and permits the p integration below.

Near u=v=1 the fixed-sign-sector formula from near2-local-kernel-identities.md gives parameter derivatives continuously through the required orders. The full normal-area function is invariant under normal-coordinate permutations and is homogeneous of degree zero. At the equal-coordinate normal its three partial derivatives are equal and sum to zero, hence both chart normal derivatives vanish. Differentiating this exact identity in p is justified by the fixed-sector regularity. Thus F(p,1,1)=0 and ∇F(p,1,1)=0 exactly, including at p=2; numerical near-zero values are not used.

## 3. Complete local derivative-Hessian certificate

The fixed proof near2-local-component.md and its full four-section derivative appendix near2-local-kernel-identities.md are parts of this proof. They derive the sector integral, all seven first variations, the logarithmic-to-physical normal derivatives, and the center-to-box mean-value enclosures. Their complete versioned inputs are NEAR2_LOCAL_MANIFEST_v2.json, SHA6c8904fb047da11842338c6a78094e50b4d35a2e787f54ff05b50d3a3079a73f.

The40 closed initial boxes cover[2,3]×[.9,1]². The saved partition has7074 nodes and3557 accepted leaves. The center Hessian of ∂pA uses128-cell midpoint second jets, with endpoint cells direct; the seven full-box variations use128 interval-image cells. Both use fresh80-bit outward interval arithmetic. Every exact rational Schur inequality passes for Hessian(∂pA)≤−I/1000. The minimum rational Schur determinant is

    2528778127552353830529993935126231/324518553658426726783156020576256000000.

Exact gradient zero and integration along the segment to(1,1) give

    F(p,u,v)≥[(1−u)²+(1−v)²]/2000

throughout the local square. This conclusion is uniform in every real p∈[2,3].

## 4. Independently checked complementary interpolation inputs

The full fixed notes near2-complement-constants.md and near2-adaptive-constants.md are parts of the analytic proof. The former establishes the entropy/normal derivative formulas and the p=2 limiting chord interpretation; the latter sharpens their constants to

    F_pp≤448/p⁴,   F_uu,F_vv≤130/p.

 On a closed p box[pl,ph], the upper constants448/pl⁴,130/pl,130/pl are valid throughout. At p=2 these are limiting one-sided chord bounds. No globally bounded classical logarithmic normal derivative at every p2-axis point is claimed.

Successive one-dimensional chord inequalities imply that the minimum of the eight corner lower enclosures, minus[448 hp²/pl⁴+130(hu²+hv²)/pl]/8, is a lower bound for F throughout a box. Only the single differentiable reference D' is used, never a maximum over vertex references.

## 5. Complementary numerical enclosure kernel

The entire five-section near2-complement-kernel.md is part of this proof. It specifies both derivative integrands, the zero extensions, the256-cell angular/t reference quadratures, the second-jet formula h f(mid)+h³J2/12, and the direct16-subcell treatment of zero and zero-adjacent cells. Every remaining Taylor cell has strict positive nonconstant bases. The identically zero z term has exactly zero jet. Cached cosine/sine base quantities depend only on p and are reused without changing their interval meaning.

The code is code/certify-near2-complement.cpp, SHA15193034c4cffbf1af068004016d470dbeb2554970c696982f9f47d13b123787. Printed lower/upper endpoints are directed binary64 bounds written with17 digits and reinterpreted as exact binary rationals. The numerical library and source require independent audit and full replay; author exact post-checking alone is not a separate transcendental implementation.

## 6. Full complementary closed-domain certificate

The20 initial roots pair p intervals[2+k/10,2+(k+1)/10], k=0,…,9, with rectangles[0,.9]² and[.9,1]×[0,.9]. Their union covers every ordered normal outside[.9,1]², including all shared faces and endpoints. The overcovered u<v points are harmless because all formulas and bounds hold on the full square.

The final v4 partition contains46988 nodes, 23504 accepted leaves and 39163 logged per-root vertices. Every root succeeds, every binary split retains both closed children, and the exact checker consumes every node and leaf, rejects duplicate/missing geometries and invalid depths, reconstructs all corner references and p-dependent losses, and verifies a strict margin greater than1/1000000. The minimum exact rational margin is

    400690021173681367/367150017121671371030528.

Thus F>1/1000000 on the entire complement. This is a continuum statement derived from finite interval enclosures and exact coverage, not from sampled point signs. The post-checker also verifies source, binary and constant-note SHA correspondence.

## 7. Integration and every equality case

On the local square, F≥distance²/2000. On the complement, F>1/1000000 and distance²=(1−u)²+(1−v)²≤2. Therefore everywhere

    F≥distance²/2000000.

For each fixed normal, integrate from2 to p, using A(2,u,v)=D(2)=π and continuity of F. This gives the displayed component inequality. Its coefficient is positive for every p>2, so equality forces distance zero. At the diagonal equality holds by definition. There is no omitted interval arbitrarily close to2 and no p2 uniqueness assertion.
