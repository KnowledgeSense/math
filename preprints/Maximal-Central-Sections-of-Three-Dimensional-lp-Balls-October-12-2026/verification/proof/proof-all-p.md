# Assembly of the five parameter ranges

## 1. Exact classification theorem

Let B_p³={x∈R³:Σ|x_i|^p≤1} for real finite p>2. For a nonzero normal a, let its section area be the ordinary Euclidean two-dimensional measure of B_p³∩a^⊥. Let D(p) be the area for a=(1,1,1), and T(p) the area for a=(1,1,0).

There is exactly one real p_*∈(499/100,5) with D(p_*)=T(p_*). The classification is:

- For2<p<p_*, the only maximizing normals are the signed-permutation and nonzero-scaling orbit of(1,1,1).
- Forp>p_*, the only maximizing normals are the corresponding orbit of(1,1,0).
- Atp=p_*, precisely those two orbits maximize.

Equivalently, every central plane section has area at most max{D(p),T(p)} for every real p>2, with exactly these equality cases. This is a three-dimensional theorem only; no classification in dimensionsn≥4 is claimed. At p=2 every plane has areaπ and no uniqueness assertion is made.

Both representative normals remain strict local maxima on49/10≤p≤51/10. The optimized area M(p)=max{D(p),T(p)} has a derivative jump

    M'_+(p_*)−M'_−(p_*)>1/50.

The minimum angle between the two maximizing unoriented normal orbits is arccos√(2/3)>0. Hence a maximizing normal orbit changes discontinuously acrossp_*.

## 2. Exact chart and the two branches

Coordinate signs and permutations preserve B_p³. Normalize a largest absolute normal coordinate to1 and order the other absolute coordinates, obtaining(1,u,v),0≤v≤u≤1. Every central plane has such a representative. Write A(p,u,v) for its Euclidean area. With S=1+u²+v², graph parameterization and radial integration give

    A(p,u,v)=∫_0^(π/2) √S Σ_(ε=±1)
        [cos^pθ+sin^pθ+|u cosθ+εv sinθ|^p]^(−2/p)dθ.

The exact symmetric branch formulas are

    D(p)=3√3∫_0^1[1+t^p+(1−t)^p]^(−2/p)dt,
    T(p)=4√2·2^(−1/p)∫_0^1(1+t^p)^(−2/p)dt.

The first is the six-sector diagonal parameterization; the second follows by scaling one coordinate of a two-dimensional ℓ_p disk, or its paired-sector radial formula. All areas use the same Euclidean normalization. They are continuous in p, and the p derivatives used in the transition interval exist by compact domination. No unnormalized comparison is substituted for an area ratio.

## 4. Assembly across every endpoint and equality case

The union(2,3]∪[3,4]∪[4,6]∪[6,100]∪[100,∞) is every finite real p>2. All finite seams3,4,6,100 are closed on both adjacent components. The first component reaches arbitrarily close to2, and the tail reaches arbitrarily large real p. There is no omitted parameter interval, parity exception or normal-coordinate band.

For2<p≤4, the first two components show diagonal maximality with equality only at(1,1). In particular D>T there, because(1,0) differs from(1,1). Forp≥6, the bridge and tail show two-coordinate maximality with equality only at(1,0), henceT>D because the diagonal is a different normal. On[4,6] the crossing classification applies. Therefore its crossing is the only equality D=T on the entire p>2 range, and the stated branch is strictly the larger one on each side. No derivative-sign bound from[4,6] is extrapolated outside that interval.

Every ordered normal is covered by the component valid at its p, including v=0,u=v,u=1 and the coordinate-axis plane. Its equality case is exactly the one stated there. Undoing signed permutations and nonzero normal scaling gives precisely the full-sphere orbits in the theorem; no additional normals appear at the seams.

## 5. Transverse transition and the scope of stability

On a neighborhood ofp_* the optimized area equals D on the left and T on the right. The transition proof gives T'(p_*)−D'(p_*)>1/50, so the displayed one-sided derivative jump follows. It also proves both critical normal representatives are strict local maxima throughout[49/10,51/10]. These properties are inherited exactly within that interval and need no high-p derivative extension.

The unit normals are(1,1,1)/√3 and(1,1,0)/√2. Their largest absolute scalar product over the signed-permutation orbits is√(2/3), proving the orbit separation angle. Any selection of globally maximizing normal orbit must therefore change discontinuously atp_*.

The component packets retain their explicit stability estimates, including the near2 factorp−2 and the transition interval's distance to the union of the two possible orbits. This assembled theorem does not assert a uniform quadratic constant to only the winning orbit acrossp_*: such a statement is not supplied by the component estimates. No unsupported all-p uniform stability coefficient is added.
