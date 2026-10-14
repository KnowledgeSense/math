# Finite high-p atlas and certificate design

## Domain decomposition

Use the exact p endpoints

    6,7,8,10,12,16,20,30,50,75,100.

On a slab [pl,ph], put a=1/(4ph), b=1/(2ph). The local rectangle is [1−a,1]×[0,b]. For the five slabs through16, a fresh interval kernel will certify Hessian A≤−I/1000. Exact stationarity at (1,0) then gives a positive quadratic T−A gap there. The u derivative vanishes by the symmetry interchanging the two nonzero normal coordinates; the v derivative vanishes by evenness. For the five slabs starting at16, the independently checked BRIDGE_CHORD_LOCAL_v1 applies directly, since a≤1/(4p) and b≤1/(2p).

For pl<50, two complementary rectangles suffice:

    R0=[0,1−a]²,   R1=[1−a,1]×[b,1].

Their union with the local rectangle covers every ordered normal 0≤v≤u≤1. R0 overcovers unordered points but contains neither T maximizing corner, since both its upper coordinates are strictly below1. This avoids the false assertion of strictness on the entire square including the second equivalent corner(0,1).

For pl≥50, the independently checked far-domain exclusion reduces every possible competitor to

    u≥umin=1−5/(3pl),   v≤vmax=10/(3pl).

The complementary rectangles are then

    R0=[umin,1−a]×[0,vmax],
    R1=[1−a,1]×[b,vmax].

These rectangles and the local rectangle cover the full candidate region. Here vmax<1−a, so writing min(vmax,1−a) in the kernel for R0 gives the same interval. The boundaries are all retained. Outside the candidate region strict A<T follows analytically.

There are exactly five numerical local roots and twenty numerical complement roots. All endpoints are integer multiples of 1/(100800·2^20): 100800 is divisible by every denominator4ph,2ph,3pl used here. This also leaves enough powers of two for adaptive midpoint refinement. Every float conversion of a recorded integer is exact because its magnitude is below2^53.

## Local numerical kernel

code/certify-bridge-local.cpp reuses the already derived seven ordinary area variations from the range [4,6], with all new per-box integrals over p[6,16]. The center Hessian is integrated using128 angular second-order jet cells, with root cells directly enclosed; the seven variations are integrated over the full box using128 interval-image cells. The three propagated errors use the corresponding parameter radii. A Schur test verifies the margin1/1000. No numerical Hessian or derivative bound from the range [4,6] is reused.

At every zero-containing power-log factor x^α log x with α≥2 and upper x≤1/2, the fresh local kernel uses [b^α log b,0]; this is a valid improvement of the earlier universal[−1,0] enclosure. For larger intervals the earlier safe global negative bound remains. All absolute-power derivatives needed are continuous for p≥6. A complete exact replay of all five roots and Schur inequalities is required.

## Complement kernel and optional cube leaf

code/certify-bridge-complement.cpp uses the fixed T reference, new interpolation constants51/pl³,24ph,24ph and midpoint error10p/N² for each individual area. For root slab upper endpoint ph it chooses N=64ph throughout that root. This choice is only a computational precision setting: success still requires the full outward error at every vertex and every exact leaf inequality.

Before expensive interpolation, an entire box can be excluded using the cube. For normal bounds ul≤u≤uh,vl≤v≤vh, set

    d=max(0,ul+vl−1)²/(uh vh)  if ul+vl>1, otherwise d=0,
    C²=(1+uh²+vh²)(4−d)².

When ul+vl>1, the exact cube formula gives A∞≤√C²; otherwise the global bound A∞≤4√(1+u²+v²) does. Denominators are positive in the first case and0≤d≤1. Since A(p,u,v)≤A∞ and T is increasing in p (its entropy first derivative is nonnegative), a lower bound for T(pl) exceeding √C² proves strict exclusion of the whole box. The exact checker reconstructs C² rationally and squares positive sides; it does not rely on a sampled cube bound.

Other leaves use the tensor chord lower bound and require margin>10^(−7). Both kinds of leaves stay in one exact binary partition with all closed children. A cube leaf may terminate before evaluating all corner areas; unused cached ancestor vertices are allowed but supply no inference. Every used bound must be validated by the numerical kernel audit and fresh replay.
