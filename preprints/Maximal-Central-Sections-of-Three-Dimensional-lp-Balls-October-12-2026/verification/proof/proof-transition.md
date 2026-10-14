# The interval 4 <= p <= 6 and the transition

## 1. Precise conclusion to be certified

Let B_p^3={x in R^3: |x_1|^p+|x_2|^p+|x_3|^p<=1}. By coordinate permutations and sign changes, every central plane has a normal proportional to(1,u,v) with0<=v<=u<=1. Write A(p,u,v) for its Euclidean section area and put

    D(p)=A(p,1,1), T(p)=A(p,1,0).

The theorem asserts that, for all p in[4,6],

    A(p,u,v)<=M(p):=max{D(p),T(p)}.                           (1)

There is exactly one p_* in(499/100,5) with D(p_*)=T(p_*). Below p_* equality occurs only at(u,v)=(1,1); above p_* only at(1,0); at p_* precisely these two points give equality. In the full normal sphere these correspond to their signed-permutation orbits. Both representatives are strict local maxima for every p in[49/10,51/10].

The certificates also establish the following explicit uniform stability estimate, subject to independent validation of this full candidate:

    M(p)-A(p,u,v) >= (1/100000) min{
                         (1-u)^2+(1-v)^2, (1-u)^2+v^2}.       (2)

This uses distance to the union of the two possible normal orbits in the ordered graph chart. It does not assert a uniform quadratic bound to just the unique winning orbit near p_*. Finally M has one-sided derivatives with

    M'_+(p_*)-M'_-(p_*)>1/50.                                (3)

The nearest angle between the two maximizing normal orbits is arccos(sqrt(2/3)), so a choice of maximizing normal orbit changes discontinuously across p_*.

## 2. Area formula, regularity and the two symmetric branches

Parametrize the plane x+uy+vz=0 by(y,z)=r(cos theta,sin theta). The surface area Jacobian is sqrt(S), where S=1+u^2+v^2. Its radial boundary satisfies r^p Q=1, with Q=|cos theta|^p+|sin theta|^p+|u cos theta+v sin theta|^p. Radial integration and pairing opposite quadrants give

    A(p,u,v)=integral_0^(pi/2) [g_+(theta)+g_-(theta)] dtheta,
    g_e=sqrt(S) Q_e^(-2/p),
    Q_e=cos(theta)^p+sin(theta)^p+|u cos(theta)+e v sin(theta)|^p.
                                                                    (4)

Throughout p in[4,6], u,v in[0,1], Q_e>=1/4. The functions |z|^p have three continuous derivatives in z, and the parameter derivatives required below have continuous extensions at z=0; in particular |z|^a log|z| tends to zero for the positive exponents used here. Compact domination therefore justifies differentiating(4) up to the third u,v derivatives and the first p derivative of its u,v Hessian. The second p derivative and the second angular derivative used below also exist with the displayed continuous extensions. No numerical differentiation premise is used.

The diagonal plane splits into six congruent sectors. On one sector use(x_1,x_2,x_3)=(rt,r(1-t),-r). The Jacobian is sqrt(3)r, so

    D(p)=3sqrt(3) integral_0^1 [1+t^p+(1-t)^p]^(-2/p) dt.       (5)

At the two-coordinate plane x_1+x_2=0 one coordinate scales by2^(-1/p), giving

    T(p)=4sqrt(2) 2^(-1/p) integral_0^1(1+t^p)^(-2/p)dt.       (6)

The normal-area function is scale invariant and invariant under coordinate permutations. At(1,1,1), its three first derivatives are equal and their sum is zero by scale invariance; thus A_u=A_v=0 at(1,1). At(1,1,0), permutation of the first two coordinates gives A_u=0, while evenness in the third gives A_v=0. These gradient identities hold exactly at every p, not just at sampled values.

## 3. Unique transverse crossing: independently checked component

For S_t=1+t^p+(1-t)^p and Q_t=1+t^p, direct p differentiation of(5)–(6) gives the integrands

    d_p S_t^(-2/p)=S_t^(-2/p)[2log S_t/p^2-2(S_t)_p/(pS_t)],
    d_p [2^(-1/p)Q_t^(-2/p)]
      =2^(-1/p)Q_t^(-2/p)[log2/p^2+2log Q_t/p^2
                                      -2t^p log t/(pQ_t)].    (7)

`code/probe-branch-intervals.cpp` performs directed80-bit MPFI interval integration on all200 closed p intervals of width1/100 partitioning[4,6], and all1024 closed t intervals of width1/1024. The full signed difference derivative is enclosed on each rectangle, then integrated by multiplying its interval image by the exact width. Every resulting derivative upper bound is less than-1/50. There is no quadrature remainder in this direct interval integration.

At t=0, the power-log function is evaluated by its continuous enclosure: x^a log x>=-1 for the exponents a>=4 in(7), and its upper endpoint is bounded separately. Thus no log0 operation or omitted endpoint is involved.

For the signs, a4096-point directed midpoint sum is used. The unscaled second t derivatives of S_t^(-2/p) and Q_t^(-2/p) have magnitude at most42: S_t,Q_t>=1, first derivatives have magnitude at most6, second derivatives at most30, and |-2/p|<=1/2, (-2/p)(-2/p-1)<=3/4. The second derivative of their complete difference integrand therefore has magnitude less than500. The midpoint remainder is at most500/(24N^2). Including this remainder gives

    D(499/100)-T(499/100) in [299,303]/1000000,
    D(5)-T(5) in [-67,-64]/1000000.                           (8)

The exact endpoint checker verifies all indices and compares the outward binary64 endpoints as exact rational numbers.  Thus F(p)=D(p)-T(p) is strictly decreasing with F'<-1/50, and(8) gives its unique zero p_* in(499/100,5). This component alone does not prove global maximality.

## 4. Fresh global estimates on p in[4,6]

The inclusion B_p^3 subset 3^(1/2-1/p)B_2^3 implies

    A<=pi*3^(1-2/p)<=pi*3^(2/3)<7.                           (9)

For each angular integrand, B=cos^p+sin^p>=2^(1-p/2), so

    0<g<=sqrt(3)*2^(1-2/p)<=sqrt(3)*2^(2/3)<3.                (10)

Set z=u cos theta+e v sin theta, Q=B+|z|^p,

    b=z|z|^(p-2)/Q, t=|z|^(p-2)/Q.

Then |b|<=1 and t<=1. For |z|=x<=1, the first assertion follows from x^(p-1)(1-x)<=x^3(1-x)<=27/256<1/4<=B; the second from x^(p-2)(1-x^2)<=x^2(1-x^2)<=1/4<=B. For x>=1 the assertions are immediate. The logarithmic Hessian formula gives

    g_uu/g=1/S-u^2/S^2-4(u/S)b cos theta
                +[2(p+2)b^2-2(p-1)t]cos^2 theta >=-12,

since u/S<=1/2. The v version is identical. Hence

    A_uu>=-84, A_vv>=-84.                                   (11)

For p derivatives, let w_i be the normalized three terms contributing to Q, H=-sum w_i log w_i, and V=Var_w(log w_i), with zero terms extended continuously. Differentiating gives

    g_pp/g=4H^2/p^4-4H/p^3-2V/p^3.

Here H<=log3<11/10 and V<=sum w_i(log w_i)^2<=12/e^2<2. As H<p, the expression is nonpositive; dropping its positive term gives a lower bound greater than-8.4/64. Combining with(9) gives

    -1<A_pp<=0.                                              (12)

Consequently either fixed-reference gap J=D-A or J=T-A satisfies

    J_uu<=84, J_vv<=84, J_pp<=1.                             (13)

These estimates apply throughout [4,6]. The derivative bounds are derived explicitly below.

For midpoint integration in theta, write the three linear forms in Q as a_i and their angular derivatives as a_i'. Let R=sum |a_i|^(p-2)a_i a_i'/Q and U=sum |a_i|^(p-2)(a_i')^2/Q. Then R^2<=U and Holder gives U<=[Q(theta+pi/2)/Q(theta)]^(2/p)<=36^(2/p)<=6, since the numerator is at most9 and the denominator at least1/4. Direct differentiation yields

    g_theta_theta/g=2-2(p-1)U+2(p+2)R^2,

whose absolute value is at most58. By(10), the second derivative of g_++g_- is bounded in magnitude by348. On the interval of length pi/2 the composite midpoint error is therefore

    <=348(pi/2)^3/(24N^2)<60/N^2.                            (14)

## 5. Local neighborhoods and complete per-box derivative formulas

The prescribed rectangles are

    L_D: p in[4,51/10], u,v in[9/10,1],
    L_T: p in[49/10,6], u in[19/20,1], v in[0,1/10].          (15)

The completed author local certificate proves the uniform Hessian bound

    Hess_(u,v) A <= -(1/1000) I_2                            (16)

on both full rectangles. It recomputes derivative bounds separately on every accepted parameter box, rather than extrapolating old constants.

Here are the formula-to-code identities. Let w_1=u,w_2=v, d_1=cos theta,d_2=e sin theta, l_i=w_i/S. For g in(4), put L_i=(log g)_i and L_ij=(log g)_ij. Then

    L_i=l_i-2b d_i,
    L_ij=delta_ij/S-2w_i w_j/S^2
                         -2[(p-1)t-pb^2]d_i d_j,
    C=(p-1)(p-2)sgn(z)|z|^(p-3)/Q
                         -3p(p-1)bt+2p^2 b^3,
    L_ijk=-2(delta_ij w_k+delta_ik w_j+delta_jk w_i)/S^2
                         +8w_i w_j w_k/S^3-2C d_i d_j d_k,
    g_ijk=g[L_i L_j L_k+L_ij L_k+L_ik L_j+L_jk L_i+L_ijk].     (17)

For the p derivative of the Hessian, let ell=Q_p/Q and

    R=2log Q/p^2-2ell/p,
    t_p=|z|^(p-2)log|z|/Q-t ell, b_p=z t_p,
    M_ij=g_ij/g=delta_ij/S-w_i w_j/S^2
       -2b(l_i d_j+l_j d_i)+[2(p+2)b^2-2(p-1)t]d_i d_j,
    (M_ij)_p=-2b_p(l_i d_j+l_j d_i)
                +[2b^2+4(p+2)bb_p-2t-2(p-1)t_p]d_i d_j,
    g_ijp=g[R M_ij+(M_ij)_p].                                (18)

Equations(17)–(18) follow by differentiating log g, using b_z=(p-1)t-pb^2. They include signed cancellation inside the angular integrals; the interval enclosure is taken only after enclosing the whole signed expression on each angular cell. At z=0 every term has a continuous extension for p>=4. The interval code uses sgn(z) in[-1,1] when its interval crosses zero, and encloses x^a log x by a global lower bound-1 plus its appropriate upper bound when x includes zero; the exponents in(18) are at least2. All these are valid enclosing operations.

## 6. Local numerical kernel and exact finite coverage

`code/certify-local-adaptive.cpp` uses the previously checked80-bit MPFI/MPFR interval primitives and records fresh evaluations on the new domain. Powers with nonnegative bases and positive exponent intervals use outward endpoint extrema; negative exponents use reciprocals on strictly positive bases. Printed floating endpoints are directed binary64 conversions with17-digit round-trip serialization.

For a center Hessian, divide theta in[0,pi/2] into128 cells. A cell on which cos theta, sin theta or u cos theta-v sin theta may vanish is integrated by its direct interval image. Elsewhere the twice-angular-differentiated jet bounds the midpoint remainder. The jet stores the value, first derivative and half the second derivative; thus the interval correction is h^3/12 times its second jet coefficient. The whole exact angular cell and midpoint are enclosed using an interval value of pi. This procedure bounds each Hessian entry, including all absolute-value roots.

On the full parameter box, the seven derivatives A_uuu,A_uuv,A_uvv,A_vvv,A_uup,A_uvp,A_vvp are integrated directly over128 closed angular cells using(17)–(18). Let their absolute interval upper bounds be B_0,...,B_6 and the parameter half-widths be r_p,r_u,r_v. By integrating a derivative along coordinate segments inside the rectangular box, entrywise Hessian errors are bounded by

    e_11=B_0 r_u+B_1 r_v+B_4 r_p,
    e_12=B_1 r_u+B_2 r_v+B_5 r_p,
    e_22=B_2 r_u+B_3 r_v+B_6 r_p.                             (19)

Let h_11^+,h_22^+ be center diagonal upper bounds and h_12^abs the center off-diagonal absolute upper bound. Define a=h_11^++e_11, c=h_22^++e_22, b=h_12^abs+e_12>=0. For any real vector x,

    x^T Hess A x <= a x_1^2+2b|x_1x_2|+c x_2^2.

Thus its maximal eigenvalue is at most that of the matrix with entries(a,b;b,c). The kernel accepts only a rigorously negative bound less than-1/1000. The rational checker separately verifies

    a+1/1000<0, c+1/1000<0,
    (a+1/1000)(c+1/1000)>b^2,                               (20)

using the saved center and derivative intervals as exact rational binary64 endpoints. This avoids relying on a rounded square-root display for final definiteness.

The initial closed boxes are44 diagonal roots:11 p intervals of width1/10 partitioning[4,51/10], and the2-by-2 u,v grid of width1/20 partitioning[9/10,1]^2; and22 two-coordinate roots:11 p intervals partitioning[49/10,6], one u interval[19/20,1], and two v intervals of width1/20. Every endpoint has denominator1000*2^20. A failed box is split at the exact midpoint of one coordinate, with both closed children recorded. No depth-limit or indivisible-midpoint failure is counted as PASS.

Every accepted leaf stores its integer endpoints, center Hessian intervals, all seven full-box derivative intervals, all three errors and the final eigenvalue bound. The complete split tree is stored separately. The exact rational checker replays every tree from its prescribed root and verifies that every leaf is present exactly once, every split has precisely its two closed children and no node is omitted. It then verifies(19)–(20) on every leaf. The completed run and rational checker pass for all66 roots, with19,494 evaluated nodes and9,780 accepted leaves. The least-negative reported eigenvalue upper bound is exactly -4759388817068359/4611686018427387904, strictly below-1/1000. The rational checker verifies strict Schur positivity on every leaf. Thus the certificate covers all parameter points, rather than just its finite centers. The four-worker run took521.679 measured seconds; its maximum individual child RSS was13,312KiB, not an asserted aggregate-memory peak. All hashes are fixed in TRANSITION_INPUT_MANIFEST_v1.json.

## 7. Complementary domains and the fixed-reference choice

Always restrict the normal chart to0<=v<=u<=1. The closed complementary cover consists of

1. p in[4,49/10], v<=9/10;
2. p in[49/10,51/10], v<=9/10 and(u<=19/20 or v>=1/10);
3. p in[51/10,6], u<=19/20 or v>=1/10.                     (21)

Together with(15) these domains cover the entire parameter set; common boundaries intentionally overlap. Partition p additionally at5. In each cell below5 use J=D-A; in each cell above5 use J=T-A. The reference is fixed on the whole cell, including the p=5 boundary. It is legitimate to use D on the short interval(p_*,5] although D<T, because a positive D-A still gives a positive M-A. No interpolation of the vertexwise maximum of two gaps is made.

For explicit initial boxes, use the common u,v ticks0,1/10,9/10,19/20,1 and take the lower triangular family of rectangles with the u interval index at least the v interval index. A rectangle with equal indices also contains points above the diagonal; certifying that larger rectangle is harmless, since(13) holds on the whole cube. Use p slabs[4,4.9],[4.9,5],[5,5.1],[5.1,6]. Omit boxes wholly in L_D or L_T on the corresponding slab. This leaves exactly28 roots and covers the complement in(21). The equal-index rectangles ensure that the diagonal itself is included.

## 8. Complement interval integration and interpolation proof

`code/certify-complement-adaptive.cpp` evaluates(4) at the eight vertices of each box by a512-point directed midpoint sum. Every saved area interval is widened by both signs of60/N^2 from(14). The D or T reference area uses the same rule and its own error interval. Consequently every computed corner gap encloses the exact fixed-reference gap, with both quadrature errors included.

For a twice differentiable one-variable function whose second derivative is bounded above by M, subtracting Mx^2/2 makes it concave. Its value is therefore at least its endpoint linear interpolation minus M t(1-t)h^2/2, hence at least that interpolation minus Mh^2/8. Applying this successively in p,u,v and using(13) proves

    J(p,u,v) >= min_(8 vertices) J -
                   [h_p^2+84h_u^2+84h_v^2]/8.               (22)

This tensor interpolation bound requires no mixed-derivative assumption. Each accepted closed leaf has a rigorous right-hand side strictly greater than1/100000. All interval calculations use the exact rational box endpoints; doubles are used only for outward serialization and the discretionary choice of the next split axis. That axis choice cannot affect correctness, because both children are retained.

The code caches and records every area vertex interval, the complete binary split tree and all accepted leaves. The exact rational checker separately rebuilds each tree from the28 specified roots, fetches all eight corner and reference intervals, recalculates the loss in(22) with rational arithmetic, and verifies the margin1/100000. It interprets printed17-digit strings by recovering their binary64 values exactly; they are not assumed to be exact mathematical decimals. It rejects missing roots, nodes, vertices, unsuccessful leaves and input inconsistencies. The completed run has32,712 evaluated nodes,16,370 accepted leaves and21,391 distinct area vertices across all28 roots. The independent-of-kernel exact rational checker gives minimum exact margin283798894833/28147497671065600, greater than1/100000. The measured kernel run took323.372seconds with maximum child RSS10,240KiB. The final hashes are fixed in TRANSITION_INPUT_MANIFEST_v1.json.

## 9. Global classification and explicit stability from the complete certificates

By the certified bound(16), Taylor's formula along the straight segment from the appropriate exact critical center inside each convex local rectangle gives

    D-A >= [(1-u)^2+(1-v)^2]/2000 on L_D,
    T-A >= [(1-u)^2+v^2]/2000 on L_T.                         (23)

These inequalities are strict away from their respective centers. Adding the nonnegative difference M-D or M-T preserves them. On the complement, the completed certificate gives J>1/100000 and M-A>=J. Thus(1) holds throughout.

Equality cannot occur in the strict complement. Within a local rectangle, equality in M-A requires both the corresponding center and that its branch equals M. The unique crossing and strict branch order from Section3 then give exactly the equality cases in Section1, with no additional normal orbit. Both local Hessian bounds hold on the overlap p in[4.9,5.1], proving coexistence of strict local maxima there.

For the stability claim, put d_union^2=min{(1-u)^2+(1-v)^2,(1-u)^2+v^2}. It is at most1, since0<=v<=u<=1 implies(1-u)^2+v^2<=(1-u)^2+u^2<=1. On either local rectangle, (23) bounds M-A below by d_union^2/2000. On the complement, M-A>1/100000>=d_union^2/100000. This proves(2) uniformly, including at the coexistence parameter. It does not assert vanishing gap at both centers away from p_*.

## 10. The corner and geometric jump

From the global classification, M=D below p_* and M=T above p_*. Both branches are differentiable by(5)–(7). Therefore the one-sided derivative jump is T'(p_*)-D'(p_*)=-F'(p_*)>1/50, proving(3). This use of the branch derivative is made only after the all-normal theorem, not inferred merely from the crossing of two candidate values.

A unit diagonal normal has absolute coordinates(1,1,1)/sqrt3; a unit two-coordinate normal has absolute coordinates(1,1,0)/sqrt2 up to permutation. The largest possible absolute inner product between their signed-permutation orbits is2/sqrt6=sqrt(2/3). Thus their minimal unoriented angle is arccos(sqrt(2/3))>0. The exact equality classification forces a change between these disjoint finite normal orbits as p passes through p_*.

## 11. Computational validity and reproducibility boundary

The interval kernels use the installed MPFI1.5.4 and MPFR4.2.2 libraries. The new local source loads no earlier derivative constants. The new complement source explicitly uses84,84,1 and60/N^2 on[4,6].

The author-side checker is `code/check_full_certificates.py`, with modes `local` and `complement`. `code/run_local_cover.py` records every one of the66 root executions, source/binary hashes, timestamps and measured resource use. The complement run has its own execution manifest. The principal proof input is the final complete set of interval enclosures plus the analytic error/coverage reasoning, not a numerical plot or floating workload plan. The floating planning scripts are retained only as diagnostics and are not read by the exact checkers.

A standard-library checker of saved interval endpoints alone does not certify that the transcendental numerical kernel evaluated the asserted expressions. Independent review must inspect that kernel, its directed rounding, the formula bridge and the continuous root handling, and reproduce the complete outputs or otherwise verify them.
