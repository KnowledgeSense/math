# The interval 3 <= p <= 4

## 1. Precise claim and scope

Let B_p^3={x in R^3: |x_1|^p+|x_2|^p+|x_3|^p<=1}. Write A(p,u,v) for the ordinary Euclidean two-dimensional area of B_p^3 intersected with x_1+u x_2+v x_3=0. The claim is

A(p,1,1)-A(p,u,v) >= ((1-u)^2+(1-v)^2)/1000

for every real p in [3,4] and every 0<=v<=u<=1.

Sign changes and coordinate permutations preserve B_p^3. Every plane through the origin has a normal which, after these operations and positive rescaling, is (1,u,v) with 0<=v<=u<=1. Thus this statement covers all central planes. Equality can occur only for the all-equal absolute normal coordinates; at (u,v)=(1,1) it does occur. The stability metric is the explicitly normalized-coordinate metric displayed above. No higher-dimensional claim or claim outside p in [3,4] is made.

The proof separates the compact region 0<=v<=min(u,17/20) from the local region 17/20<=v<=u<=1. The former uses a finite vertex certificate plus analytic interpolation. The latter uses a uniformly negative normal Hessian, with its finite interval certificate described below.

## 2. Exact area and regularity

Use graph coordinates x=(-u y-v z,y,z); their Euclidean area Jacobian is sqrt(S), where S=1+u^2+v^2. Polar coordinates y=r cos(theta), z=r sin(theta) give

A(p,u,v)=(1/2) integral_0^(2pi) g(theta) dtheta,

g(theta)=sqrt(S) Q(theta)^(-2/p),
Q(theta)=|cos(theta)|^p+|sin(theta)|^p+|u cos(theta)+v sin(theta)|^p.

On [0,pi/2], let c=cos(theta), s=sin(theta), d=(c,epsilon s), z=u c+epsilon v s, epsilon in {-1,1}; let g_epsilon denote the corresponding g. Reflection in the quadrants gives exactly

A=integral_0^(pi/2) (g_+ + g_-) dtheta.

Throughout the whole parameter domain, B=|cos(theta)|^p+|sin(theta)|^p>=2^(1-p/2)>=1/2, so the denominator is bounded away from zero. Since p>=3, |z|^p is C2 in z. All second normal derivatives of the integrand and all p derivatives used below extend continuously through z=0. Power-log terms are assigned their continuous zero limits. Compact domination therefore justifies integrating those derivatives.

On the local domain u,v in [17/20,1], the third normal derivatives exist pointwise for almost every angle. At p=3 their expressions contain sign(z); the zero set of each nonzero linear form z(theta) has finitely many angles. The third normal derivatives are bounded uniformly on this compact parameter domain and converge almost everywhere under parameter convergence. The dominated convergence theorem, applied also to second-derivative difference quotients via the absolutely continuous function |z| when p=3, gives third normal derivatives of A, continuous as functions of the parameters. This justifies the first-order variation bounds for the Hessian. The p derivatives of the Hessian involve |z|^(p-2) log|z|, which are continuous at zero uniformly for p>=3; the same differentiation-under-integral argument applies. There is no use of a fourth normal derivative at p=3.

The elementary norm inequality ||x||_2<=3^(1/2-1/p)||x||_p shows B_p^3 is contained in the Euclidean ball of radius 3^(1/4). Hence A<=pi sqrt(3)<11/2.

## 3. Analytic normal second-derivative bounds on the whole domain

Put b=z|z|^(p-2)/Q and t=|z|^(p-2)/Q. Direct differentiation gives

g_uu/g=1/S-u^2/S^2-4(u/S)b cos(theta)+[2(p+2)b^2-2(p-1)t]cos(theta)^2.

There is an identical formula after exchanging u,v and cos,sin.

First, |b|<=3/4. It suffices to check x^(p-1)(4-3x)<=3/2 for x>=0 because Q>=1/2+x^p. For 0<=x<=1, x^(p-1)<=x^2 and max x^2(4-3x)=256/243<3/2. For 1<=x<=4/3, use x^(p-1)<=x^3, and x^3(4-3x) decreases from 1. For x>=4/3 the left side is nonpositive.

Second, t<=1. Indeed x^(p-2)(1-x^2)<=1/2: for x<=1 its left side is at most x(1-x^2)<=2/(3sqrt(3))<1/2; for x>=1 it is nonpositive.

For the upper estimate of the last bracket, set w=|z|^p/Q in [0,1). The bracket equals 2t[(p+2)w-(p-1)]. If it is positive, the expression in brackets is <=5w-2, since its derivative with respect to p is w-1<=0. Also

t=B^(-2/p) w^(1-2/p)(1-w)^(2/p)<=2^(2/3)sqrt(1-w).

Since max_{2/5<=w<=1} sqrt(1-w)(5w-2)=2/sqrt(5), the bracket is at most 4*2^(2/3)/sqrt(5)<3. The inequality is automatic when the bracket is nonpositive.

Now 0<=1/S-u^2/S^2<=1 and u/S<=1/2. Thus g_uu<=(1+3/2+3)g=(11/2)g and g_uu>=-(3/2+6)g=-(15/2)g. Integrating, and using A<11/2, gives

-42<A_uu<31,   -42<A_vv<31.                                      (3.1)

No mixed normal derivative bound is needed for the interpolation argument.

## 4. Analytic p second-derivative bounds

At a fixed angle, let x=(|cos(theta)|,|sin(theta)|,|z|), w_i=x_i^p/Q, H=-sum_i w_i log w_i, and V=Var_w(log w_i). Terms with w_i=0 use the limiting value zero. Direct differentiation gives

(log g)_p=2H/p^2,
g_pp/g=4H^2/p^4-4H/p^3-2V/p^3.

Here H<=log 3<11/10 and V<=sum_i w_i log^2 w_i<=12/e^2<2. The last bound follows by maximizing x log^2 x on [0,1], whose maximum is 4/e^2, and summing three terms. Since H<p, g_pp<=0. Dropping the nonnegative first term gives g_pp/g>=-(4H+2V)/p^3>=-14/45. After integration,

-2<A_pp<=0.                                                     (4.1)

These inequalities hold also at the p endpoints by one-sided continuity, and by the same formula in an open p neighborhood where needed to define the endpoint derivatives.

## 5. Uniform quadrature error for areas

Write the three linear forms of theta occurring in Q as l_i, so l_i''=-l_i. Set

T=sum_i |l_i|^(p-2)(l_i')^2/Q,
R=sum_i |l_i|^(p-2)l_i l_i'/Q.

Cauchy-Schwarz gives R^2<=T. Direct differentiation gives

g''/g=2-2(p-1)T+2(p+2)R^2.

Holder gives T<=[Q(theta+pi/2)/Q(theta)]^(2/p). The numerator is at most 1+(sqrt(2))^p<=5, and Q>=1/2. Therefore T<=10^(2/3)<5. It follows that -28<g''/g<32. The sharper denominator bound B>=2^(1-p/2) gives Q^(-2/p)<=2^(1-2/p)<=sqrt(2), while sqrt(S)<=sqrt(3). Hence g<5/2 and |g''|<80. For the quadrant sum |(g_++g_-)''|<160.

The composite midpoint rule with N equal subintervals of [0,pi/2] consequently has absolute error at most

160*(pi/2)^3/(24N^2)<26/N^2.                                    (5.1)

This is the classical second-derivative midpoint remainder, obtained by integrating the second-order Taylor inequality separately on each cell. The integrand is C2 even across its absolute-value zeros because p>=3. The sampled values in the certificate are enclosed using interval arithmetic, not ordinary floating-point approximations.

## 6. Compact-complement reduction to a finite vertex certificate

Define F(p,u,v)=A(p,1,1)-A(p,u,v)-[(1-u)^2+(1-v)^2]/1000. Equations (3.1) and (4.1) give F_uu<=42, F_vv<=42, F_pp<=2. If f''<=M on an interval of length h, then f at every interior point is at least the linear interpolation of its two endpoint values minus Mh^2/8. One way to prove this is to add M x(h-x)/2 to f minus its endpoint interpolation; the resulting function is concave and vanishes at the endpoints.

Apply this in each coordinate, using the nonnegative interpolation weights to preserve earlier error bounds. On a rectangular cell with side lengths h_u=h_v=1/100 and h_p=1/20,

F>=min_vertex F-[42h_u^2+42h_v^2+2h_p^2]/8
  =min_vertex F-67/40000.                                       (6.1)

The certified vertex set consists of

p=3+k/20, u=i/100, v=j/100,
0<=k<=20, 0<=i<=100, 0<=j<=min(i,85).

There are 105651 vertices. At each vertex, code/certify-complement.cpp uses N=384 midpoint samples and 80-bit MPFI intervals to enclose the two approximate areas. It subtracts the stability term, 67/40000, and 52/384^2, the last quantity accounting for the two area errors in (5.1). A strictly positive lower endpoint therefore implies the precise vertex inequality needed in (6.1).

The cells are indexed by 0<=k<20, 0<=j<85 and j<=i<100, with the above mesh widths. They number 98600. Their intersection with u>=v covers the closed compact complement 0<=v<=min(u,17/20), including boundaries by closed cells. A cell with i=j extends slightly into u<v. Its exceptional vertex with u<v is evaluated after swapping u and v; A and F have this exact symmetry, so the swapped node is in the vertex set. Every other vertex is already ordered. code/check_complement_cover.py enumerates all cells and all their corners, checks this swap and membership exactly with integers, checks every recorded vertex index appears exactly once, and checks every lower endpoint is finite and strictly positive. It interprets the printed directed binary64 endpoints as exact binary rational numbers. The proof does not rely on a floating minimum across untested points.

The run completed all 105651 vertices with zero failed tests. The full index/cell checker also passed. The smallest recorded certified margin lower endpoint is the exact binary rational 7726427080913609/18446744073709551616 (approximately 0.00041885045133386846), occurring at p=3, u=95/100, v=85/100. The vertex CSV SHA256 is 5e0f435c5c9358d59462bd79b22641b723ecc5e2aa92ffe844a18bf6c801886f. The checker code SHA256 is a0e6497174cad9e06e83161e2e5f3f70063ad70aed6fd9a14f7823338e08bba1. Every vertex margin already subtracts both interpolation and quadrature losses; no unsampled vertex or cell is inferred from a floating numerical scan.

## 7. Certified derivative bounds on the local square

The auxiliary parameter region is 3<=p<=4 and 17/20<=u,v<=1. The proposed certified bounds are

|A_uuu|, |A_vvv| < 9,
|A_uuv|, |A_uvv| < 6,
|A_uup|, |A_vvp| < 2,
|A_uvp| < 1.                                                    (7.1)

Here is a full specification of the formulas and finite cover producing those bounds. On a quadrant, write w=(u,v), d=(cos(theta),epsilon sin(theta)), z=w dot d, S=1+|w|^2, l_i=w_i/S, and keep b,t,g as above. Logarithmic differentiation gives

L_i=l_i-2b d_i,
L_ij=delta_ij/S-2w_i w_j/S^2-2[(p-1)t-pb^2]d_i d_j,
B_2=(p-1)(p-2)sign(z)|z|^(p-3)/Q-3p(p-1)bt+2p^2b^3,
L_ijk=-2(delta_ij w_k+delta_ik w_j+delta_jk w_i)/S^2
       +8w_i w_j w_k/S^3-2B_2 d_i d_j d_k,
g_ijk=g[L_iL_jL_k+L_ijL_k+L_ikL_j+L_jkL_i+L_ijk].

For the p derivative of a normal Hessian entry, put ell=Q_p/Q, where Q_p=sum x^p log x for x=cos(theta),sin(theta),|z|, and put

R=2 log(Q)/p^2-2ell/p,
t_p=|z|^(p-2)log|z|/Q-t ell,  b_p=z t_p,
M_ij=delta_ij/S-w_iw_j/S^2-2b(l_i d_j+l_j d_i)
      +[2(p+2)b^2-2(p-1)t]d_i d_j,
(M_ij)_p=-2b_p(l_i d_j+l_j d_i)
         +[2b^2+4(p+2)bb_p-2t-2(p-1)t_p]d_i d_j.

Then g_ij=g M_ij and g_ijp=g[R M_ij+(M_ij)_p]. Integrating the plus and minus expressions over the quadrant gives all derivatives in (7.1).

The interval implementation is code/mpfi-signed-derivative-bound.cpp. The driver covers p by 8 intervals of width 1/8, and u,v by 24 intervals of width 1/160 starting at 17/20, taking the 24*25/2 ordered pairs of coordinate intervals. There are exactly 2400 parameter boxes. A diagonal box includes some points with u<v; coordinate-exchange symmetry extends the union and the symmetric derivative bounds to the whole local square. Every parameter box is integrated over 512 equal closed angle cells. The full image interval of the signed derivative integrand on each cell is multiplied by that cell's width and added. This is a rigorous interval Riemann enclosure; no unbounded Taylor error near a zero is used.

At a zero-crossing z cell, sign(z) is enclosed in [-1,1]. The factor |z|^(p-3) has nonnegative exponent, including zero; its interval enclosure contains the value 1 needed for p=3 at nonzero z as well as all limiting values from p>3. Values at the finite zero angles themselves do not affect the integral. Power-log expressions x^b log x, b>=1, are evaluated directly if x has a strictly positive lower endpoint. Otherwise they are enclosed below by -1, since min_{x>=0} x^b log x=-1/(eb)>=-1, and above by 0 if x<=1, or by the interval evaluation at the positive upper endpoint if it exceeds 1. This avoids evaluating log(0).

The complete auxiliary certificate logs/local_signed_derivative_cover.json has SHA256
36617cbb3051623c52b75edaface69d39f3d0fb6161a9a440eef35e01445ea0e.
Its maximum absolute enclosures in the four groups of (7.1) are respectively 8.288312127348627, 5.333031804864571, 1.3073780320626593, and 0.9453100864850059. The exact-rational checker verifies all 2400 box indices, all seven finite derivative intervals per box, and the strict inequalities against 9,6,2,1. It also checks the producing source and binary hashes recorded by the driver.

Important correction: a preliminary estimate anticipated the bound 8 instead of 9 for the pure third derivatives. The actual enclosures do not certify 8. No assertion that the true derivative necessarily exceeds 8 is made. Any preliminary local run using 8 is therefore conditional and cannot by itself certify the theorem. Section 9 explains the independent row-by-row replacement with (7.1).

## 8. Enclosing the normal Hessian at each box center

The center computations in code/certify-local-hessian.cpp use the exact formula g_ij=g M_ij from Section 7, summed over the two quadrant signs. The angle integral uses 128 equal cells. A cell is designated a root cell if either cos or sin has an interval containing zero, or if u cos(theta)-v sin(theta) has an interval containing zero. In a root cell the whole Hessian integrand is interval-enclosed and multiplied by the width. This is valid without any smoothness beyond continuity.

On every other cell all absolute-value signs are fixed and all power bases are strictly positive. The code propagates jets (f,f',f''/2) by exact differentiation rules with interval coefficients. In particular

(fg)_2=f_2 g_0+f_1 g_1+f_0 g_2,
(f/g)_0=f_0/g_0,
(f/g)_1=(f_1-(f/g)_0 g_1)/g_0,
(f/g)_2=(f_2-(f/g)_0 g_2-(f/g)_1 g_1)/g_0,
(f^b)_2=b f^(b-1) f_2+[b(b-1)/2]f^(b-2) f_1^2.

The exponent b is constant for the theta differentiation. The trigonometric jets are (cos,-sin,-cos/2) and (sin,cos,-sin/2). Since every root-containing cell is excluded from this Taylor branch, these jets and the fixed absolute signs apply throughout the cell. If h is its width and m its midpoint, the integral is enclosed by

h f(m)+(h^3/12) interval(f''/2).

This follows from the second-order Taylor remainder and the positive integration kernel; it is valid with only a bound on f'' over that cell. The first-order term integrates to zero. Interval pi and interval widths enclose their exact values throughout. No finite difference, heuristic convergence criterion, or fourth-derivative assumption is used.

Once the three real Hessian entries H11,H12,H22 are enclosed, the larger eigenvalue is enclosed with the algebraic identity

lambda_max(H)=(H11+H22)/2+sqrt(((H11-H22)/2)^2+H12^2).

The upper endpoint is converted to binary64 with rounding toward +infinity and printed to 17 significant digits, sufficient for round-trip recovery of that exact binary endpoint. The certificate retains this endpoint and exact integer coordinates for each accepted box.

## 9. Corrected Hessian variation and exact cover checking

All boxes have exact integer endpoints with common denominator D=1000*2^20. There are initially 150 boxes: ten p intervals of width 1/10, and the fifteen ordered pairs of five u,v intervals of width 3/100 spanning [17/20,1]. They cover the ordered local domain; diagonal rectangles include some unnecessary u<v points. They are bisected at exact integer midpoints adaptively. The exact coordinate center of a box is used in Section 8.

Let r_p,r_u,r_v be its half widths. Equations (7.1) and the fundamental theorem of calculus imply

|H11(x)-H11(center)|<=9r_u+6r_v+2r_p,
|H12(x)-H12(center)|<=6r_u+6r_v+r_p,
|H22(x)-H22(center)|<=6r_u+9r_v+2r_p.

For a symmetric matrix, its operator norm is at most its maximum absolute row sum. Thus the whole box satisfies

lambda_max(H(x))<=lambda_max(H(center))+V_new,
V_new=max(15r_u+12r_v+3r_p,12r_u+15r_v+3r_p).                    (9.1)

The original producing run chose its subdivision based on the unverified pure-third constant 8 and a looser p-off-diagonal constant 2. Its original variation and final-upper columns, as well as its original PASS wording, are not accepted as a certificate of (9.1). They are preserved to document the computation honestly.

The initial postprocessor code/check_certificate_cover.py (SHA256 f3fe985b4394c8b78cd9dd70407df69f15ddb52b43e9d6a273833f7cb6ec4421) ignored both old columns and checked all leaves. For the final theorem input, code/export_corrected_local_certificate.py strips the old error fields entirely and creates logs/local_hessian_corrected_certificate.csv (SHA256 77f991d025d2c71487765828da81860b9b5f52f4597a2ec0cd06d39f6ebe43e6). The final postprocessor code/check_final_local_certificate.py (SHA256 1e34835f3ed9567166b2e4e284414d86fb0e10ee73c1e5db279ae87ef06a8b8d) reads only this corrected file and the fixed derivative certificate. It also checks that the saved corrected rational variation and final bound match its own recomputation exactly, and does not use the old run PASS label. The original raw file remains solely as center-enclosure provenance and correction history. It reads only the exact six box endpoints, denominator, and outward center-eigenvalue endpoint. It computes (9.1) with exact rational arithmetic and the newly certified integer constants 9,6,2,1. Every leaf must separately satisfy the strict inequality

center_eigenvalue_upper+V_new < -1/500.                          (9.2)

No claim that two aggregate error budgets are similar substitutes for these individual tests. The checker also checks all leaves lie in their assigned initial rectangle and recursively verifies that they form an exact gap-free dyadic partition of each of the 150 initial rectangles. At each recursive step it finds a coordinate midpoint crossed by no leaf, partitions the leaves on its two sides, and continues; a singleton group is accepted only if its leaf equals the whole current rectangle. This proves full coverage using integers alone.

 It evaluated 11316 centers and produced 5733 leaves. The corrected postprocessor passed every leaf and the full 150-rectangle partition. The largest corrected upper bound was -0.010765169034357909, strictly below -1/500. The original center-provenance CSV SHA256 is 32865904b990603668a18a2575291e3066db92cfc8ba672fb5f14f2e526a5856; the corrected final certificate hash is stated above. The final exact postcheck JSON SHA256 is 0f934d2417db344f0de93ead8c94934a3aa0f4274d9a328f3b5c51baca5b6ce4.

## 10. Concluding the near-diagonal estimate

The area as a function of a nonzero plane normal is homogeneous of degree zero and invariant under coordinate permutations. It is differentiable near (1,1,1), by the regularity in Section 2. At that vector its three partial derivatives are therefore equal, and Euler's homogeneous-function identity says their sum is zero. They all vanish. Hence the gradient of A(p,u,v) with respect to (u,v) vanishes at (1,1).

Assuming the fully checked certificate (9.2), H<=-(1/500)Id throughout the local square by coordinate-exchange symmetry. The segment from (1,1) to any (u,v) in the local region lies entirely there. Taylor's formula with integral remainder yields

A(p,u,v)-A(p,1,1)
=integral_0^1 (1-t) q^T H(p,(1,1)+tq) q dt
<=-(1/1000)|q|^2,

where q=(u-1,v-1). This is the target inequality in the local region. Section 6 gives the target on its compact complement. Together they cover all parameters specified in Section 1, including all boundaries and p endpoints.

## 11. Directed arithmetic and reproducibility requirements

The numerical interval operations use the installed MPFI 1.5.4 and MPFR 4.2.2 libraries, precision 80 bits. The compiler is g++ Debian 14.2.0-19. The code declares the public MPFR/MPFI ABI structures and links against those libraries; this ABI choice is part of the implementation requiring independent inspection. The MPFR rounding constants used are RNDD=3 and RNDU=2. Every noninteger rational input is obtained by interval division of exactly representable integers, or by decimal-string parsing with outward rounding. All endpoint integers fit within exact binary64 integer range. The code's binary64 constructor is thus exact for those input integers; it is not used to round a decimal parameter inward.

Positive powers on nonnegative interval bases are enclosed by monotonicity in the base and the exponent on each side of base 1. Negative powers use a reciprocal, or interval log/exp when the exponent interval crosses zero; the latter case occurs only for strictly positive bases. At base zero with a nonnegative exponent, setting the lower endpoint to zero is conservative, including the special exponent-zero limit described in Section 7. Every denominator is strictly positive by Q>=1/2 and S>=1. The final checkers reject nonfinite printed endpoints.

The MPFI shared library SHA256 is 19f3197d5239532f9df2c4da0a16660cf2c23e38e2c1438942a884269ae14126. The MPFR shared library SHA256 is 4e3ccf5b442fc91054b0153140fe62939009f98ca1367f45de62376d5b18d28c. Full source, binary, output and input hashes will be fixed in the final manifest.
