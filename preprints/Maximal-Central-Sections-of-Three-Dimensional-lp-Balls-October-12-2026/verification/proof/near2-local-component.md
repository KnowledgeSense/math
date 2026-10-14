# Local derivative Hessian near p=2

## Exact statement

For every p in[2,3] and every u,v in[9/10,1], the normal Hessian of partial_p A satisfies

    Hessian_(u,v)(partial_p A)(p,u,v)<=-(1/1000)I.           (LC1)

In particular, with D(p)=A(p,1,1),

    D'(p)-partial_p A(p,u,v)
       >=[(1-u)^2+(1-v)^2]/2000.                          (LC2)

The square includes points u<v deliberately; all formulas are valid on the full square. The derivative at p=2 is its continuous extension from p>2.

## Analytic bridge

The complete derivative derivation is the fixed file `near2-local-kernel-identities.md`, whose four sections are part of this component's proof. It derives the exact three-sign-sector integral, its first two p derivatives and normal derivatives through third order, and all log-coordinate to physical-coordinate conversions. No mathematical reference beyond these explicit formulas, ordinary calculus, the graph Jacobian and finite interval arithmetic is an input.

On the positive parameter square the coefficient bases uv,v,u are bounded below by.81. In each sign sector at least one factor tau_j is identically1. Thus Q is bounded below by a fixed positive constant. Every parameter derivative used is a finite sum of bounded rational functions of these positive coefficients and factors tau_j^p log^r(tau_j),r<=2. Their zero extensions are continuous and bounded on0<=tau<=1,2<=p<=3. Therefore they pass under the t integral throughout the closed parameter domain. Moving-root logarithmic singularities from the angular parameterization are absent in these coordinates.

At each rational center, the code encloses the Hessian of partial_p A by128-cell interval quadrature. On the first and last t cells it uses the entire interval image. On each other cell it constructs the second t derivative/2 jet and uses h f(mid)+h^3 J2(cell)/12. All jet bases are strictly positive there. The fixed zero-power-log bounds in the identity file handle endpoint cells. The ordinary midpoint Taylor enclosure uses the entire closed cell for its remainder, not a floating estimate.

The seven first variations A_uuup,A_uuvp,A_uvvp,A_vvvp,A_uupp,A_uvpp,A_vvpp are enclosed over each full parameter box by direct128-cell interval integration. Each is integrated with its sign before the absolute upper bound is taken. This bound is valid uniformly over the box because each interval image contains the integrand for every parameter point. There is no unaccounted quadrature error in an interval-image integral.

For radii(rp,ru,rv), the three entry errors are exactly B0ru+B1rv+B4rp, B1ru+B2rv+B5rp and B2ru+B3rv+B6rp. The coordinate-segment mean-value argument stays inside the box. If a,c are the enlarged diagonal upper bounds and b the enlarged absolute off-diagonal bound, the rational conditions

    a+1/1000<0, c+1/1000<0,
    (a+1/1000)(c+1/1000)>b^2

imply (LC1) everywhere on that box by the two-dimensional Schur criterion and the Rayleigh bound using absolute coordinate products. No perturbation estimate for eigenvectors is assumed.

## Complete domain certificate

The40 initial roots are

    [2+k/10,2+(k+1)/10]
       x[9/10+i/20,9/10+(i+1)/20]
       x[9/10+j/20,9/10+(j+1)/20],

with0<=k<10 andi,j in{0,1}. These closed boxes plainly cover the entire required rectangular domain, including p=2 and3 and all normal faces. All endpoints are recorded as integers divided by1000*2^20. Adaptive splits use exact midpoints and keep both children. The full saved partition has7,074 nodes and3,557 accepted leaves, consistent with7074=2*3557-40.

The exact author post-checker `code/check_near2_local.py`, default mode, consumes every root, tree node and leaf. It rejects duplicate or missing geometries, nonpositive widths, incorrect depths, unknown/failed decisions, indivisible splits and incomplete root manifests. It recovers printed outward binary64 endpoints using Fraction.from_float(float(text)) and rederives all entry errors and Schur inequalities. The worst displayed eigenvalue upper is

    -4809792612002777/4611686018427387904 <-1/1000.

More importantly, the independently recomputed rational Schur determinant is positive on every leaf; its minimum is

    2528778127552353830529993935126231 /
    324518553658426726783156020576256000000.

The saved center enclosures are checked by `checks/near2_local.py`; their C++ generator is `components/near-two-and-large-exponents/code/certify-near2-local.cpp`. [MANIFEST.json](../MANIFEST.json) records the distributed files. The checker reconstructs the entry errors and Schur inequalities from the saved enclosures using exact rational arithmetic.

## Consequence from exact stationarity

The original area is invariant under normal-coordinate permutations and is degree-zero homogeneous in the full nonzero normal. At the diagonal, equality of its three normal partial derivatives and Euler's identity imply gradient_(u,v) A(p,1,1)=0 for all p. Differentiating in p is justified by the regularity above, giving exact gradient zero for partial_p A. Its value at the center is D'(p).

For fixed p, the segment from(1,1) to(u,v) stays in the convex square. Taylor integration of (LC1) along this segment gives(LC2), includingp=2. An approximately zero numerical gradient is never substituted for this identity.
