"""Bounded exact controls for the analytic hypercomb entry; writes only stdout.

Run with Python 3 and SymPy. No network, optimizer, or growing census.
The all-parameter proof is in the accompanying manuscript.
"""
import json
from fractions import Fraction
from math import comb

import sympy as sp


def mul(p, q):
    out = [0] * (len(p) + len(q) - 1)
    for i, u in enumerate(p):
        for j, v in enumerate(q):
            out[i + j] += u * v
    return out


def add(p, q):
    return [(p[i] if i < len(p) else 0) +
            (q[i] if i < len(q) else 0)
            for i in range(max(len(p), len(q)))]


def recurrence(n, ell):
    a = ell - 1
    f, g = [1, a], [1, a - 1]
    p, q = [1, a + 1], mul(f, add(mul(f, g), [0, 2]))
    if n == 0:
        return p
    for _ in range(2, n + 1):
        p, q = q, mul(f, add(mul(g, q), [0] + p))
    return q


def hypercomb(n, ell):
    """Explicit edge sets, with disjoint private vertices and named spine."""
    edges = []
    next_vertex = n + 1
    for i in range(n):
        edge = [i, i + 1] + list(range(next_vertex, next_vertex + ell - 2))
        next_vertex += ell - 2
        edges.append(edge)
    for i in range(n + 1):
        edge = [i] + list(range(next_vertex, next_vertex + ell - 1))
        next_vertex += ell - 1
        edges.append(edge)
    assert all(len(set(e)) == ell for e in edges)
    assert all(len(set(e) & set(f)) <= 1
               for j, e in enumerate(edges) for f in edges[j + 1:])
    return next_vertex, edges


def direct_counts(n, ell):
    vertices, edges = hypercomb(n, ell)
    masks = [sum(1 << v for v in e) for e in edges]
    counts = [0] * (vertices + 1)
    for selected in range(1 << vertices):
        if all((selected & e).bit_count() <= 1 for e in masks):
            counts[selected.bit_count()] += 1
    while counts[-1] == 0:
        counts.pop()
    assert counts == recurrence(n, ell)
    return {"n": n, "ell": ell, "vertices": vertices,
            "edges": edges, "tested_subsets": 1 << vertices,
            "coefficients": counts}


def main():
    a, s, t, x, w, v, r, p, d, q = sp.symbols("a s t x w v r p d q")
    f, g = 1 + a*x, 1 + (a-1)*x
    A, B = f*g, x*f
    quartic = (A+s*x)**2 + t**2*x*f
    D = (w-a)*(w-a+1)-s*w
    F = v**4-t*v**3+(1-s)*v**2-a*t*v-a*s
    assert sp.cancel(w**4*quartic.subs(x, -1/w) -
                     (D**2-t**2*w**2*(w-a))) == 0
    assert sp.expand(D.subs(w, a+v**2)-t*(a+v**2)*v-F) == 0
    product = sp.Poly(sp.expand((v-r)*(v+p)*(v**2+d*v+q)), v)
    assert sp.expand(product.coeff_monomial(v**2) -
                     (q-r*p-d*(r-p))) == 0
    assert sp.expand(-product.coeff_monomial(v) -
                     (r*p*d+(r-p)*q)) == 0
    assert sp.expand(product.coeff_monomial(1)+r*p*q) == 0

    C = [f+x, f*(A+2*x)]
    for n in range(2, 7):
        C.append(sp.expand(A*C[-1]+B*C[-2]))
    checked = []
    for n in range(2, 7):
        # Off-diagonal products equal -B, exactly as for i*sqrt(B).
        matrix = sp.zeros(n)
        for j in range(n):
            matrix[j, j] = A + (x if j in (0, n-1) else 0)
            if j+1 < n:
                matrix[j, j+1], matrix[j+1, j] = x, -f
        assert sp.expand(f*matrix.det(method="domain-ge")-C[n]) == 0
        checked.append(n)

    controls = [direct_counts(n, ell)
                for n, ell in [(0, 3), (1, 3), (2, 3), (3, 3), (2, 4)]]
    counter = recurrence(5, 3)
    normalized = [Fraction(c, comb(11, k)) for k, c in enumerate(counter)]
    defect = normalized[10]**2-normalized[9]*normalized[11]
    assert defect == Fraction(-6144, 121)
    print(json.dumps({
        "status": "PASS",
        "purpose": "Fixed exact implementation controls, not an infinite proof",
        "quartic_substitution_and_vieta_identities": 5,
        "continuant_identity_exact_in_a_for_n": checked,
        "direct_hypergraph_controls": controls,
        "total_subsets_tested": sum(c["tested_subsets"] for c in controls),
        "stronger_ulc_gate_failure": {"n": 5, "ell": 3, "degree": 11,
                                      "rank": 10, "coefficients": counter,
                                      "normalized_defect": str(defect)}
    }, indent=2))


if __name__ == "__main__":
    main()
