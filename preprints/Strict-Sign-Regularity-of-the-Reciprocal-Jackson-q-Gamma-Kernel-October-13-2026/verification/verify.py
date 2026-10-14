"""Exact rational examples for the reciprocal Jackson q-gamma kernel.

Author: Knowledge Sense
Run: python verify.py > reproduced-results.json
Python 3.10 or later; standard library only.
"""

from fractions import Fraction as F
from itertools import permutations
from math import comb
import json


def product(values):
    result = F(1)
    for value in values:
        result *= value
    return result


def determinant(matrix):
    """Gaussian elimination over rational numbers, including row swaps."""
    a = [[F(value) for value in row] for row in matrix]
    n = len(a)
    result = F(1)
    for k in range(n):
        pivot = next((i for i in range(k, n) if a[i][k]), None)
        if pivot is None:
            return F(0)
        if pivot != k:
            a[pivot], a[k] = a[k], a[pivot]
            result = -result
        value = a[k][k]
        result *= value
        for i in range(k + 1, n):
            multiplier = a[i][k] / value
            for j in range(k + 1, n):
                a[i][j] -= multiplier * a[k][j]
    return result


def determinant_by_definition(matrix):
    """Independent Leibniz sum, used for the small matrices in these examples."""
    n = len(matrix)
    value = F(0)
    for perm in permutations(range(n)):
        inversions = sum(perm[i] > perm[j] for i in range(n) for j in range(i + 1, n))
        value += (-1) ** inversions * product(matrix[i][perm[i]] for i in range(n))
    return value


def checked_det(matrix):
    value = determinant(matrix)
    assert value == determinant_by_definition(matrix)
    return value


def sign(r):
    return (-1) ** (r * (r - 1) // 2)


def pochhammer(a, q, n):
    return product(1 - a * q ** k for k in range(n))


def gamma_integer(q, n):
    assert 0 < q < 1 and isinstance(n, int) and n >= 1
    return pochhammer(q, q, n - 1) / (1 - q) ** (n - 1)


def vandermonde_decreasing(values):
    return product(values[i] - values[j] for i in range(len(values)) for j in range(i + 1, len(values)))


def integer_node_bound(q, xs, ys):
    """Theorem 1.2 after exact cancellation of the infinite products.

    For positive integer y, (q^y;q)_infinity/(q;q)_infinity
    equals 1/(q;q)_(y-1).
    """
    r = len(xs)
    numerator = q ** comb(r, 3) * (1 - q) ** (sum(xs) + sum(ys) - r)
    numerator *= vandermonde_decreasing([q ** x for x in xs])
    numerator *= vandermonde_decreasing([q ** y for y in ys])
    denominator = product(pochhammer(q, q, y - 1) for y in ys)
    denominator *= product(pochhammer(q, q, k) for k in range(r))
    return numerator / denominator


def polynomial(q, s, k):
    return pochhammer(1 - s, q, k)


def run():
    q_values = [F(1, 4), F(1, 2), F(3, 4)]
    families = [([1, 3, 5, 7], [2, 3, 6, 8]), ([0, 1, 4, 6], [1, 2, 4, 7])]
    main_cases = []
    discrete_cases = []
    finite_cases = []
    skipped_cases = []
    example = [[F(1), F(2, 3)], [F(2, 3), F(8, 21)]]
    example_det = checked_det(example)
    example_bound = integer_node_bound(F(1, 2), [1, 2], [1, 2])
    assert example_det == -F(4, 63) and example_bound == F(1, 64)

    for q in q_values:
        for r in range(1, 5):
            for xs_full, ys_full in families:
                xs, ys = xs_full[:r], ys_full[:r]
                matrix = [[1 / gamma_integer(q, x + y) for y in ys] for x in xs]
                signed_det = sign(r) * checked_det(matrix)
                bound = integer_node_bound(q, xs, ys)
                assert signed_det >= bound > 0
                main_cases.append({'q': str(q), 'x': xs, 'y': ys, 'signed_determinant': str(signed_det), 'lower_bound': str(bound)})

            ns = [0, 1, 3, 5][:r]
            mus = [1, 2, 4, 7][:r]
            discrete = [[1 / pochhammer(q ** mu, q, n) for mu in mus] for n in ns]
            signed_discrete = sign(r) * checked_det(discrete)
            assert signed_discrete > 0
            discrete_cases.append({'q': str(q), 'n': ns, 'mu': mus, 'signed_determinant': str(signed_discrete)})

            s = [F(0), F(1, 4), F(1, 2), F(3, 4)][:r]
            v = [F(3, 4), F(1, 2), F(1, 3), F(1, 4)][:r]
            u = [1 - value for value in s]
            finite_bound = q ** comb(r, 3) * vandermonde_decreasing(u) * vandermonde_decreasing(v)
            finite_bound /= product(pochhammer(q, q, k) for k in range(r))
            for truncation in [r - 1, r + 1]:
                h = [[sum((polynomial(q, si, k) * vj ** k / pochhammer(q, q, k) for k in range(truncation + 1)), F(0)) for vj in v] for si in s]
                signed_h = sign(r) * checked_det(h)
                assert signed_h >= finite_bound > 0
                if truncation == r - 1:
                    assert signed_h == finite_bound
                finite_cases.append({'q': str(q), 'r': r, 'M': truncation, 'signed_determinant': str(signed_h), 'fixed_term_bound': str(finite_bound)})

        for s_values in ([F(0), F(1, 3), F(2, 3)], [F(1, 5), F(2, 5), F(4, 5)]):
            for degrees in ([0, 2, 4], [1, 3, 5]):
                minor = checked_det([[polynomial(q, si, k) for k in degrees] for si in s_values])
                assert minor >= 0
                if s_values[0] > 0:
                    assert minor > 0
                skipped_cases.append({'q': str(q), 's': [str(v) for v in s_values], 'degrees': degrees, 'determinant': str(minor)})

    return {'title': 'Exact rational examples for the reciprocal Jackson q-gamma kernel', 'author': 'Knowledge Sense', 'arithmetic': 'fractions.Fraction; no floating-point arithmetic', 'status': 'PASS', 'illustrative_example': {'q': '1/2', 'x': [1, 2], 'y': [1, 2], 'determinant': str(example_det), 'signed_determinant': str(-example_det), 'lower_bound': str(example_bound)}, 'counts': {'main_theorem_and_bound': len(main_cases), 'discrete_corollary': len(discrete_cases), 'finite_truncation_and_fixed_bound': len(finite_cases), 'skipped_degree_polynomial_minors': len(skipped_cases)}, 'main_theorem_and_bound': main_cases, 'discrete_corollary': discrete_cases, 'finite_truncation_and_fixed_bound': finite_cases, 'skipped_degree_polynomial_minors': skipped_cases}


if __name__ == '__main__':
    print(json.dumps(run(), ensure_ascii=False, indent=2))
