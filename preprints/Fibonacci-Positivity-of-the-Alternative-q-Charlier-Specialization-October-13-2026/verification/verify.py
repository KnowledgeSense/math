"""Exact finite checks accompanying the alternative q-Charlier positivity note.

Author: Knowledge Sense. Contact: math@knowledgesense.jp
Python 3.10 or later; standard library only.
"""
from fractions import Fraction as F
from functools import lru_cache
import json

T, R = F(5, 16), F(3, 8)
MARGIN = 1 - (1 + T) * R / (1 - T)


def det(matrix):
    """Determinant by exact Gaussian elimination, independent of expansions."""
    n = len(matrix)
    a = [[F(x) for x in row] for row in matrix]
    value = F(1)
    for i in range(n):
        pivot = next((j for j in range(i, n) if a[j][i]), None)
        if pivot is None:
            return F(0)
        if pivot != i:
            a[i], a[pivot] = a[pivot], a[i]
            value = -value
        v = a[i][i]
        value *= v
        for j in range(i + 1, n):
            ratio = a[j][i] / v
            for k in range(i + 1, n):
                a[j][k] -= ratio * a[i][k]
            a[j][i] = F(0)
    return value


def tri(diag, upper):
    n = len(diag)
    a = [[F(0) for _ in range(n)] for _ in range(n)]
    for i, v in enumerate(diag):
        a[i][i] = v
        if i + 1 < n:
            a[i][i + 1] = upper[i]
            a[i + 1][i] = F(1)
    return det(a)


def setup(rho, q):
    @lru_cache(None)
    def t(k):
        if k == 0:
            return F(0)
        return (rho * q**(k-1) * (1-q**k) * (1+rho*q**(2*k+1))
                / ((1+rho*q**k)*(1+rho*q**(2*k-1))))

    @lru_cache(None)
    def c(k):
        return q**(k-1)*(1+rho*q**(k-1))/((1+rho*q**(2*k-1))*(1+rho*q**(2*k-2)))

    def x(k):
        return (q**(k-1)*(1+rho*q**(k-2)+rho*q**(k-1)-rho*q**(2*k-2))
                / ((1+rho*q**(2*k-3))*(1+rho*q**(2*k-1))))

    def y(k):
        return (rho*q**(3*k-2)*(1-q**k)*(1+rho*q**(k-1))
                / ((1+rho*q**(2*k))*(1+rho*q**(2*k-1))**2*(1+rho*q**(2*k-2))))

    def a(ell, m, norm=True):
        return tri([1+t(m+j) if norm else x(m+j+1) for j in range(ell)],
                   [t(m+j+1) if norm else y(m+j+1) for j in range(ell-1)])

    def b(ell, m, norm=True):
        first = t(m+1) if norm else y(m+1)
        if ell == 0:
            return first
        diag = [first]+[1+t(m+j+1) if norm else x(m+j+2) for j in range(1, ell+1)]
        upper = [(1+t(m))*t(m+2) if norm else x(m+1)*y(m+2)]
        upper += [t(m+j+2) if norm else y(m+j+2) for j in range(1, ell)]
        return tri(diag, upper)

    def d_closed(ell, m):
        value, product = F(1), F(1)
        for j in range(ell):
            product *= t(m+j)
            value += product
        return value

    def e_closed(ell, m):
        return t(m+1) if ell == 0 else t(m+1)-(1+t(m)-t(m+1))*t(m+2)*d_closed(ell-1, m+3)

    @lru_cache(None)
    def word_value(word, shift, norm=True):
        if not word:
            return F(1)
        if 2 not in word:
            return a(len(word), shift, norm)
        ell = word.index(2)
        tail = word[ell+1:]
        return b(ell, shift+sum(tail), norm)*word_value(tail, shift, norm)

    def word_lower(word, shift):
        if 2 not in word:
            return F(1)
        ell = word.index(2)
        tail = word[ell+1:]
        return MARGIN*t(shift+sum(tail)+1)*word_lower(tail, shift)

    return t, c, x, y, a, b, d_closed, e_closed, word_value, word_lower


def words(weight):
    if weight == 0:
        yield ()
    else:
        for first in (1, 2):
            if first <= weight:
                for tail in words(weight-first):
                    yield (first,)+tail


def require(condition, description):
    if not condition:
        raise AssertionError(description)


def main():
    require(MARGIN == F(25, 88), 'Relative margin')
    parameters = [(F(1,4), F(1,5)), (F(1,8), F(1,10)), (F(1,100), F(1,5))]
    counts = {'factorizations': 0, 'sequence_bounds': 0, 'determinant_pairs': 0,
              'word_shift_parameter_cases': 0}
    for rho, q in parameters:
        t, c, x, y, a, b, d, e, value, lower = setup(rho, q)
        for k in range(1, 17):
            require(x(k) == c(k)*(1+t(k-1)), 'x factorization')
            require(y(k) == c(k)*c(k+1)*t(k), 'y factorization')
            counts['factorizations'] += 2
            require(0 < t(k) <= rho*(1+rho)*q**(k-1) <= T, 't bound')
            require(0 < t(k+1)/t(k) <= q*(1+q)*(1+rho)**2 <= R, 'ratio bound')
            counts['sequence_bounds'] += 2
        for m in range(6):
            for ell in range(7):
                require(a(ell, m) == d(ell, m), 'D determinant expansion')
                require(b(ell, m) == e(ell, m), 'E determinant expansion')
                require(1 <= d(ell, m) <= F(16,11), 'D upper bound')
                require(e(ell, m) >= MARGIN*t(m+1) > 0, 'E lower bound')
                counts['determinant_pairs'] += 1
        for n in range(9):
            for word in words(n):
                for shift in (0, 1, 5):
                    v = value(word, shift)
                    require(v >= lower(word, shift) > 0, 'Word positivity and lower bound')
                    product = F(1)
                    for k in range(shift+1, shift+n+1):
                        product *= c(k)
                    require(value(word, shift, False) == product*v, 'Rescaling identity')
                    counts['word_shift_parameter_cases'] += 1
    toy = {0:F(0), **{k:F(1,4**k) for k in range(1,7)}}
    require(toy[1]-(1+toy[0]-toy[1])*toy[2] == F(13,64), 'Example 12')
    require(toy[2] == F(1,16), 'Example 21')
    require(toy[3]*toy[1] == F(1,256), 'Example 22')
    result = {
        'title': 'Fibonacci positivity of the alternative q-Charlier specialization',
        'author': 'Knowledge Sense', 'contact': 'math@knowledgesense.jp',
        'arithmetic': 'Exact rational arithmetic using Python fractions.Fraction',
        'result': 'pass', 'relative_margin': str(MARGIN),
        'parameters': [{'rho':str(r), 'q':str(q)} for r,q in parameters],
        'sequence_indices': {'min':1,'max':16},
        'determinants': {'ell_min':0,'ell_max':6,'m_min':0,'m_max':5},
        'words': {'weight_min':0,'weight_max':8,'shifts':[0,1,5]},
        'counts': counts,
        'examples': {'12':'13/64','21':'1/16','22':'1/256'},
        'scope': 'Finite exact checks of the displayed identities and bounds. The proof in the paper establishes the theorem for every word, shift and parameter pair in the stated range.'
    }
    print(json.dumps(result, ensure_ascii=False, indent=2))


if __name__ == '__main__':
    main()
