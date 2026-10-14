"""Exact checks accompanying the paper on x exp(i m pi x).
Author: Knowledge Sense. Python standard library only.
Polynomial arrays store coefficients from constant term to highest degree.
The published coefficient fixture is from Lyu and Zhou, arXiv:2607.19797v1,
Appendix C(4), PDF page 21. The table fixture is Table 1 of the accompanying paper.
"""
import argparse
import json
import math
from fractions import Fraction
from pathlib import Path

def trim(a):
    while len(a) > 1 and a[-1] == 0:
        a.pop()
    return a

def sub(a, b):
    return trim([(a[i] if i < len(a) else 0) - (b[i] if i < len(b) else 0) for i in range(max(len(a), len(b)))])

def mul(a, b):
    c = [0] * (len(a) + len(b) - 1)
    for i, x in enumerate(a):
        for j, y in enumerate(b):
            c[i + j] += x * y
    return trim(c)

def divexact(a, b):
    a = a[:]
    q = [0] * max(1, len(a) - len(b) + 1)
    while len(a) >= len(b) and a != [0]:
        k = len(a) - len(b)
        v, r = divmod(a[-1], b[-1])
        assert r == 0, ('noninteger division', a, b)
        q[k] = v
        for i, x in enumerate(b):
            a[k + i] -= v * x
        trim(a)
    assert a == [0], ('nonexact division', a, b)
    return trim(q)

def det(A):
    n = len(A)
    if n == 0:
        return [1]
    B = [[v[:] for v in row] for row in A]
    prev = [1]
    for k in range(n - 1):
        pivot = B[k][k]
        assert pivot != [0]
        for i in range(k + 1, n):
            for j in range(k + 1, n):
                B[i][j] = divexact(sub(mul(pivot, B[i][j]), mul(B[i][k], B[k][j])), prev)
        prev = pivot
    return B[-1][-1]

def M(r):
    return [2 * math.factorial(r + 1) * (-1) ** j // math.factorial(2 * j + 1) for j in range(r // 2 + 1)]

def C(k):
    return math.prod((math.factorial(j) ** 2 for j in range(k)))

def expected(n):
    k = n // 2
    d = n * n // 4
    a = 4 ** (k * k) * C(k) ** 2 if n % 2 == 0 else 2 * 4 ** (k * (k + 1)) * C(k) * C(k + 1)
    T = 2 * k * k if n % 2 == 0 else 3 * k * k + 5 * k + 2
    e = 2 * k * (k + 1) if n % 2 == 0 else k * (k + 1)
    return (d, (-1) ** d * a, T, e)

PUBLISHED = {2: ([1, -13, 6], 1), 3: ([1, -7, 12, -360], 1), 4: ([1, -14, 165, -1224, 216], 1), 5: ([1, -133, 1929, -5940, -4320, -64800], 1), 6: ([1, -77, 1101, -4932, 17361, -113400, 9720], 1), 8: ([2, -78, 1089, -70785, 1578285, -11659950, 21402225, 22963500, 76545000], 2), 9: ([1, -54, 2286, -105966, 1927125, -13601520, 31122225, -30362850, 273375000, -13122000], 1), 11: ([2, -829, 58275, -1433430, 13530150, -117734175, 3083335875, -41419987875, 211076026875, -264998790000, -273265650000, -385786800000], 2), 12: ([1, -252, 16437, -425835, 6134265, -120820950, 2458605150, -26341594875, 124060399875, -176784778125, -8439086250, -699238575000, 20667150000], 1), 15: ([1, -126, 6654, -749439, 71087220, -3142068435, 67831410825, -727590460275, 3449814897375, -12254173249500, 266877060778125, -2987052554075625, 12107364149475000, -11246939027100000, -10207918728000000, -7655939046000000], 1), 16: ([1, -152, 15804, -2021700, 157758030, -6308511300, 132164631450, -1493816296500, 10920101842125, -117706861125000, 1646298202263750, -13233804005362500, 47682964163165625, -47494695181500000, -22188045568500000, -93572588340000000, 1822842630000000], 1)}

TABLE_1 = [[1, 0, 2, 2, 0], [2, 1, -4, 2, 4], [3, 2, 32, 10, 2], [4, 4, 256, 8, 12], [5, 6, 32768, 24, 6], [6, 9, -4194304, 18, 24], [7, 12, 19327352832, 44, 12], [8, 16, 89060441849856, 32, 40], [9, 20, 26264993026824732672, 70, 20], [10, 25, -7745861623526935561764864, 50, 60]]

def verify(output_dir):
    output_dir.mkdir(parents=True, exist_ok=True)
    raw = {0: ([1], [0])}
    family = {0: [Fraction(1)]}
    rows = []
    for n in range(1, 11):
        hankel = det([[M(a+b) for b in range(n)] for a in range(n)])
        bordered = det([[M(a+b) for b in list(range(n-1))+[n]] for a in range(n)])
        degree, leading, theta, e = expected(n)
        assert len(hankel)-1 == degree and hankel[-1] == leading
        assert len(bordered)-1 == degree and bordered[-1] == theta*leading
        assert bordered[0] == n*(n+1)*hankel[0]
        assert hankel[0] == 2**n*math.prod(math.factorial(k)*math.factorial(k+1) for k in range(1,n))
        numerator = sub([n*(n+1)*v for v in hankel], bordered)
        assert numerator[0] == 0
        assert n == 1 or (len(numerator)-1 == degree and numerator[-1] == e*leading)
        assert [n,degree,leading,theta,e] == TABLE_1[n-1]
        raw[n] = (hankel, bordered)
        family[degree] = [Fraction(v,leading) for v in hankel]
        if n >= 4:
            family[degree-1] = [Fraction(v,e*leading) for v in numerator[1:]]
        rows.append({'n':n,'degree':degree,'lambda':leading,'theta':theta,'e':e,'table_row_matches':True,'constant_identity_matches':True,'K_divisible_by_z':True})
    matches = {}
    for j, (descending, scale) in PUBLISHED.items():
        expected_coefficients = [Fraction(v,scale) for v in reversed(descending)]
        assert family[j] == expected_coefficients
        matches[str(j)] = {'all_coefficients_equal':True,'coefficient_count':len(expected_coefficients)}
    assert sub([6*v for v in raw[2][0]],raw[2][1]) == [0,-16]
    f3 = [Fraction(v,expected(3)[1]*expected(3)[3]) for v in sub([12*v for v in raw[3][0]],raw[3][1])[1:]]
    assert f3 == [Fraction(-24),Fraction(1)]
    assert family[1] == [Fraction(-2),Fraction(1)]
    lambda_n = {0:1, **{n:expected(n)[1] for n in range(1,11)}}
    for k in range(1,5):
        assert Fraction(lambda_n[2*k+1]*lambda_n[2*k-1],lambda_n[2*k]**2) == 4*k*k
    for k in range(5):
        assert Fraction(lambda_n[2*k+2]*lambda_n[2*k],lambda_n[2*k+1]**2) == -1
    result = {'author':'Knowledge Sense','arithmetic':'integer polynomial Bareiss elimination with exact division; Fraction normalization','determinant_sizes':list(range(1,11)),'rows':rows,'table_entries_matched':50,'appendix_C4':matches,'appendix_polynomials_matched':len(matches),'appendix_coefficients_matched':sum(v['coefficient_count'] for v in matches.values()),'G1':[str(v) for v in family[1]],'F2':['1'],'F3':[str(v) for v in f3],'normalizing_constant_ratios_match':True,'all_checks_passed':True}
    polynomials = {'author':'Knowledge Sense','coefficient_order':'constant term to highest degree','number_format':'exact rational strings','polynomials':{str(j):[str(v) for v in a] for j,a in sorted(family.items())}}
    (output_dir/'verification-results.json').write_text(json.dumps(result,indent=2)+'\n',encoding='utf-8')
    (output_dir/'constructed-polynomials.json').write_text(json.dumps(polynomials,indent=2)+'\n',encoding='utf-8')
    print(json.dumps({'all_checks_passed':True,'table_entries_matched':50,'appendix_polynomials_matched':11,'appendix_coefficients_matched':102},indent=2))


if __name__ == '__main__':
    parser = argparse.ArgumentParser(description='Reproduce the exact finite checks in the accompanying paper.')
    parser.add_argument('--output-dir',type=Path,default=Path(__file__).resolve().parent,help='Directory for the two JSON result files; defaults to this script directory.')
    verify(parser.parse_args().output_dir)
