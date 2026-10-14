"""Exact rational checks for the logarithmic circle heat-kernel paper.

Author: Knowledge Sense
Run with Python 3 and its standard library. Writes verification.json beside
this script. Finite checks supplement the proofs in the accompanying paper.
"""

from fractions import Fraction as F
from math import comb, factorial
from pathlib import Path
import json


def require(condition, message):
    if not condition:
        raise ArithmeticError(message)


def bernoulli(nmax):
    values = [F(1)]
    for n in range(1, nmax + 1):
        values.append(-sum(F(comb(n + 1, k)) * values[k]
                           for k in range(n)) / (n + 1))
    return values


def v2_int(n):
    n = abs(n)
    if n == 0:
        raise ValueError("The valuation of zero is not used here.")
    return (n & -n).bit_length() - 1


def v2(value):
    return v2_int(value.numerator) - v2_int(value.denominator)


def coefficients(t, sequence, order):
    # Differentiate exp(-t * sum(sequence[k] * z**k)).
    t = F(t)
    values = [F(1)]
    for n in range(1, order + 1):
        values.append(-t / n * sum(k * sequence[k] * values[n - k]
                                   for k in range(1, n + 1)))
    return values


def partition_vectors(total, maxpart):
    if maxpart == 0:
        if total == 0:
            yield ()
        return
    for count in range(total // maxpart + 1):
        for tail in partition_vectors(total - count * maxpart, maxpart - 1):
            yield tail + (count,)


def bernoulli_polynomial(n, u, numbers):
    u = F(u)
    return sum(F(comb(n, k)) * numbers[k] * u ** (n - k)
               for k in range(n + 1))


def g_coefficients(q, s, order, numbers):
    # Differentiate exp(q * sum((-1)**(k+1) * B_k(s) * y**k / k)).
    q = F(q)
    b = [bernoulli_polynomial(k, s, numbers) for k in range(order + 1)]
    values = [F(1)]
    for n in range(1, order + 1):
        values.append(q / n * sum((-1) ** (k + 1) * b[k] * values[n - k]
                                  for k in range(1, n + 1)))
    return values


def main():
    numbers = bernoulli(100)
    require(numbers[1:5] == [F(-1, 2), F(1, 6), F(0), F(-1, 30)],
            "Bernoulli-number convention differs from the paper.")
    s1 = [F(0)] + [(1 - F(2) ** (1 - k)) * 2 * numbers[k] / k
                    for k in range(1, 101)]
    rows = []
    for m in range(1, 51):
        pm = coefficients(F(1, 2) - m, s1, 2 * m)[2 * m]
        expected = -3 * m - v2_int(factorial(m))
        scaled = pm * 8 ** m * factorial(m)
        require(pm != 0 and v2(pm) == expected, f"Valuation failed at m={m}.")
        require(scaled.numerator % 2 and scaled.denominator % 2,
                f"Normalized coefficient failed at m={m}.")
        rows.append({"m": m, "P_m": str(pm), "Q_m": str(scaled),
                     "v2_P_m": v2(pm), "expected_v2": expected})
    expected_first = [F(1, 24), F(-9, 640), F(7625, 580608),
                      F(-4311167, 199065600), F(27527769, 504627200)]
    require([F(row["P_m"]) for row in rows[:5]] == expected_first,
            "The first five coefficients differ from the paper's table.")

    patterns = 0
    for m in range(1, 16):
        alpha = F(2 * m - 1, 2)
        singleton = (alpha * s1[2]) ** m / factorial(m)
        for counts in partition_vectors(m, m):
            term, denominator = F(1), 1
            for r, count in enumerate(counts, 1):
                term *= (alpha * s1[2 * r]) ** count / factorial(count)
                denominator *= r ** count * factorial(count)
            cycle_count = F(factorial(m), denominator)
            require(cycle_count.denominator == 1, "Cycle count is not integral.")
            gap = v2(term) - v2(singleton)
            require(gap == m - sum(counts) + v2(cycle_count),
                    "Partition valuation formula failed.")
            require(gap == 0 if counts[0] == m else gap >= 1,
                    "The singleton term is not the unique minimum.")
            patterns += 1

    shifts = [F(-7, 4), F(0), F(1, 3), F(1, 2), F(1)]
    identity_rows, reflected_coefficients = [], 0
    for m in range(1, 13):
        q = 2 * m - 1
        pm = F(rows[m - 1]["P_m"])
        for u in shifts:
            s2 = [F(0)] + [-bernoulli_polynomial(k, u, numbers) / k
                           for k in range(1, 2 * m + 2)]
            values = coefficients(-q, s2, 2 * m + 1)
            expected = (u - F(1, 2)) * pm
            require(values[2 * m] == pm and values[2 * m + 1] == expected,
                    f"Equation (5.4) failed at m={m}, u={u}.")
            reflected = g_coefficients(q, 1 - u, 2 * m + 1, numbers)
            require(values == reflected, "The reflected G identity failed.")
            reflected_coefficients += len(values)
            identity_rows.append({"m": m, "u": str(u),
                                  "odd_coefficient": str(expected),
                                  "even_predecessor": str(pm)})
    result = {
        "description": "Exact rational finite checks supplementary to the manuscript proofs.",
        "all_passed": True,
        "main_theorem_m_range": [1, 50],
        "partition_m_range": [1, 15],
        "partitions_checked": patterns,
        "equation_5_4_m_range": [1, 12],
        "equation_5_4_u_values": [str(u) for u in shifts],
        "equation_5_4_cases": len(identity_rows),
        "reflected_G_coefficients_checked": reflected_coefficients,
        "main_theorem_values": rows,
        "equation_5_4_values": identity_rows,
    }
    output = Path(__file__).with_name("verification.json")
    output.write_text(json.dumps(result, ensure_ascii=False, indent=2) + "\n",
                      encoding="utf-8")
    print(json.dumps({key: value for key, value in result.items()
                      if not key.endswith("_values")}, ensure_ascii=False, indent=2))


if __name__ == "__main__":
    main()
