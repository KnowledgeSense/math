"""Finite coefficient checks for power-related matrix weights.

Author: Knowledge Sense
Contact: math@knowledgesense.jp

Uses only the Python standard library. See README.md for the mathematical
meaning and the distinction between these checks and the general theorem.
"""
import argparse
import json
from pathlib import Path

PRIME = 1000003


def modular_rank(rows):
    """Exact sparse Gaussian elimination over the field with PRIME elements."""
    basis = {}
    for row in rows:
        row = {k: v % PRIME for k, v in row.items() if v % PRIME}
        while row:
            pivot = min(row)
            if pivot not in basis:
                inverse = pow(row[pivot], PRIME - 2, PRIME)
                basis[pivot] = {k: v * inverse % PRIME for k, v in row.items()}
                break
            factor = row[pivot]
            for k, v in basis[pivot].items():
                value = (row.get(k, 0) - factor * v) % PRIME
                if value:
                    row[k] = value
                else:
                    row.pop(k, None)
    return len(basis)


def coefficient_matrices(n, exponents, parameters):
    """Coefficients of P(x)=(I+xA)diag(x**s)(I+xA.T)."""
    a = [[0] * n for _ in range(n)]
    for j, value in enumerate(parameters):
        if j % 2 == 0:
            a[j][j + 1] = value
        else:
            a[j + 1][j] = value
    coefficients = {}

    def add(degree, i, j, value):
        if value:
            matrix = coefficients.setdefault(degree, [[0] * n for _ in range(n)])
            matrix[i][j] += value

    for k in range(n):
        add(exponents[k], k, k, 1)
        for i in range(n):
            add(exponents[k] + 1, i, k, a[i][k])
            add(exponents[k] + 1, k, i, a[i][k])
            for j in range(n):
                add(exponents[k] + 2, i, j, a[i][k] * a[j][k])
    return coefficients


def equation_rows(n, coefficients, sign):
    """Rows for XP + sign*PX.T=0, with n*n unknown entries of X."""
    for degree in sorted(coefficients):
        matrix = coefficients[degree]
        for i in range(n):
            for j in range(n):
                row = {}
                for k in range(n):
                    if matrix[k][j]:
                        index = i * n + k
                        row[index] = row.get(index, 0) + matrix[k][j]
                    if matrix[i][k]:
                        index = j * n + k
                        row[index] = row.get(index, 0) + sign * matrix[i][k]
                yield row


def check(n, exponents, parameters):
    coefficients = coefficient_matrices(n, exponents, parameters)
    real_rows = list(equation_rows(n, coefficients, -1))
    # Exact verification of the real identity solution supplies the upper
    # bound n*n-1 on rational rank; a modular nonzero minor supplies the lower.
    diagonal_indices = {i * n + i for i in range(n)}
    if any(sum(value for k, value in row.items() if k in diagonal_indices)
           for row in real_rows):
        raise ArithmeticError("The real identity is not in the exact kernel")
    real_rank = modular_rank(real_rows)
    imaginary_rank = modular_rank(equation_rows(n, coefficients, 1))
    if real_rank != n * n - 1 or imaginary_rank != n * n:
        raise ArithmeticError(f"Unexpected rank for N={n}, exponents={exponents}, a={parameters}")
    return {
        "N": n,
        "a": parameters,
        "exponents": exponents,
        "real_rank_mod_prime": real_rank,
        "imaginary_rank_mod_prime": imaginary_rank,
        "real_solution_dimension": 1,
        "imaginary_solution_dimension": 0,
    }


def run_checks():
    if any(PRIME % d == 0 for d in range(2, 1001)):
        raise ArithmeticError("The modulus must be prime")
    records = []
    for n in range(1, 11):
        lists = [("L", [0] + [max(0, j - 1) for j in range(1, n)]),
                 ("E", list(range(n)))]
        cases = [("ones", [1] * (n - 1)),
                 ("signed_integers", [(-1) ** j * (j + 2) for j in range(n - 1)])]
        for name, exponents in lists:
            for case_name, parameters in cases:
                record = check(n, exponents, parameters)
                record.update({"list": name, "parameter_case": case_name})
                records.append(record)
    return {
        "author": "Knowledge Sense",
        "contact": "math@knowledgesense.jp",
        "method": "Exact coefficient equations for FP=PF*, F=R+iQ; modular rank certificate",
        "prime": PRIME,
        "size_range": [1, 10],
        "cases": len(records),
        "all_passed": True,
        "scope": "Finite selected integer parameter cases; the uniform theorem is proved in the manuscript.",
        "records": records,
    }


def main():
    parser = argparse.ArgumentParser(description=__doc__.splitlines()[0])
    parser.add_argument("--output", type=Path, default=Path("verification-results.json"))
    args = parser.parse_args()
    result = run_checks()
    args.output.write_text(json.dumps(result, ensure_ascii=False, indent=2) + "\n", encoding="utf-8")
    print(f"Passed {result['cases']} cases. Results: {args.output}")


if __name__ == "__main__":
    main()
