"""Exact finite checks for prime-field maximum-degree local permutation polynomials.

Two different models are used:
1. Formal polynomial arithmetic in F_p[U]/(U^q-U) for the recurrence.
2. Polynomial-basis finite fields and power-sum interpolation for switching.
All arithmetic is exact; only the Python standard library is used.
"""
import json
from functools import lru_cache
from pathlib import Path


def function_product(a, b, p, q):
    out = [0] * q
    for i, x in enumerate(a):
        if x:
            for j, y in enumerate(b):
                if y:
                    d = i + j
                    if d >= q:
                        d = 1 + (d - 1) % (q - 1)
                    out[d] = (out[d] + x * y) % p
    return out


def recurrence_algebra(p, r, last_n):
    q = p**r
    t = [1] * (q - 1) + [0]
    t[1] = 2 % p
    powers = [[1] + [0] * (q - 1)]
    for _ in range(q - 1):
        powers.append(function_product(powers[-1], t, p, q))
    # Verify the transposition polynomial is an involution in the quotient.
    t_of_t = [sum(t[j] * powers[j][i] for j in range(q)) % p for i in range(q)]
    assert t_of_t == [0, 1] + [0] * (q - 2)
    h = [0, 1] + [0] * (q - 2)
    states = [h.copy()]
    for _ in range(1, last_n):
        # Compute composition by ordinary powers, reduce, then differentiate.
        k = [sum(h[j] * powers[j][i] for j in range(q)) % p for i in range(q)]
        dh = [(j * k[j]) % p for j in range(1, q)]
        out = [0] * q
        for exponent, c in enumerate(dh):
            reduced = 0 if exponent == 0 else 1 + (exponent * (q - 2) - 1) % (q - 1)
            out[reduced] = (out[reduced] + c) % p
        h = out
        states.append(h.copy())
    if p == 3:
        a = [2, 0] + [(-j) % 3 for j in range(2, q - 1)] + [0]
        b = [0, 0] + [(-j * j) % 3 for j in range(2, q - 1)] + [0]
        assert all(v == (a if n % 2 == 0 else b) for n, v in enumerate(states[1:], 2))
    return {"p": p, "r": r, "q": q, "last_n": last_n,
            "coefficients": [h[q - 2] for h in states],
            "last_state": states[-1], "passed": True}


class FiniteField:
    def __init__(self, p, modulus):
        self.p, self.modulus = p, modulus
        self.r, self.q = len(modulus) - 1, p ** (len(modulus) - 1)
        self.digits = [tuple((a // p**i) % p for i in range(self.r)) for a in range(self.q)]
        self.inverses = [0] + [self.power(a, self.q - 2) for a in range(1, self.q)]
        assert all(self.multiply(a, self.inverses[a]) == 1 for a in range(1, self.q))
        assert all(self.power(a, self.q) == a for a in range(self.q))

    def encode(self, v):
        return sum((c % self.p) * self.p**i for i, c in enumerate(v))

    @lru_cache(None)
    def add(self, a, b):
        return self.encode([x + y for x, y in zip(self.digits[a], self.digits[b])])

    def negate(self, a):
        return self.encode([-c for c in self.digits[a]])

    @lru_cache(None)
    def multiply(self, a, b):
        c = [0] * (2 * self.r - 1)
        for i, x in enumerate(self.digits[a]):
            for j, y in enumerate(self.digits[b]):
                c[i + j] += x * y
        for d in range(2 * self.r - 2, self.r - 1, -1):
            leading = c[d] % self.p
            for j in range(self.r):
                c[d - self.r + j] -= leading * self.modulus[j]
        return self.encode(c[:self.r])

    def power(self, a, exponent):
        out = 1
        while exponent:
            if exponent % 2:
                out = self.multiply(out, a)
            a = self.multiply(a, a)
            exponent //= 2
        return out

    def total(self, values):
        out = 0
        for a in values:
            out = self.add(out, a)
        return out

    def orbit(self, a):
        result, current = [], a
        while current not in result:
            result.append(current)
            current = self.power(current, self.p)
        assert current == a
        return result

    def interpolate(self, values):
        # Power-sum transform: coefficient_j = -sum_a values[a]*a^(q-1-j), j>0.
        coeff = [0] * self.q
        coeff[0] = values[0]
        for a, value in enumerate(values):
            power = 1
            for j in range(self.q - 1, 0, -1):
                coeff[j] = self.add(coeff[j], self.negate(self.multiply(value, power)))
                power = self.multiply(power, a)
        assert all(self.evaluate(coeff, a) == values[a] for a in range(self.q))
        return coeff

    def evaluate(self, coeff, a):
        out = 0
        for c in reversed(coeff):
            out = self.add(self.multiply(out, a), c)
        return out


def switching_check(p, modulus):
    field = FiniteField(p, modulus)
    seen, full_orbits = set(), []
    for a in range(field.q):
        if a in seen:
            continue
        orbit = field.orbit(a)
        seen.update(orbit)
        if len(orbit) == field.r:
            full_orbits.append(orbit)
    oa = full_orbits[0]
    s = {field.add(a, c) for a in oa for c in range(p)}
    ob = next(o for o in full_orbits if set(o).isdisjoint(s) and field.total(o) != field.total(oa))
    h = list(range(field.q))
    for a, b in zip(oa, ob):
        h[a], h[b] = b, a
    support = (s - set(oa)) | set(ob)
    g = [int(a in support) for a in range(field.q)]
    assert len(s) == len(support) == p * field.r
    assert len(support) % p == 0 and field.total(support) != 0
    assert {field.add(a, 1) for a in s} == s
    assert {h[a] for a in support} == s
    assert all(h[field.power(a, p)] == field.power(h[a], p) for a in range(field.q))
    assert all(g[field.power(a, p)] == g[a] for a in range(field.q))
    hc, gc = field.interpolate(h), field.interpolate(g)
    assert all(c < p for c in hc + gc)
    assert hc[-1] == gc[-1] == 0
    assert gc[-2] == field.negate(field.total(support)) != 0
    assert len(set(h)) == field.q
    assert len({field.add(h[a], g[a]) for a in range(field.q)}) == field.q
    for fixed in range(field.q):
        row = [field.add(field.add(h[a], h[fixed]), g[a] * g[fixed]) for a in range(field.q)]
        assert len(set(row)) == field.q
    return {"p": p, "r": field.r, "q": field.q, "modulus": modulus,
            "orbit_alpha": oa, "orbit_beta": ob, "S": sorted(s), "T": sorted(support),
            "sum_T": field.total(support), "h_coefficients": hc, "g_coefficients": gc,
            "all_binary_slices": 2 * field.q, "passed": True}


def weighted_prime(p, last_n):
    # Exact combinatorial aggregation of all input tuples, without polynomial reduction.
    inverse = [0] + [pow(x, -1, p) for x in range(1, p)]
    def swap(a):
        return 1 if a == 0 else 0 if a == 1 else a
    weights, coeff = list(range(p)), [0]
    for n in range(2, last_n + 1):
        updated_weights = [0] * p
        for y, w in enumerate(weights):
            for x in range(p):
                z = swap((inverse[y] + inverse[x]) % p)
                updated_weights[z] = (updated_weights[z] + w * x) % p
        weights = updated_weights
        coeff.append(((-1)**n * sum(z * weights[z] for z in range(p))) % p)
    return {"q": p, "last_n": last_n, "coefficients": coeff, "weights": weights}


def main():
    result = {"method": "quotient-ring composition and power-sum interpolation",
              "recurrences": [], "orbit_switching": [], "weighted_counterexamples": []}
    for p, r, n in [(7, 1, 10), (19, 1, 8), (3, 2, 20), (3, 3, 20), (3, 4, 20), (3, 5, 20)]:
        row = recurrence_algebra(p, r, n)
        result["recurrences"].append(row)
        print("algebra", row["q"], row["coefficients"], flush=True)
    for p, modulus in [(5, [2, 0, 1]), (7, [1, 0, 1]), (11, [1, 0, 1]),
                       (5, [1, 1, 0, 1]), (3, [2, 0, 0, 1, 1])]:
        row = switching_check(p, modulus)
        result["orbit_switching"].append(row)
        print("switching", row["q"], "top indicator coefficient", row["g_coefficients"][-2], flush=True)
    for p, n in [(7, 10), (19, 8)]:
        row = weighted_prime(p, n)
        algebra = next(z for z in result["recurrences"] if z["q"] == p)
        assert row["coefficients"] == algebra["coefficients"]
        assert row["coefficients"][-1] == 0
        result["weighted_counterexamples"].append(row)
        print("counterexample", p, n, row["weights"], flush=True)
    result["passed"] = True
    Path(__file__).with_name("certificates.json").write_text(json.dumps(result, indent=2), encoding="utf-8")
    print("All checks passed.", flush=True)


if __name__ == "__main__":
    main()
