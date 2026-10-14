"""Exact enumeration of preorder support polynomials and matching coefficients.

All arithmetic is integral; only the Python standard library is required.
"""
from functools import lru_cache
from itertools import combinations
from math import comb
from pathlib import Path
import json
import random
import time


def vectors(length, budget):
    if length == 0:
        yield ()
        return
    for a in range(budget + 1):
        for rest in vectors(length - 1, budget - a):
            yield (a,) + rest


@lru_cache(None)
def literal_point_tests(n):
    tests = []
    for x in vectors(n, n):
        sums = [0] * (1 << n)
        invalid_ideals = 0
        for mask in range(1, 1 << n):
            low = mask & -mask
            sums[mask] = sums[mask ^ low] + x[low.bit_length() - 1]
            if sums[mask] > mask.bit_count():
                invalid_ideals |= 1 << mask
        tests.append((invalid_ideals, sum(v > 0 for v in x)))
    assert len(tests) == comb(2 * n, n)
    return tests


def ideal_mask(rows):
    n = len(rows)
    predecessors = [sum(1 << i for i in range(n) if rows[i] >> j & 1)
                    for j in range(n)]
    ideal_indices = 0
    for mask in range(1 << n):
        if all(not (mask >> j & 1) or predecessors[j] & ~mask == 0
               for j in range(n)):
            ideal_indices |= 1 << mask
    return ideal_indices


def literal_h(rows):
    n = len(rows)
    ideal_indices = ideal_mask(rows)
    h = [0] * (n + 1)
    for invalid, support in literal_point_tests(n):
        if invalid & ideal_indices == 0:
            h[support] += 1
    return h


def matchable(left, right, rows):
    """Existence of an upward bijection; witnesses are never counted."""
    if left.bit_count() != right.bit_count():
        return False
    if not left:
        return True
    choices = [(rows[i] & right, i)
               for i in range(len(rows)) if left >> i & 1]
    targets, i = min(choices, key=lambda z: z[0].bit_count())
    while targets:
        target = targets & -targets
        targets ^= target
        if matchable(left ^ (1 << i), right ^ target, rows):
            return True
    return False


@lru_cache(None)
def disjoint_pairs(n):
    levels = []
    for j in range(n // 2 + 1):
        pairs = []
        for I in combinations(range(n), j):
            left = sum(1 << i for i in I)
            available = [i for i in range(n) if not (left >> i & 1)]
            for J in combinations(available, j):
                pairs.append((left, sum(1 << i for i in J)))
        levels.append(pairs)
    return levels


def matching_gamma(rows):
    return [sum(matchable(I, J, rows) for I, J in pairs)
            for pairs in disjoint_pairs(len(rows))]


def expand_gamma(b, n):
    result = [0] * (n + 1)
    for j, count in enumerate(b):
        for k in range(n - 2 * j + 1):
            result[j + k] += count * comb(n - 2 * j, k)
    return result


def extract_gamma(h):
    n = len(h) - 1
    assert h == h[::-1]
    residual = h.copy()
    b = []
    for j in range(n // 2 + 1):
        coefficient = residual[j]
        b.append(coefficient)
        for k in range(n - 2 * j + 1):
            residual[j + k] -= coefficient * comb(n - 2 * j, k)
    assert all(v == 0 for v in residual)
    return b


def all_preorders(n):
    row_options = []
    for i in range(n):
        others = [j for j in range(n) if j != i]
        row_options.append([1 << i | sum(1 << j for k, j in enumerate(others)
                                       if pattern >> k & 1)
                            for pattern in range(1 << max(0, n - 1))])
    width = max(0, n - 1)
    bits = (1 << width) - 1
    for code in range(1 << (n * width)):
        rows = tuple(row_options[i][code >> (i * width) & bits]
                     for i in range(n))
        if all(not (rows[i] >> j & 1) or rows[j] & ~rows[i] == 0
               for i in range(n) for j in range(n)):
            yield rows


def closure(rows):
    rows = list(rows)
    for k in range(len(rows)):
        for i in range(len(rows)):
            if rows[i] >> k & 1:
                rows[i] |= rows[k]
    return tuple(rows)


def verify_preorder(rows):
    h = literal_h(rows)
    b = matching_gamma(rows)
    assert h == expand_gamma(b, len(rows)), (rows, h, b)
    assert b == extract_gamma(h), (rows, h, b)
    dual = tuple(sum(1 << i for i in range(len(rows)) if rows[i] >> j & 1)
                 for j in range(len(rows)))
    assert b == matching_gamma(dual)
    return h, b


def bipartite_h(rows, right_size):
    left_size = len(rows)
    h = [0] * (max(left_size, right_size) + 1)
    neighbors = [0] * (1 << left_size)
    for mask in range(1, 1 << left_size):
        low = mask & -mask
        neighbors[mask] = neighbors[mask ^ low] | rows[low.bit_length() - 1]
    for x in vectors(left_size, right_size):
        if all(sum(x[i] for i in range(left_size) if mask >> i & 1)
               <= neighbors[mask].bit_count() for mask in range(1 << left_size)):
            h[sum(v > 0 for v in x)] += 1
    return h


def verify_bipartite():
    count = 0
    for p in range(4):
        for q in range(4):
            for code in range(1 << (p * q)):
                rows = tuple(code >> (i * q) & ((1 << q) - 1) for i in range(p))
                dual = tuple(sum(1 << i for i in range(p) if rows[i] >> j & 1)
                             for j in range(q))
                h = bipartite_h(rows, q)
                assert h == bipartite_h(dual, p)
                endpoints = 0
                for I in combinations(range(q), p):
                    mask = sum(1 << i for i in I)
                    extended_rows = rows + (0,) * max(0, q - p)
                    endpoints += matchable((1 << p) - 1, mask, extended_rows)
                assert h[p] == endpoints, (p, q, rows, h, endpoints)
                count += 1
    return count


def main():
    start = time.monotonic()
    results = {'status': 'PASS', 'seed': 10072026, 'exhaustive': []}
    expected = [1, 1, 4, 29, 355, 6942]
    for n in range(6):
        count = equivalent = points = 0
        for rows in all_preorders(n):
            h, b = verify_preorder(rows)
            count += 1
            points += sum(h)
            equivalent += any(rows[i] >> j & 1 and rows[j] >> i & 1
                              for i in range(n) for j in range(i))
        assert count == expected[n]
        entry = {'n': n, 'preorders': count, 'nontrivial_equivalence': equivalent,
                 'feasible_lattice_points': points}
        results['exhaustive'].append(entry)
        print(json.dumps(entry), flush=True)
    results['bipartite_graphs'] = verify_bipartite()
    rng = random.Random(results['seed'])
    random_count = 100
    for case in range(random_count):
        n = 6 + case % 3
        p = rng.uniform(0.04, 0.4)
        rows = tuple(1 << i | sum(1 << j for j in range(n)
                                 if i != j and (case % 2 or i < j)
                                 and rng.random() < p)
                     for i in range(n))
        verify_preorder(closure(rows))
    results['random_preorders_n6_to_n8'] = random_count
    # a1,a2,a3,d,b0,b1,b2,b3, with nine strict relations.
    example = tuple((1 << i) for i in range(8))
    example = list(example)
    for i in range(3):
        example[i] |= (1 << 4) | (1 << (5 + i))
        example[3] |= 1 << (5 + i)
    h, b = verify_preorder(tuple(example))
    results['eight_element_example'] = {'rows': example, 'h': h, 'gamma': b}
    results['seconds'] = round(time.monotonic() - start, 3)
    (Path(__file__).parent / 'certificate.json').write_text(
        json.dumps(results, ensure_ascii=False, indent=2), encoding='utf-8')
    print(json.dumps(results, ensure_ascii=False, indent=2), flush=True)


if __name__ == '__main__':
    main()
