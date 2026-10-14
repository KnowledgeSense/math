"""Exact rank polynomials of unions of divisor boxes by disjoint coordinate slices.

No inclusion-exclusion or family formula is
used to generate a Hilbert function. Counts use arbitrary-precision integers.
"""
from pathlib import Path
from functools import lru_cache
from itertools import product
from collections import Counter
from math import comb
import json

OUT = Path(__file__).resolve().parent

def maximal_boxes(boxes):
    unique = sorted(set(tuple(b) for b in boxes))
    return tuple(b for b in unique if not any(b != c and all(x <= y for x, y in zip(b, c)) for c in unique))

@lru_cache(None)
def sliced_union(boxes):
    if not boxes:
        return ()
    if not boxes[0]:
        return (1,)
    # On each interval the same boxes contain the first coordinate.
    ends = sorted({0} | {b[0] + 1 for b in boxes})
    result = [0] * (max(map(sum, boxes)) + 1)
    for lo, hi in zip(ends, ends[1:]):
        remaining = maximal_boxes(b[1:] for b in boxes if b[0] >= lo)
        tail = sliced_union(remaining)
        for x in range(lo, hi):
            for d, count in enumerate(tail):
                result[x + d] += count
    return tuple(result)

def ranks(generators):
    return sliced_union(maximal_boxes(generators))

def structure(gens, r, t, e):
    assert len(gens) == len(set(gens)) == t
    assert all(len(g) == r and min(g) >= 0 and sum(g) == e for g in gens)
    assert all(any(g[c] > 0 for g in gens) for c in range(r))
    assert len(maximal_boxes(gens)) == t
    h = ranks(gens)
    assert len(h) == e + 1 and h[0] == 1 and h[1] == r and h[-1] == t
    return h

def q(j):
    return comb(j + 2, 2)

def centered_defect(h, i):
    return h[i] ** 2 - h[i - 1] * h[i + 1]

def main():
    witness = ((10, 10, 56), (15, 15, 46), (27, 27, 22))
    h = structure(witness, 3, 3, 76)
    ambient = Counter()
    points = set()
    for v in product(range(28), range(28), range(57)):
        if any(all(x <= a for x, a in zip(v, g)) for g in witness):
            ambient[sum(v)] += 1
            points.add(v)
    assert tuple(ambient[i] for i in range(77)) == h
    for v in points:
        for c in range(3):
            if v[c]:
                predecessor = list(v)
                predecessor[c] -= 1
                assert tuple(predecessor) in points
    maxima = []
    for v in points:
        successors = []
        for c in range(3):
            successor = list(v)
            successor[c] += 1
            successors.append(tuple(successor))
        if not any(v1 in points for v1 in successors):
            maxima.append(v)
    assert set(maxima) == set(witness)
    negative = [{'degree': i, 'defect': centered_defect(h, i)} for i in range(1, 76) if centered_defect(h, i) < 0]
    assert negative == [{'degree': 55, 'defect': -3}]
    assert h[54:57] == (532, 509, 487) and sum(h) == 25386
    peak = max(h)
    peak_indices = [i for i, x in enumerate(h) if x == peak]
    assert all(h[i] <= h[i + 1] for i in range(peak_indices[0]))
    assert all(h[i] >= h[i + 1] for i in range(peak_indices[-1], 76))
    controls = []
    for k in (5, 6, 9, 20, 51):
        for shift in (0, 1, 37, 113):
            e = 14 * k + 6 + shift
            gens = ((2*k, 2*k, 10*k+6+shift), (3*k, 3*k, 8*k+6+shift), (5*k+2, 5*k+2, 4*k+2+shift))
            v = structure(gens, 3, 3, e)
            i = e - 4*k - 1
            target = tuple(q(j) + (3*k+1)**2 for j in (4*k+2, 4*k+1, 4*k))
            assert v[i-1:i+2] == target
            assert centered_defect(v, i) == -k*k + 4*k + 2 < 0
            controls.append({'family': 'three_variables_type_three', 'k': k, 'L': shift, 'e': e, 'triple': target, 'defect': centered_defect(v, i)})
    for t in (4, 5, 6, 11, 33, 70):
        for shift in (0, 1, 29):
            e = t + 20 + shift
            gens = ((4, 4, e-8), (1, e-2, 1), (1, 1, e-2)) + tuple((e-p-1, p, 1) for p in range(1, t-2))
            v = structure(gens, 3, t, e)
            i = e - 3
            target = tuple(q(j) + 2*t + 4 for j in (4, 3, 2))
            assert v[i-1:i+2] == target and centered_defect(v, i) == 6 - 2*t < 0
            controls.append({'family': 'three_variable_string', 't': t, 'e': e, 'triple': target, 'defect': centered_defect(v, i)})
    for r in (4, 5, 6, 10, 16):
        for t in (2, 3, 5, 13, 51):
            for shift in (0, 17):
                e = t + 4*r + 50 + shift
                gens = ((r+10, r+10, e-2*r-20) + (0,)*(r-3),) + tuple((e-r-8-p, 4+p, 4, 4) + (1,)*(r-4) for p in range(t-1))
                v = structure(gens, r, t, e)
                i = e - r - 9
                constant = 25 * (t+3) * 2**(r-4)
                target = tuple(q(j) + constant for j in (r+10, r+9, r+8))
                assert v[i-1:i+2] == target and centered_defect(v, i) == comb(r+11, 2) - constant < 0
                controls.append({'family': 'higher_codimension_string', 'r': r, 't': t, 'e': e, 'triple': target, 'defect': centered_defect(v, i)})
    # Exact bounded controls for the cited positive two-generator case.
    pair_count = 0
    from itertools import combinations
    for e in range(1, 13):
        monomials = [(a, b, e-a-b) for a in range(e+1) for b in range(e-a+1)]
        for gens in combinations(monomials, 2):
            if not all(any(g[c] > 0 for g in gens) for c in range(3)):
                continue
            v = structure(gens, 3, 2, e)
            assert all(centered_defect(v, i) >= 0 for i in range(1, e))
            pair_count += 1
    result = {
        'status': 'PASS',
        'method': 'Disjoint coordinate intervals and recursively computed tail-union rank polynomials; separate direct ambient membership count for the witness. No inclusion-exclusion or family count formula is used to generate ranks.',
        'witness': {'generators': witness, 'rank_vector': h, 'union_size': len(points), 'maxima': sorted(maxima), 'negative_defects': negative, 'peak_degrees': peak_indices, 'peak_value': peak},
        'negative_family_controls': {'count': len(controls), 'by_family': dict(Counter(v['family'] for v in controls)), 'cases': controls},
        'positive_two_generator_controls': {'socle_degrees': [1, 12], 'exact_codimension_three_pair_count': pair_count},
        'scope': 'Finite exact checks supplement the all-parameter proof in the accompanying manuscript.'
    }
    (OUT / 'recomputed_certificate.json').write_text(json.dumps(result, ensure_ascii=False, indent=2), encoding='utf-8')
    print(json.dumps({k: v for k, v in result.items() if k not in ('negative_family_controls', 'witness')}, ensure_ascii=False, indent=2))
    print(json.dumps({'witness_triple': h[54:57], 'defect': centered_defect(h, 55), 'negative_family_controls': len(controls), 'peak': [peak_indices, peak]}, indent=2))

if __name__ == '__main__':
    main()
