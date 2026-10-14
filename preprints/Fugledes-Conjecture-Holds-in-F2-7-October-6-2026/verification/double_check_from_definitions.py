"""Finite-set and Hadamard checks from mathematical definitions.

The checks are implemented directly from the mathematical definitions.
Eight-point input sets are generated here without reading their certificates.
Small Hadamard row spaces are verified by enumerating their entire linear spans.
The Walsh integer equivalence is verified by exact integer matrix multiplication.
"""
import argparse
from collections import Counter
from functools import lru_cache
from itertools import combinations
import hashlib
import json
from math import comb
from pathlib import Path


def require(value, explanation):
    if not value:
        raise ArithmeticError(explanation)


def fourier(points, frequency):
    return sum((-1) ** ((point & frequency).bit_count() % 2) for point in points)


def cover_search(points, dimension):
    """Enumerate disjoint translates covering the first uncovered point.

    Translation of a complement lets us require shift 0 to be present.
    No search programs or supplied witnesses are used.
    """
    size = 1 << dimension
    complete = (1 << size) - 1
    covers = [sum(1 << (point ^ shift) for point in points) for shift in range(size)]

    @lru_cache(None)
    def finish(used):
        if used == complete:
            return ()
        uncovered = complete ^ used
        point = (uncovered & -uncovered).bit_length() - 1
        for tile_point in points:
            shift = point ^ tile_point
            mask = covers[shift]
            if mask & used:
                continue
            remaining = finish(used | mask)
            if remaining is not None:
                return (shift,) + remaining
        return None

    tail = finish(covers[0])
    return None if tail is None else (0,) + tail


def spectrum_search(points, dimension):
    """Exhaustive subset search with character 0 fixed by translation."""
    n = 1 << dimension
    values = [fourier(points, x) for x in range(n)]
    zeros = [x for x in range(1, n) if values[x] == 0]
    adjacency = [0] * n
    available = sum(1 << x for x in zeros)
    for a in zeros:
        adjacency[a] = sum(1 << b for b in zeros if a != b and values[a ^ b] == 0)

    @lru_cache(None)
    def choose(candidates, missing):
        if missing == 0:
            return ()
        while candidates.bit_count() >= missing:
            bit = candidates & -candidates
            vertex = bit.bit_length() - 1
            candidates ^= bit
            tail = choose(candidates & adjacency[vertex], missing - 1)
            if tail is not None:
                return (vertex,) + tail
        return None

    selected = choose(available, len(points) - 1)
    return None if selected is None else (0,) + selected


def check_cover(points, shifts, dimension):
    n = 1 << dimension
    require(len(points) == len(set(points)), "Point set has duplicates")
    require(len(shifts) == len(set(shifts)), "Complement has duplicates")
    require(all(type(x) is int and 0 <= x < n for x in points + list(shifts)), "Coordinates outside ambient group")
    counts = Counter(point ^ shift for point in points for shift in shifts)
    require(counts == Counter({x: 1 for x in range(n)}), "Tiling does not cover each point once")


def universal_slice(points, dimension):
    # Character evaluation embeds the dual of span(points) into F2^7.
    inverse = {sum((((a & t).bit_count() % 2) << i) for i, t in enumerate(points[1:])): a
               for a in range(1 << dimension)}
    require(len(inverse) == 1 << dimension, "Dual embedding is not injective")
    simplex = [0] + [1 << i for i in range(7)]
    antipodal = sorted(set(simplex + [127 ^ x for x in simplex]))
    require(len(antipodal) == 16, "Antipodal construction size")
    slices = [[inverse[x ^ anchor] for x in antipodal if (x ^ anchor) in inverse]
              for anchor in antipodal]
    selected = max(slices, key=len)[:1 << (dimension - 3)]
    require(len(selected) == 1 << (dimension - 3), "Coset slicing cardinality")
    require(all(fourier(points, a ^ b) != 0 for a, b in combinations(selected, 2)), "Nonvanishing construction failed")
    return selected


def all_eight_cases(output):
    counts = {}
    witnesses = []
    for dimension in range(3, 8):
        fixed = [0] + [1 << i for i in range(dimension)]
        extra_pool = [x for x in range(1 << dimension) if x not in fixed]
        tally = Counter()
        for extra in combinations(extra_pool, 7 - dimension):
            points = fixed + list(extra)
            complement = cover_search(points, dimension)
            spectrum = spectrum_search(points, dimension)
            require((complement is None) == (spectrum is None), "Eight-point Fuglede disagreement")
            if complement is not None:
                check_cover(points, complement, dimension)
                require(len(spectrum) == len(set(spectrum)) == 8, "Spectrum size")
                require(all(fourier(points, a ^ b) == 0 for a, b in combinations(spectrum, 2)), "Spectrum orthogonality")
                tally['tile_and_spectral'] += 1
            else:
                tally['neither_property'] += 1
            universal = universal_slice(points, dimension)
            tally['all_sets'] += 1
            witnesses.append(dict(dimension=dimension, points=points, complement=complement,
                                  spectrum=spectrum, nonvanishing=universal))
        counts[str(dimension)] = dict(tally)
    (output / 'fresh_eight_cases.json').write_text(json.dumps(witnesses, indent=2), encoding='utf-8')
    return counts


def kron(a, b):
    return [[a[i][j] * b[k][l] for j in range(len(a[0])) for l in range(len(b[0]))]
            for i in range(len(a)) for k in range(len(b))]


def multiply(a, b):
    # Python integers; no floating point or fixed-width arithmetic.
    result = []
    for row in a:
        total = [0] * len(b[0])
        for k, value in enumerate(row):
            if value:
                total = [x + value * y for x, y in zip(total, b[k])]
        result.append(total)
    return result


def walsh_smith_check():
    left = right = [[1]]
    for _ in range(7):
        left = kron(left, [[1, 0], [1, -1]])
        right = kron(right, [[1, -1], [0, 1]])
    # Both are triangular integer matrices with diagonal entries +/-1.
    require(all(left[i][j] == 0 for i in range(128) for j in range(i + 1, 128)), "Left integer transformation not triangular")
    require(all(right[i][j] == 0 for i in range(128) for j in range(i)), "Right integer transformation not triangular")
    require(all(abs(left[i][i]) == abs(right[i][i]) == 1 for i in range(128)), "Integer transformations not unimodular")
    walsh = [[(-1) ** ((i & j).bit_count() % 2) for j in range(128)] for i in range(128)]
    actual = multiply(multiply(left, walsh), right)
    require(all(actual[i][j] == ((1 << i.bit_count()) if i == j else 0)
                for i in range(128) for j in range(128)), "Exact Walsh diagonalization failed")
    exponents = sorted(i.bit_count() for i in range(128))
    require(Counter(exponents) == Counter({k: comb(7, k) for k in range(8)}), "Smith multiplicities")
    exclusions = []
    for m in range(4, 64, 4):
        if m.bit_count() == 1:
            continue
        odd, valuation = m, 0
        while odd % 2 == 0:
            valuation += 1
            odd //= 2
        determinant_valuation = (m // 2) * valuation
        minor_valuation = sum(exponents[:m])
        require(determinant_valuation < minor_valuation, "Non-power cardinality survives Smith bound")
        exclusions.append(dict(m=m, determinant_valuation=determinant_valuation, minor_valuation=minor_valuation))
    return dict(exact_integer_diagonalization=True, exclusions=exclusions)


def binary_span(rows):
    space = {0}
    basis = []
    for row in rows:
        if row not in space:
            space |= {x ^ row for x in space}
            basis.append(row)
    return space, basis


def normalized_rows(words, base_row=0, base_column=0):
    mask = (1 << len(words)) - 1
    differences = [word ^ words[base_row] for word in words]
    return [word ^ (mask if (word >> base_column) & 1 else 0) for word in differences]


def orientation(words, transposed):
    if not transposed:
        return words
    return [sum(((row >> column) & 1) << i for i, row in enumerate(words))
            for column in range(len(words))]


def check_matrix(words, certificate=None):
    order = len(words)
    require(all(0 <= x < 1 << order for x in words), "Invalid Hadamard row word")
    require(all((a ^ b).bit_count() == order // 2 for a, b in combinations(words, 2)), "Hadamard identity fails")
    logs = normalized_rows(words)
    span, basis = binary_span(logs)
    rank = len(basis)
    require(rank <= 7, "Unexpected high rank in small checks")
    if certificate is not None:
        require(certificate['r'] == rank, "Certificate rank differs")
        points = certificate['E']
        require(len(points) == len(set(points)) == order, "Certificate column count differs")
        require(all(type(x) is int and 0 <= x < 1 << rank for x in points), "Certificate column coordinates")
        coordinate_rows = [sum(((point >> i) & 1) << j for j, point in enumerate(points))
                           for i in range(rank)]
        other_span, _ = binary_span(coordinate_rows)
        require(span == other_span, "Supplied points not attached to source row space")
        check_cover(points, certificate['T'], rank)
    # Generate a new canonical point set and search a complement from scratch.
    fresh_points = [sum(((row >> j) & 1) << i for i, row in enumerate(basis)) for j in range(order)]
    fresh_complement = cover_search(fresh_points, rank)
    require(fresh_complement is not None, "Canonical set has no tiling complement")
    check_cover(fresh_points, fresh_complement, rank)
    # Every possible base row and column; not randomized trials.
    normalizations = 0
    for i in range(order):
        for j in range(order):
            other_logs = normalized_rows(words, i, j)
            other_span, _ = binary_span(other_logs)
            require(len(other_span) == 1 << rank, "Rank changed under normalization")
            normalizations += 1
    return dict(order=order, rank=rank, fresh_points=fresh_points,
                fresh_complement=fresh_complement, exhaustive_normalizations=normalizations)


def hadamard_checks(packet, scan_output):
    cert16 = json.loads((packet / 'spectral16_certificates.json').read_text())
    indexed16 = {d['index']: d for d in cert16}
    require(len(cert16) == 5 and set(indexed16) == set(range(5)), "Order-16 certificates not complete")
    results = []
    for index in range(5):
        text = (packet / f'had.16.{index}.txt').read_text()
        signs = [line.strip() for line in text.splitlines()
                 if len(line.strip()) == 16 and set(line.strip()) <= {'+', '-'}]
        require(len(signs) == 16, "Order-16 source matrix shape")
        words = [sum((character == '+') << j for j, character in enumerate(line)) for line in signs]
        for transposed in (False, True):
            results.append(dict(source_index=index, transposed=transposed,
                                **check_matrix(orientation(words, transposed), None if transposed else indexed16[index])))
    selected = {}
    for line in (scan_output / 'exact_rank_le7.txt').read_text().splitlines():
        items = line.split()
        index, declared_rank = map(int, items[:2])
        require(index not in selected and len(items) == 34, "Duplicate or malformed retained record")
        selected[index] = (declared_rank, [int(x, 16) for x in items[2:]])
    old_selected = {}
    for line in (packet / 'had32_rank_le7.txt').read_text().splitlines():
        items = line.split()
        old_selected[int(items[0])] = (int(items[1]), [int(x, 16) for x in items[2:]])
    require(selected == old_selected, "Fresh full-rank extraction differs from original")
    cert32 = json.loads((packet / 'spectral32_certificates.json').read_text())
    indexed32 = {(d['class_index'], d['transpose']): d for d in cert32}
    require(len(cert32) == len(indexed32) and set(indexed32) == {(i, tr) for i in selected for tr in (False, True)}, "Oriented certificates do not cover retained classes")
    for index, (declared_rank, words) in selected.items():
        for transposed in (False, True):
            outcome = check_matrix(orientation(words, transposed), indexed32[index, transposed])
            require(outcome['rank'] == declared_rank, "Full scanner rank and span enumeration disagree")
            results.append(dict(source_index=index, transposed=transposed, **outcome))
    return results


def main():
    parser = argparse.ArgumentParser()
    parser.add_argument('--packet', type=Path, required=True)
    parser.add_argument('--output', type=Path, required=True)
    args = parser.parse_args()
    args.output.mkdir(parents=True, exist_ok=True)
    report = {}
    report['walsh_smith'] = walsh_smith_check()
    print('PASS: exact 128x128 integer Walsh diagonalization and non-power exclusions', flush=True)
    report['eight'] = all_eight_cases(args.output)
    print('PASS: fresh exhaustive eight-point tiling, spectral, and universal-slice decisions', report['eight'], flush=True)
    report['hadamard'] = hadamard_checks(args.packet, args.output)
    report['normalizations'] = sum(x['exhaustive_normalizations'] for x in report['hadamard'])
    report['full_scan'] = json.loads((args.output / 'exact_scan_results.json').read_text(encoding='utf-8-sig'))
    require(report['full_scan']['records'] == 6857010 and report['full_scan']['retained'] == 16, 'Unexpected complete source coverage')
    report['status'] = 'passed'
    report['supplied_verifier_imports'] = False
    (args.output / 'double_check_results.json').write_text(json.dumps(report, indent=2), encoding='utf-8')
    print('PASS: small matrices and all supplied positive certificates; newly generated tilings;'
          f' {report["normalizations"]} exhaustive normalization choices', flush=True)
    print('PASS: full source scan retained records and exact ranks agree; double check complete', flush=True)


if __name__ == '__main__':
    main()
