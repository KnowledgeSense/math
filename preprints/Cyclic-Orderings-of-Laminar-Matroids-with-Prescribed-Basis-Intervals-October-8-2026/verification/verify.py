"""Finite checks for the laminar padded-row construction; standard library only."""
from __future__ import annotations

import argparse
import itertools as it
import json
import math
import random
import time
from collections import Counter
from dataclasses import dataclass
from pathlib import Path


COUNTS = Counter()


def bits(mask):
    while mask:
        low = mask & -mask
        yield low.bit_length() - 1
        mask ^= low


def mask_of(elements):
    return sum(1 << e for e in elements)


def laminar(family):
    for (a, _), (b, _) in it.combinations(family, 2):
        overlap = a & b
        if overlap and overlap != a and overlap != b:
            return False
    return True


def independent(mask, family):
    # Deliberately no calls to the capacity tree or recursive construction.
    return all((mask & subset).bit_count() <= capacity
               for subset, capacity in family)


def exact_rank(n, family):
    return max((m.bit_count() for m in range(1 << n)
                if independent(m, family)), default=0)


def greedy_rank(n, family):
    chosen = 0
    for e in range(n):
        candidate = chosen | (1 << e)
        if independent(candidate, family):
            chosen = candidate
    return chosen.bit_count()


@dataclass(frozen=True)
class Node:
    ground: int
    capacity: int
    children: tuple


def tree_from_subsets(n, family, root_capacity):
    # Empty-set inequalities are vacuous for nonnegative capacities.
    constraints = {s: c for s, c in family if s}
    full = (1 << n) - 1
    constraints[full] = root_capacity

    def make(subset):
        proper = [s for s in constraints if s and s != subset
                  and s & subset == s]
        maximal = [s for s in proper if not any(
            s != t and s & t == s for t in proper)]
        maximal.sort()
        children = [make(s) for s in maximal]
        covered = 0
        for child in maximal:
            covered |= child
        remainder = subset & ~covered
        if children and remainder:
            children.append(Node(remainder, remainder.bit_count(), ()))
        return Node(subset, constraints[subset], tuple(children))

    return make(full)


def future_lifetime(support, row, k):
    if len(support) == k:
        return k  # Larger than every finite lifetime; representation of infinity.
    duration = 0
    for step in range(1, k):
        if (row + step) % k not in support:
            break
        duration += 1
    return duration


def construct(node, rows):
    # Only real elements returned.  Private parent dummies all have lifetime 0
    # and follow real lifetime-0 labels under the required fixed tie order.
    if not node.children or node.capacity == 0 or len(rows) == 1:
        return [sorted(row) for row in rows]
    child_orders = []
    for child in node.children:
        child_rows = [[e for e in row if (1 << e) & child.ground]
                      for row in rows]
        child_orders.append(construct(child, child_rows))
    k = len(rows)
    supports = {}
    for child_index, orders in enumerate(child_orders):
        for row_index, order in enumerate(orders):
            for occurrence in range(len(order)):
                supports.setdefault((child_index, occurrence), set()).add(row_index)
    answer = []
    for row_index in range(k):
        active = [(j, occurrence) for j, orders in enumerate(child_orders)
                  for occurrence in range(len(orders[row_index]))]
        active.sort(key=lambda label: (
            -future_lifetime(supports[label], row_index, k), label))
        answer.append([child_orders[j][row_index][occurrence]
                       for j, occurrence in active])
    return answer


def check_window_orders(orders, capacity, family, count=True):
    if capacity == 0:
        if count:
            COUNTS['zero_length_window_cases'] += 1
        return all(not row for row in orders)
    padded = []
    for row_index, row in enumerate(orders):
        if len(row) > capacity:
            return False
        padded.extend(row)
        padded.extend(('dummy', row_index, j)
                      for j in range(capacity - len(row)))
    if len(set(padded)) != len(padded):
        return False
    for start in range(len(padded)):
        window = [padded[(start + j) % len(padded)]
                  for j in range(capacity)]
        real_mask = mask_of(e for e in window if isinstance(e, int))
        if count:
            COUNTS['direct_cyclic_windows'] += 1
        if not independent(real_mask, family):
            return False
    return True


def audit_case(n, family, rows, capacity, suite, theorem=False):
    assert laminar(family)
    assert all(c >= 0 for _, c in family)
    assert len(set(e for row in rows for e in row)) == sum(map(len, rows))
    assert all(len(row) <= capacity and independent(mask_of(row), family)
               for row in rows)
    node = tree_from_subsets(n, family, capacity)
    orders = construct(node, rows)
    if [set(row) for row in orders] != [set(row) for row in rows]:
        fail_case(n, family, rows, capacity, suite, 'block element mismatch')
    if not check_window_orders(orders, capacity, family):
        fail_case(n, family, rows, capacity, suite, 'dependent cyclic window')
    COUNTS[suite + '_cases'] += 1
    COUNTS['cases_with_empty_rows'] += any(not row for row in rows)
    COUNTS['cases_with_unequal_row_lengths'] += len(set(map(len, rows))) > 1
    COUNTS['cases_with_zero_capacity_constraint'] += any(c == 0 for _, c in family)
    COUNTS['cases_with_redundant_above_cardinality'] += any(
        c > s.bit_count() for s, c in family)
    COUNTS['cases_with_missing_nonempty_root'] += n > 0 and all(
        s != (1 << n) - 1 for s, _ in family)
    COUNTS['cases_k1'] += len(rows) == 1
    COUNTS['cases_with_some_real_elements'] += any(rows)
    COUNTS['maximum_ground_size'] = max(COUNTS['maximum_ground_size'], n)
    COUNTS['maximum_row_count'] = max(COUNTS['maximum_row_count'], len(rows))
    COUNTS['maximum_capacity'] = max(COUNTS['maximum_capacity'], capacity)
    if theorem:
        assert sum(map(len, rows)) == n
        assert all(len(row) == capacity for row in rows)
        assert greedy_rank(n, family) == capacity
        COUNTS['theorem_cases'] += 1
    return orders


def fail_case(n, family, rows, capacity, suite, reason):
    raw = {'n': n, 'family': family, 'rows': rows, 'capacity': capacity,
           'suite': suite, 'reason': reason}
    Path(__file__).with_name('failure-raw.json').write_text(
        json.dumps(raw, indent=2), encoding='utf-8')
    # Greedy reduction by whole constraints and unused/selected elements.
    reduced = dict(raw)
    changed = True
    while changed:
        changed = False
        for j in range(len(reduced['family'])):
            candidate = reduced['family'][:j] + reduced['family'][j + 1:]
            candidate_orders = construct(tree_from_subsets(
                n, candidate, capacity), reduced['rows'])
            if not check_window_orders(candidate_orders, capacity, candidate, False):
                reduced['family'] = candidate
                changed = True
                break
        if changed:
            continue
        for i, row in enumerate(reduced['rows']):
            for e in row:
                candidate_rows = [list(r) for r in reduced['rows']]
                candidate_rows[i].remove(e)
                candidate_orders = construct(tree_from_subsets(
                    n, reduced['family'], capacity), candidate_rows)
                if not check_window_orders(candidate_orders, capacity,
                                           reduced['family'], False):
                    reduced['rows'] = candidate_rows
                    changed = True
                    break
            if changed:
                break
    Path(__file__).with_name('failure-reduced.json').write_text(
        json.dumps(reduced, indent=2), encoding='utf-8')
    raise AssertionError(raw)


def all_laminar_subfamilies(n):
    full = (1 << n) - 1
    possible = list(range(1, full))
    for selection in range(1 << len(possible)):
        chosen = [possible[j] for j in bits(selection)]
        if laminar([(s, 0) for s in chosen]):
            yield chosen + ([full] if full else [])


def exhaustive_padded():
    # Every nonempty constrained subset and every laminar subfamily on n<=3.
    # Root is explicit, with every capacity 0..|F|+1 (includes redundancy).
    for n in range(4):
        for subsets in all_laminar_subfamilies(n):
            ranges = [range(s.bit_count() + 2) for s in subsets]
            for caps in it.product(*ranges):
                family = list(zip(subsets, caps))
                capacity = caps[-1] if caps else 0
                COUNTS['exhaustive_presentations'] += 1
                allowed = [independent(m, family) for m in range(1 << n)]
                for k in range(1, 5):
                    # Owner 0 means unselected; owners 1..k give disjoint rows.
                    for owners in it.product(range(k + 1), repeat=n):
                        rows = [[e for e in range(n) if owners[e] == i + 1]
                                for i in range(k)]
                        if all(allowed[mask_of(row)] for row in rows):
                            audit_case(n, family, rows, capacity,
                                       'exhaustive_padded')
                            if sum(map(len, rows)) == n and all(
                                    len(row) == capacity for row in rows):
                                COUNTS['exhaustive_theorem_inputs'] += 1


def exhaustive_labels():
    for k in range(1, 5):
        for labels in range(5):
            for masks in it.product(range(1 << k), repeat=labels):
                supports = [{i for i in range(k) if mask & (1 << i)}
                            for mask in masks]
                orders = []
                for i in range(k):
                    order = [a for a in range(labels) if i in supports[a]]
                    order.sort(key=lambda a: (-future_lifetime(supports[a], i, k), a))
                    orders.append(order)
                for i in range(k):
                    next_i = (i + 1) % k
                    old = {a: j for j, a in enumerate(orders[i])}
                    new = {a: j for j, a in enumerate(orders[next_i])}
                    for a in old.keys() & new.keys():
                        assert new[a] >= old[a]
                        COUNTS['surviving_label_comparisons'] += 1
                    for a, b in it.combinations(range(labels), 2):
                        if a in old and b in old and supports[a] >= supports[b]:
                            assert old[a] < old[b]
                            COUNTS['nested_support_comparisons'] += 1
                COUNTS['exhaustive_active_patterns'] += 1


def random_family(n, rng):
    full = (1 << n) - 1
    family = {}
    def divide(elements, depth):
        subset = mask_of(elements)
        if elements and (depth == 0 or rng.random() < 0.85):
            size = len(elements)
            if rng.random() < 0.18:
                capacity = rng.randrange(size, size + 8)
            else:
                capacity = rng.randrange(size + 1)
            family[subset] = capacity
        if len(elements) <= 1:
            return
        count = rng.randrange(2, min(len(elements), 5) + 1)
        groups = [[] for _ in range(count)]
        shuffled = list(elements)
        rng.shuffle(shuffled)
        for j, e in enumerate(shuffled):
            groups[j % count].append(e)
        for group in groups:
            if rng.random() < 0.8:
                divide(group, depth + 1)
    divide(list(range(n)), 0)
    if rng.random() < 0.5:
        family.pop(full, None)  # Missing root presentation is deliberate.
    family[0] = rng.randrange(5)  # Empty constraints are also deliberate.
    return list(family.items())


def random_padded(rng, repetitions):
    for case in range(repetitions):
        n = rng.randrange(1, 45)
        k = rng.randrange(1, 10)
        family = random_family(n, rng)
        full = (1 << n) - 1
        original_root = next((c for s, c in family if s == full), None)
        capacity = original_root if original_root is not None else rng.randrange(n + 9)
        rows = [[] for _ in range(k)]
        shuffled = list(range(n))
        rng.shuffle(shuffled)
        for e in shuffled:
            i = rng.randrange(k + 2)
            if i < k and len(rows[i]) < capacity and independent(
                    mask_of(rows[i]) | (1 << e), family):
                rows[i].append(e)
        audit_case(n, family, rows, capacity, 'random_padded')
        if n <= 9:
            assert exact_rank(n, family) == greedy_rank(n, family)
            COUNTS['rank_crosschecks'] += 1


def random_theorem(rng, repetitions):
    for case in range(repetitions):
        r = rng.randrange(1, 17)
        k = rng.randrange(1, 10)
        n = r * k
        family = random_family(n, rng)
        permutation = list(range(n))
        rng.shuffle(permutation)
        rows = [permutation[j * r:(j + 1) * r] for j in range(k)]
        # Make the chosen bases feasible; preserve slack and redundant bounds.
        family = [(s, max(c, max((mask_of(row) & s).bit_count()
                                  for row in rows))) for s, c in family]
        full = (1 << n) - 1
        if case % 3 == 0:
            family = [(s, c) for s, c in family if s != full]
        elif case % 3 == 1:
            family = [(s, c) for s, c in family if s != full] + [(full, r + 11)]
        # The matroid needs rank r: absent/redundant full-root presentation can
        # have rank larger. Add a proper rank-r constraint only when enough:
        # use full-root r for theorem; absent and redundant are padded tests,
        # and normalized rank is independently computed below.
        actual_rank = greedy_rank(n, family)
        if actual_rank != r:
            family = [(s, c) for s, c in family if s != full] + [(full, r)]
        rng.shuffle(rows)  # Arbitrary prescribed order retained thereafter.
        audit_case(n, family, rows, r, 'random_theorem', theorem=True)


def brute_force_existence(rng, repetitions):
    # Existence is decided independently by row permutations and direct oracle.
    configurations = [(1, 1), (1, 4), (2, 2), (2, 3), (3, 2), (3, 3), (4, 2)]
    for case in range(repetitions):
        r, k = configurations[case % len(configurations)]
        n = r * k
        family = random_family(n, rng)
        elements = list(range(n))
        rng.shuffle(elements)
        rows = [elements[i * r:(i + 1) * r] for i in range(k)]
        family = [(s, max(c, max((mask_of(row) & s).bit_count()
                                  for row in rows))) for s, c in family
                  if s != (1 << n) - 1]
        family.append(((1 << n) - 1, r))
        constructive = audit_case(n, family, rows, r, 'bruteforce_construction', True)
        feasible_count = 0
        constructive_found = False
        # Enumerate *all* candidates, not merely until the first success.
        for candidate in it.product(*(list(it.permutations(row)) for row in rows)):
            COUNTS['permutation_candidates'] += 1
            if check_window_orders(candidate, r, family, False):
                feasible_count += 1
                if list(map(list, candidate)) == constructive:
                    constructive_found = True
        assert feasible_count > 0 and constructive_found
        COUNTS['permutation_feasible_candidates'] += feasible_count
        COUNTS['bruteforce_existence_cases'] += 1


def targeted():
    cases = [
        (0, [(0, 0)], [[], [], []], 0, False),
        (0, [], [[]], 0, False),
        (3, [(7, 7), (3, 0)], [[], [2], [], []], 7, False),
        (5, [(31, 5), (15, 1), (3, 9), (12, 9)],
         [[0, 4], [2], [], [1], [3]], 5, False),
        (6, [(3, 1), (12, 1), (48, 1)], [[0, 2, 4], [1, 3, 5]], 3, True),
        (6, [(63, 50), (3, 1), (12, 1), (48, 1)],
         [[0, 2, 4], [1, 3, 5]], 3, True),
        (4, [(15, 2), (3, 1), (12, 1)], [[0, 2]], 2, False),
        (6, [(63, 8), (3, 1), (12, 2), (48, 2)],
         [[0, 2, 4], [], [1, 3], [5]], 8, False),
    ]
    # Four parallel classes, rank-three truncation, four prescribed bases.
    rows = [[], [], [], []]
    family = [(4095, 3)]
    for group in range(4):
        family.append((7 << (3 * group), 1))
        element = 3 * group
        for row in range(4):
            if row != group:
                rows[row].append(element)
                element += 1
    for order in it.permutations(range(4)):
        cases.append((12, family, [rows[i] for i in order], 3, True))
    for n, family, rows, capacity, theorem in cases:
        audit_case(n, family, rows, capacity, 'targeted', theorem)
    # Strict inclusion chains exercise depth well beyond ranks used in toy tests.
    for depth in (2, 8, 32, 128, 256):
        k = 7
        rows = [[e for e in range(depth) if e % k == i] for i in range(k)]
        family = []
        for size in range(1, depth + 1):
            subset = (1 << size) - 1
            occupancy = max((mask_of(row) & subset).bit_count() for row in rows)
            family.append((subset, occupancy + (size % 3 == 0) * (depth + 2)))
        capacity = max(map(len, rows)) + 3
        family[-1] = (family[-1][0], capacity)
        audit_case(depth, family, rows, capacity, 'deep_chain')


def main():
    parser = argparse.ArgumentParser()
    parser.add_argument('--seed', type=int, default=2026100811)
    parser.add_argument('--random-padded', type=int, default=20000)
    parser.add_argument('--random-theorem', type=int, default=10000)
    parser.add_argument('--brute-force', type=int, default=350)
    parser.add_argument('--output', default='results.json')
    args = parser.parse_args()
    rng = random.Random(args.seed)
    started = time.monotonic()
    suites = [
        ('exhaustive_labels', exhaustive_labels),
        ('exhaustive_padded', exhaustive_padded),
        ('targeted', targeted),
        ('random_padded', lambda: random_padded(rng, args.random_padded)),
        ('random_theorem', lambda: random_theorem(rng, args.random_theorem)),
        ('brute_force_existence', lambda: brute_force_existence(rng, args.brute_force)),
    ]
    durations = {}
    for name, suite in suites:
        begin = time.monotonic()
        suite()
        durations[name] = round(time.monotonic() - begin, 6)
        print(name, 'PASS', 'seconds=', durations[name], flush=True)
    report = {'status': 'PASS', 'seed': args.seed,
              'arguments': vars(args), 'counts': dict(sorted(COUNTS.items())),
              'suite_seconds': durations,
              'elapsed_seconds': round(time.monotonic() - started, 6)}
    Path(args.output).write_text(json.dumps(report, indent=2) + '\n', encoding='utf-8')
    print(json.dumps(report, indent=2), flush=True)


if __name__ == '__main__':
    main()
