"""Check the cyclic sharpness construction in the manuscript (Python 3 only)."""
from itertools import product
from math import prod
import json
from pathlib import Path


def check(qs):
    D = prod(q + 1 for q in qs)
    moduli, forbidden = [], []
    previous = 1
    for q in qs:
        modulus = previous * (q + 1)
        target = {j * previous % modulus for j in range(1, q + 1)}
        assert len(target) == q and 0 not in target
        moduli.append(modulus)
        forbidden.append(target)
        previous = modulus
    allowed = [ell for ell in range(D)
               if all(ell % n not in target
                      for n, target in zip(moduli, forbidden))]
    assert allowed == [0], (qs, allowed)
    # A basis of U_(D-1,2D-2) is feasible precisely when it contains zero A-elements.
    # For the interval example every possible nonempty interval has length 1,...,D-1.
    assert all(any(length % n in target
                   for n, target in zip(moduli, forbidden))
               for length in range(1, D))
    return {"sizes": list(qs), "D": D, "unique_allowed_A_count": 0,
            "distance": D - 1, "status": "PASS"}


if __name__ == "__main__":
    cases = [check(qs) for k in range(5) for qs in product(range(5), repeat=k)]
    result = {"status": "PASS", "tuples_checked": len(cases),
              "scope": "0 <= k <= 4 and 0 <= q_t <= 4", "cases": cases}
    Path("manuscript_examples.json").write_text(
        json.dumps(result, ensure_ascii=False, indent=2) + "\n", encoding="utf-8")
    print(f"PASS: {len(cases)} tuples; unique feasible basis and all interval lengths")
