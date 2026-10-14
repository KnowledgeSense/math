# Finite checks for the laminar construction

Requirements: Python 3.12 or later; standard library only.

Run from this directory:

```text
python verify.py --output results.json
```

The script constructs an inclusion tree from subset-capacity constraints and independently checks each output window against those original constraints. It also checks that every input row keeps precisely its original real elements and that all elements are used once. The suites cover active-label supports, exhaustive small laminar families, empty rows, redundant and zero capacities, deep chains, random padded rows and basis partitions, and exhaustive within-row permutations for small inputs. The four-parallel-class example is tested for all block orders.

Successful completion prints PASS for each suite and writes status PASS with the seed, suite parameters and counts to results.json. Assertion failures stop the program. The supplied results.json records a completed run with the default parameters. Timing measurements depend on the environment.

These finite checks are diagnostics. The unrestricted theorem follows from the mathematical induction in the [accompanying manuscript](../article.pdf).
