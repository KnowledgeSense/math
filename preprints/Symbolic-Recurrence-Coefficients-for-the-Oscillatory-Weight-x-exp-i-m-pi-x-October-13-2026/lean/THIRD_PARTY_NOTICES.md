# Third-party attribution

The following upstream notice applies to the adapted π-transcendence proof and its supporting algebraic lemmas, not to the oscillatory-recurrence formalization as a whole. The upstream license is included as `LICENSE-APACHE-2.0.md`.

## Upstream notice

This repository contains a formalization, in Lean 4, of the mathematics of

    Michael Spivak, *Calculus* (Publish or Perish; 3rd edition 1994,
    4th edition 2008).

The Lean code in this repository is licensed under the Apache License 2.0
(see LICENSE) and is Copyright 2026 Jon-Erik G. Storm.

The underlying mathematics, the choice and ordering of the results, and the
problems whose content the theorems formalize are Spivak's, and the book is
his copyrighted work.  This repository is an independent formalization; it is
not affiliated with, endorsed by, or published by Michael Spivak or Publish or
Perish, Inc.  It is not a substitute for the book: it reproduces neither the
book's exposition nor its text, and the problems are identified by number
rather than reproduced.  Readers need a copy of the book to follow it.

Where a docstring describes what a theorem formalizes, or records that a
statement in the book is false as printed, it does so in the brief terms
needed to make the Lean statement intelligible.

Only the pi-transcendence proof and its required algebraic lemmas are included here. Adaptations change imports, namespace, and isolate the constant-term reduction.
Source: https://github.com/stormj-UH/spivak-lean/tree/fourth-edition
Pi source blob: ef71e88c6a47ae4f3f81459bd0b6afee90731bde
Auxiliary source blob: e059d9d4dadf694505ce6467ef7fa40566f14293
Constant-term reduction source blob: 0d2362aeef3bba1653f8eea8def2cdc1139dc816

Compatibility changes for the pinned mathlib version:
- Replace `Equiv.Finset.congr` with `Equiv.finsetCongr`.
- Use `integerNormalization_spec` for the normalization identity.
- Add an explicit congruence step in the symmetric-polynomial coefficient proof.
