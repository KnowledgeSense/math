# Universal unimodality of coronas

Classifies the attachments for which every graph corona has a unimodal independence polynomial, and constructs arbitrarily large counterexamples for the other attachments.

Entry points:

- `MainTheorems/Corona/Classification.lean`

## Build

Lean 4.34.1 and Mathlib v4.34.1 are pinned at the repository root.
On Windows, use a short checkout path, such as `C:/math`.

From the repository root:

```sh
lake exe cache get
lake --wfail build Corona
lake script run audit Corona
lake env leanchecker --fresh Corona
```

`Audit.lean` lists the axioms used by the main results and selected supporting theorems.
