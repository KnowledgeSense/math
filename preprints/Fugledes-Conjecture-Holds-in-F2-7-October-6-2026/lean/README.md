# Lean certificates

Formal verification of the finite certificates accompanying the [manuscript](../article.pdf).

| Certificates | Count | Statements |
| --- | ---: | --- |
| Hadamard matrices of order 16 | 5 | Orthogonality, binary row-space coordinates, tiling |
| Hadamard matrices of order 32 | 32 | The same statements for both orientations of 16 representatives |
| Eight-point sets | 168 | Tiling, spectral orthogonality, nonzero Walsh conditions |
| Excluded orders | 11 | Numerical determinant bounds |

Binary vectors are encoded as integers, with XOR as addition. The theorem
`tiles_give_unique_representation` proves that the finite tiling check gives
a unique decomposition of every vector into a point and a translation.

## Build

From the repository root, run:

```sh
lake exe cache get
lake --wfail build FugledeCertificates
lake script run audit FugledeCertificates
lake script run certificates FugledeCertificates
lake env leanchecker --fresh FugledeCertificates
```

The shared toolchain and dependency revisions are pinned at the repository root.

## Source

| File | Contents |
| --- | --- |
| `FugledeCertificates/Definitions.lean` | Hadamard matrices, row-space witnesses, finite tiling |
| `FugledeCertificates/Tiling.lean` | Unique decomposition from the tiling condition |
| `FugledeCertificates/Spectrum.lean` | Binary characters and spectral orthogonality |
| `FugledeCertificates/Hadamard.lean` | Order-16 and order-32 certificate theorems |
| `FugledeCertificates/EightPoint.lean` | Eight-point certificate theorems |
| `FugledeCertificates/Cardinality.lean` | The numerical inequalities for excluded orders |
| `FugledeCertificates/Data/` | Certificate data from `../verification/` |

These theorems cover the finite certificates and inequalities above. The complete
classification scan is supplied in [the verification package](../verification/);
the general mathematical reductions are given in the manuscript.

## Reproduction

To compare the generated Lean data with the original inputs, use Python 3.10
or later from this directory:

```sh
python scripts/generate_data.py --check
```

Omit `--check` to regenerate the two data files. The generator computes the
linear-combination witnesses; Lean checks them against the source matrices.
