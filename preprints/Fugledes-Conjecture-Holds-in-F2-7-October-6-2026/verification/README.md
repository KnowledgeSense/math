# Computational verification

Certificates and programs accompanying [Fuglede’s conjecture holds in F₂⁷](../article.pdf). Run the commands below from this directory.

## Certificate verification

Python 3.10 or later is sufficient; no third-party Python packages are required.

```sh
python3 verify_hadamard_certificates.py
python3 verify_eight_full.py
```

The first command checks all five order-16 certificates, all 32 oriented order-32 certificates, and the non-power-of-two cardinality exclusions. The second checks the 549 eight-point cases.

## Complete rank scan

The complete order-32 classification is available from [Brendan McKay's Hadamard database](https://users.cecs.anu.edu.au/~bdm/data/hadamard.html). Its compressed data file is downloaded by the reproduction script and is not included in this repository.

```sh
bash reproduce_full.sh
```

This requires Bash, Python 3.10 or later, a C++17 compiler, zlib, and curl. The script verifies the input file, runs both C++ rank scans, compares the selected records, and runs the certificate checks and independent verification programs.

Input data: `had32_tr.txt.gz`, 142,334,914 bytes.
SHA-256: `e51a18c458e1bae995e335e5067b53078e7e8c6901278e755d33c1b281547520`.

The scan processes 6,857,010 classes modulo equivalence and transposition and retains 16 classes with dephased binary rank at most seven. Certificates are supplied for both orientations of each retained matrix.

The full rank distribution is:

| Rank | Classes |
| --- | ---: |
| 5 | 1 |
| 6 | 2 |
| 7 | 13 |
| 8 | 150 |
| 9 | 1,874 |
| 10 | 20,202 |
| 11 | 158,127 |
| 12 | 786,379 |
| 13 | 2,250,131 |
| 14 | 2,753,834 |
| 15 | 886,297 |
| Total | 6,857,010 |

## Additional independent verification

A separate full-rank implementation is provided for PowerShell:

```powershell
./double_check_exact_scan.ps1 -DataPath ./had32_tr.txt.gz -OutputDirectory ./double-check
```

Its retained records and rank distribution are included in `double-check/`. Using those records, the verification from mathematical definitions can be run with:

```sh
python3 double_check_from_definitions.py --packet . --output ./double-check
```

The latter command regenerates the eight-point cases, checks the integer Walsh diagonalization, and checks the Hadamard certificates under all base-row and base-column choices. Stored results are available in `double-check/double_check_results.json`.

## Files

| Path | Contents |
| --- | --- |
| `had.16.0.txt` through `had.16.4.txt` | Five order-16 Hadamard representatives |
| `had32_rank_le7.txt` | Sixteen selected order-32 representatives |
| `spectral16_certificates.json` | Order-16 tiling certificates |
| `spectral32_certificates.json` | Order-32 tiling certificates, both orientations |
| `eight_certificates.json` | Eight-point cases and witnesses |
| `verify_hadamard_certificates.py` | Direct certificate verification |
| `verify_eight_full.py` | Complete eight-point verification |
| `filter_hadamard32.cpp` | First rank-scan implementation |
| `audit/independent_filter32.cpp` | Second rank-scan implementation |
| `audit/independent_audit.py` | Independent checks for order 16 and eight-point sets |
| `audit/independent_check32.py` | Independent order-32 checks |
| `audit/independent_eight_spectra.py` | Independent spectrality checks |
| `double_check_exact_scan.ps1` | Third full-rank scan |
| `double_check_from_definitions.py` | Verification from mathematical definitions |
| `reproduce_full.sh` | Complete reproduction procedure |

The manuscript relies on the published completeness of the Hadamard classifications. Data checksums identify the files used; the classification results and the mathematical reductions supply completeness of the case analysis.
