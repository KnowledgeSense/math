#!/usr/bin/env bash
set -euo pipefail
cd -- "$(dirname -- "$0")"
DATA=had32_tr.txt.gz
URL='https://users.cecs.anu.edu.au/~bdm/data/hadamard/had32_tr.txt.gz'
HASH=e51a18c458e1bae995e335e5067b53078e7e8c6901278e755d33c1b281547520
if [[ ! -f "$DATA" ]]; then
  curl -L --fail --retry 2 "$URL" -o "$DATA"
fi
python3 - "$DATA" "$HASH" <<'PY'
import sys,hashlib
h=hashlib.sha256()
with open(sys.argv[1],'rb') as f:
    for b in iter(lambda:f.read(1<<20),b''):h.update(b)
if h.hexdigest()!=sys.argv[2]:raise RuntimeError('Dataset SHA-256 mismatch')
print('Dataset SHA-256 verified')
PY
c++ -O3 -std=c++17 filter_hadamard32.cpp -lz -o filter_hadamard32
./filter_hadamard32 "$DATA" had32_rank_le7.rescan.txt
cmp had32_rank_le7.txt had32_rank_le7.rescan.txt
python3 verify_hadamard_certificates.py
python3 verify_eight_full.py
python3 audit/independent_audit.py
python3 audit/independent_eight_spectra.py
c++ -O3 -std=c++17 audit/independent_filter32.cpp -lz -o audit/independent_filter32
./audit/independent_filter32 "$DATA" audit/independent_rank_le7.rescan.txt
cmp had32_rank_le7.txt audit/independent_rank_le7.rescan.txt
python3 audit/independent_check32.py
printf '\nAll original and independent verification steps passed.\n'
