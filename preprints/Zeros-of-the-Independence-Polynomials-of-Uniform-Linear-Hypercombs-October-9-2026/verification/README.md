Exact supplementary checks for uniform linear hypercombs

Requirements: Python 3.10 or newer and SymPy 1.14.0.
Install with: python -m pip install -r requirements.txt
Run with: python verify.py > results.json

The output status must be PASS and its parsed JSON must equal expected.json.
All checks use exact integer/rational or symbolic arithmetic. The five direct
subset counts examine a total of 100488 subsets; determinant controls retain
symbolic a for n=2,...,6. Finite checks validate transcription and the model.
The all-length and all-parameter proof is in the accompanying manuscript. The script writes stdout only and uses no network or local data.
