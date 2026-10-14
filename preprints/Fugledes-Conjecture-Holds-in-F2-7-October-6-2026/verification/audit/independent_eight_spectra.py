"""Independent spectral decision for all 549 normalized eight-point sets.
Works with character value patterns on the eight positions. Balanced rows have
four negative entries; two rows are orthogonal exactly when their negative-entry
patterns have Hamming distance four. Searches seven mutually orthogonal balanced
rows alongside the constant row, in ascending pattern order. No author code.
"""
from functools import lru_cache
from collections import Counter
from pathlib import Path
import json
from independent_audit import dot, need, BASE, OUT

def spectral_eight(T,r):
    patterns=[]
    for a in range(1,2**r):
        v=sum(dot(a,t)<<i for i,t in enumerate(T))
        if bin(v).count('1')==4:patterns.append(v)
    need(len(patterns)==len(set(patterns)),'character restriction unexpectedly duplicated')
    patterns=tuple(sorted(patterns))
    @lru_cache(None)
    def extend(available,missing):
        if missing==0:return True
        if len(available)<missing:return False
        # Each possible smallest remaining row is considered exactly once.
        for i in range(len(available)-missing+1):
            row=available[i]
            compatible=tuple(other for other in available[i+1:] if bin(row^other).count('1')==4)
            if extend(compatible,missing-1):return True
        return False
    return extend(patterns,7)

if __name__=='__main__':
    data=json.loads((BASE/'eight_certificates.json').read_text())
    counts=Counter()
    for d in data:
        result=spectral_eight(d['T'],d['r'])
        need(result==(d['tile'] is not None),'independent spectral classification mismatch')
        counts['spectral' if result else 'non_spectral']+=1
    need(dict(counts)=={'spectral':168,'non_spectral':381},'incorrect totals')
    print('INDEPENDENT CHARACTER-PATTERN CHECK',dict(counts),'total',len(data))
    (OUT/'independent_eight_spectra_results.json').write_text(json.dumps(dict(counts),indent=2)+'\n')
