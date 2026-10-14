"""Audit all retained order-32 matrices, both orientations, with alternate pivot.
Uses rank/tiling code from this audit only, not author's code. Checks supplied
witnesses in their coordinates and independently finds fresh exact-cover tiles
in an alternative normalization (row 17 / column 13 instead of row 0 / col 0).
"""
from pathlib import Path
from itertools import combinations
import json, random
from independent_audit import need, dot, tiling_search, verify_tiling, echelon_rows, BASE, OUT

def canonical(words,n=32,base_row=17,base_column=13):
    normalized=[(x^words[base_row])^(((1<<n)-1) if ((x^words[base_row])>>base_column)&1 else 0) for x in words]
    # Eliminate columns using a basis of rows. Reverse input row order and bit
    # order for coordinate independence from the author's canonicalization.
    normalized=list(reversed(normalized))
    basis=echelon_rows(normalized)
    E=[sum(((word>>j)&1)<<i for i,word in enumerate(basis)) for j in range(n)]
    need(len(set(E))==n,'canonical projection not injective')
    return E,len(basis)

def transpose(words):
    return [sum(((word>>j)&1)<<i for i,word in enumerate(words)) for j in range(32)]

def main():
    a=(OUT/'independent_rank_le7.txt').read_text().splitlines()
    b=(BASE/'had32_rank_le7.txt').read_text().splitlines()
    need(a==b,'independent class filter differs')
    need(len(a)==16,'expected 16 extended representatives')
    certificates=json.loads((BASE/'spectral32_certificates.json').read_text())
    need(len(certificates)==32,'expected 32 oriented certificates')
    cert={(d['class_index'],d['transpose']):d for d in certificates}
    need(len(cert)==32,'duplicate certificate')
    out=[];rnd=random.Random(734001)
    for line in a:
        tokens=line.split();index,r=int(tokens[0]),int(tokens[1]);words=[int(s,16) for s in tokens[2:]]
        need(len(words)==32,'row count')
        need(all(bin(x^y).count('1')==16 for x,y in combinations(words,2)),'Hadamard orthogonality')
        for tr in [False,True]:
            M=transpose(words) if tr else words
            E,rank=canonical(M)
            need(rank==r,'alternate normalization rank changed')
            T=tiling_search(E,r)
            need(T is not None,'failed independent order32 tiling')
            verify_tiling(E,T,r)
            d=cert[(index,tr)]
            verify_tiling(d['E'],d['T'],r)
            # Check supplied E really corresponds to author's row-basis convention,
            # independently reconstructed, rather than trusting detached witnesses.
            rows=[(x^M[0])^((2**32-1) if (x^M[0])%2 else 0) for x in M]
            basis=echelon_rows(rows)
            expected=[sum(((v>>j)%2)<<i for i,v in enumerate(basis)) for j in range(32)]
            need(expected==d['E'],'certificate detached from source representative')
            need(d['r']==r,'certificate rank')
            # Stress-test rank invariance under independent row/column sign flips,
            # permutations, and arbitrary normalized pivots. This is supplemental,
            # not the mathematical equivalence proof.
            for trial in range(10):
                rp=list(range(32));cp=list(range(32));rnd.shuffle(rp);rnd.shuffle(cp)
                colsign=rnd.getrandbits(32)
                Q=[sum(((M[i]>>j)&1)<<k for k,j in enumerate(cp)) ^ colsign ^ (2**32-1 if rnd.randrange(2) else 0) for i in rp]
                _,rr=canonical(Q,base_row=rnd.randrange(32),base_column=rnd.randrange(32))
                need(rr==r,'equivalence stress-test failed')
            out.append({'class_index':index,'transpose':tr,'r':r,'normalization_row':17,'normalization_column':13,'E':E,'T':T})
    (OUT/'independent_thirtytwo_tilings.json').write_text(json.dumps(out,indent=2)+'\n')
    print('INDEPENDENTLY VERIFIED',len(out),'oriented representatives; alternate normalization; source attachment; 320 equivalence stress-tests')
if __name__=='__main__':main()
