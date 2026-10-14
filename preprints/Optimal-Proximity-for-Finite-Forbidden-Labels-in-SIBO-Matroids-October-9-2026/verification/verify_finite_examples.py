"""Independent finite checks of actual bases and directed interval obstructions.

No supplied proof or supplied verification routine is imported.
Finite computations supplement the general proof; they do not prove all cases.
"""
from itertools import product
from math import prod, comb
from pathlib import Path
import json

def mixed_radix():
    rows=[]
    total=0
    for k in range(5):
        for sizes in product(range(4),repeat=k):
            moduli=[]
            forbidden=[]
            scale=1
            for q in sizes:
                modulus=scale*(q+1)
                forbidden.append({j*scale-1 for j in range(1,q+1)})
                moduli.append(modulus)
                scale=modulus
            rank=scale-1
            good=[count for count in range(scale) if all(count % m not in f for m,f in zip(moduli,forbidden))]
            assert good==[rank]
            assert all(len(f)==q for f,q in zip(forbidden,sizes))
            bases=sum(comb(rank,x)*comb(rank,rank-x) for x in good)
            assert bases==1
            total+=scale
            rows.append({'sizes':sizes,'D':scale,'distance':rank,'feasible_occupancy':good,'feasible_basis_count':bases})
    return {'tuples':len(rows),'occupancy_values':total,'largest_rank':max(x['distance'] for x in rows),'rows':rows}

def partition_bases():
    # Four blocks {a_i,b_i}; a basis chooses one item from each block.
    # This is a nonuniform SBO (hence SIBO) matroid of rank four on eight items.
    # a_i labels are zero; b_i labels range over C2 x C4 in all 8^4 ways.
    group=list(product(range(2),range(4)))
    bases=list(product(range(2),repeat=4))
    instances=feasible_instances=distance_checks=0
    max_dist=0
    witness=None
    for labels in product(group,repeat=4):
        instances+=1
        good=[]
        for b in bases:
            s1=sum(labels[i][0]*b[i] for i in range(4))%2
            s2=sum(labels[i][1]*b[i] for i in range(4))%4
            if s1!=0 and s2!=1:
                good.append(b)
        if not good:
            continue
        feasible_instances+=1
        for a in bases:
            distance=min(sum(x!=y for x,y in zip(a,b)) for b in good)
            assert distance<=3
            distance_checks+=1
            if distance>max_dist:
                max_dist=distance
                witness={'labels':labels,'start':a,'feasible_bases':good,'distance':distance}
    assert max_dist==3
    return {'instances':instances,'feasible_instances':feasible_instances,'start_basis_checks':distance_checks,'maximum_distance':max_dist,'witness':witness}

def interval_chains(moduli,T):
    # If every forward prefix difference belongs to a forbidden slab,
    # the vertices form a directed chain in this finite relation.
    group=list(product(*(range(m) for m in moduli)))
    zero=(0,)*len(moduli)
    allowed={a:[b for b in group if any((b[t]-a[t])%moduli[t] in T[t] for t in range(len(moduli)))] for a in group}
    visited=0
    longest=[zero]
    def search(chain,candidates):
        nonlocal visited,longest
        visited+=1
        if len(chain)>len(longest):
            longest=list(chain)
        for b in candidates:
            search(chain+[b],[c for c in candidates if c in allowed[b]])
    search([zero],allowed[zero])
    bound=prod(len(t)+1 for t in T)-1
    distance=len(longest)-1
    assert distance<=bound
    return {'moduli':moduli,'forbidden_differences':T,'maximum_obstructed_intervals':distance,'product_bound':bound,'search_nodes':visited,'longest_prefix_chain':longest}

def main():
    result={'status':'PASS','method':'Independent exact finite enumeration; no supplied routines imported',
            'sharpness':mixed_radix(),
            'actual_partition_bases':partition_bases(),
            'interval_obstructions':[
                interval_chains([2,4],[[1],[2]]),
                interval_chains([3,6],[[1,2],[3]]),
                interval_chains([2,2],[[1],[1]])]}
    output=Path(__file__).parent/'finite_examples.json'
    output.write_text(json.dumps(result,ensure_ascii=False,indent=2),encoding='utf-8')
    summary={**result,'sharpness':{k:v for k,v in result['sharpness'].items() if k!='rows'}}
    print(json.dumps(summary,ensure_ascii=False,indent=2))

if __name__=='__main__':
    main()
