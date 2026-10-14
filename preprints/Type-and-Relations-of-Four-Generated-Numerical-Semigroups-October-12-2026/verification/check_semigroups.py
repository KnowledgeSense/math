"""Exact finite checks for type and relations of numerical semigroups.
Author: Knowledge Sense
"""
from pathlib import Path
from itertools import combinations, permutations
from functools import reduce
from math import gcd
from heapq import heappush, heappop
from collections import Counter
import json, time

ROOT=Path(__file__).resolve().parent
INF=10**30

def residue_table(gens,mod=None):
    mod=mod or min(gens); d=[INF]*mod; d[0]=0; q=[(0,0)]
    while q:
        val,r=heappop(q)
        if val!=d[r]: continue
        for a in gens:
            w=val+a; s=w%mod
            if w<d[s]: d[s]=w; heappush(q,(w,s))
    return d

def member(s,d): return s>=0 and d[s%len(d)]<=s

def invariants(gens):
    d=residue_table(gens); F=max(d)-min(gens)
    pf=[s-min(gens) for s in d if all(member(s+a-min(gens),d) for a in gens)]
    betti=[]
    for s in range(1,F+2*max(gens)+1):
        vertices=[i for i,a in enumerate(gens) if member(s-a,d)]
        if len(vertices)<2: continue
        parent=list(range(4))
        def find(i):
            while i!=parent[i]: i=parent[i]
            return i
        for i,j in combinations(vertices,2):
            if member(s-gens[i]-gens[j],d): parent[find(i)]=find(j)
        n=len({find(i) for i in vertices})
        if n>1: betti.append({'degree':s,'components':n,'contribution':n-1})
    return {'generators':list(gens),'F':F,'PF':sorted(pf),'t':len(pf),
            'eta':sum(x['contribution'] for x in betti),'betti':betti}

def critical_graph(gens):
    critical=[]; edges=[]; full=[]; tables=[]
    for i,a in enumerate(gens):
        other=[x for j,x in enumerate(gens) if j!=i]; d=residue_table(other); tables.append(d)
        for q in range(1,min(other)//gcd(a,min(other))+1):
            if member(q*a,d): break
        critical.append(q)
        edges.append([j for j,x in enumerate(gens) if j!=i and member(q*a-x,d)])
        if member(q*a-sum(other),d): full.append(i)
    return critical,edges,full,tables

def order_choice(gens):
    a,edges,F,tab=critical_graph(gens)
    indeg=[sum(j in es for es in edges) for j in range(4)]
    prim=[j for j in range(4) if indeg[j]>=2]
    if prim:
        choices=[j for j in prim if j not in F] or [j for j in prim if indeg[j]==3]
        assert choices
        j=choices[0]; others=[i for i in range(4) if i!=j]
        others.sort(key=lambda i:(j not in edges[i],gens[i]))
        return tuple(gens[i] for i in [j]+others),'primary'
    for order in permutations(range(4)):
        i,j,k,l=order
        if a[i]*gens[i]==a[j]*gens[j] and a[k]*gens[k]==a[l]*gens[l] and a[i]*gens[i]!=a[k]*gens[k]:
            return tuple(gens[u] for u in order),'secondary'
    raise AssertionError('classification')

def apery_geometry(gens,inv,ordered=None):
    order,kind=order_choice(gens)
    if ordered is not None: order=ordered
    d0,dx,dy,dz=order
    a,edges,F,tables=critical_graph(order)
    ap=residue_table(order,mod=d0); ap_set=set(ap); M=max(ap)
    T={(u,v,w) for w in range(a[3]) for u in range(M//dx+1)
       for v in range(max(0,(M-u*dx-w*dz)//dy)+1) if u*dx+v*dy+w*dz in ap_set}
    assert len(T)==d0 and len({u*dx+v*dy+w*dz for u,v,w in T})==d0
    units=((1,0,0),(0,1,0),(0,0,1))
    plus=lambda p,e:tuple(p[i]+e[i] for i in range(3))
    corners=[p for p in T if all(plus(p,e) not in T for e in units)]
    boundary={plus(p,e) for p in T for e in units if plus(p,e) not in T}
    G=sorted(p for p in boundary if all(tuple(p[j]-(j==i) for j in range(3)) in T for i in range(3) if p[i]>0))
    r=sum(all(c>0 for c in p) for p in G); mu=len(G); tp=len(corners)
    monomial=member(a[3]*dz-d0,residue_table(order))
    assert r<=1
    assert tp<=mu+r-2
    assert mu<=2*tp+1
    assert inv['eta']<=mu
    assert tp-inv['t']<=r+1
    if not monomial and r==0: assert inv['eta']>=mu-1
    elif monomial: assert inv['eta']==mu and inv['t']==tp
    return {'order':order,'kind':kind,'a':a,'mu':mu,'t_prime':tp,'r':r,
            'monomial':monomial,'corner_gap':tp-inv['t'],'generator_gap':mu-inv['eta']}

def all_orders(gens):
    a,edges,F,tab=critical_graph(gens)
    for order in permutations(range(4)):
        i,j,k,l=order
        primary=i in edges[j] and i in edges[k]
        secondary=all(len(es)==1 for es in edges) and a[i]*gens[i]==a[j]*gens[j] and a[k]*gens[k]==a[l]*gens[l] and a[i]*gens[i]!=a[k]*gens[k]
        if primary or secondary: yield tuple(gens[u] for u in order)

def small_order_ideals():
    rows=[(a,b,c) for a in range(4) for b in range(a+1) for c in range(b+1)]
    counts=Counter(); failures=[]
    for row0 in rows:
      for row1 in rows:
        if any(row1[i]>row0[i] for i in range(3)):continue
        for row2 in rows:
          if any(row2[i]>row1[i] for i in range(3)):continue
          heights=(row0,row1,row2)
          T={(x,y,z) for x in range(3) for y in range(3) for z in range(heights[x][y])}
          if not T:continue
          counts['ideals']+=1
          units=((1,0,0),(0,1,0),(0,0,1))
          plus=lambda p,e:tuple(p[i]+e[i] for i in range(3))
          corners=[p for p in T if all(plus(p,e) not in T for e in units)]
          a=max(p[2] for p in T)+1
          boundary={plus(p,e) for p in T for e in units if plus(p,e) not in T}
          G={p for p in boundary if all(tuple(p[j]-(j==i) for j in range(3)) in T for i in range(3) if p[i]>0)}
          r=sum(all(v>0 for v in p) for p in G)
          top=sorted((x,y) for x,y,z in corners if z==a-1)
          for b in range(4):
            for c in range(1,4):
              spurious=[i for i,(x,y) in enumerate(top) if (x+b,y+c,0) in T]
              assert len(spurious)<=r+1
              images=[]
              for i in spurious:
                if i==0:continue
                projection=(top[i-1][0]+1,top[i][1]+1)
                matches=[p for p in G if p[:2]==projection and p[2]<=a-1]
                assert len(matches)==1 and all(v>0 for v in matches[0])
                images.append(matches[0]);counts['injections']+=1
              assert len(images)==len(set(images))
              counts['tails']+=1
    return dict(counts)

def graph_check():
    valid=0
    arcs=[(i,j) for i in range(4) for j in range(4) if i!=j]
    for mask in range(1<<12):
        edges=[set() for _ in range(4)]
        for u,(i,j) in enumerate(arcs):
            if mask>>u&1: edges[i].add(j)
        if not all(edges): continue
        indeg=[sum(j in e for e in edges) for j in range(4)]
        prim=[j for j in range(4) if indeg[j]>=2]
        if not prim: continue
        eligible=[i for i in range(4) if len(edges[i])==3]
        for fm in range(1<<len(eligible)):
            F={eligible[k] for k in range(len(eligible)) if fm>>k&1}
            assert any(j not in F or indeg[j]==3 for j in prim)
            valid+=1
    return valid

def main():
    start=time.perf_counter(); stats=Counter(); examples=[]; violations=[]
    records=[]; order_stats=Counter(); special_orders=[]
    for gens in combinations(range(2,29),4):
        if reduce(gcd,gens)!=1: continue
        if any(member(x,residue_table([a for a in gens if a!=x])) for x in gens): continue
        inv=invariants(gens); geo=apery_geometry(gens,inv)
        stats['total']+=1; stats[geo['kind']]+=1
        stats['monomial' if geo['monomial'] else 'nonmonomial']+=1
        stats['r_'+str(geo['r'])]+=1; stats['corner_gap_'+str(geo['corner_gap'])]+=1
        stats['generator_gap_'+str(geo['generator_gap'])]+=1
        stats['type_'+str(inv['t'])]+=1
        if not inv['t']+1<=inv['eta']<=2*inv['t']+3: violations.append(inv)
        records.append({'generators':gens,'t':inv['t'],'eta':inv['eta'],**geo})
        if max(gens)<=20:
            for order in all_orders(gens):
                og=apery_geometry(gens,inv,ordered=order)
                order_stats['total']+=1;order_stats['r_'+str(og['r'])]+=1
                order_stats['corner_gap_'+str(og['corner_gap'])]+=1
                if og['r']==1 and len(special_orders)<4:special_orders.append({'generators':gens,'t':inv['t'],'eta':inv['eta'],**og})
    for gens in [(5,6,7,8),(37,57,174,234),(77,85,89,131),(76,99,143,223),(195,200,209,226),
                 (145,203,74,111),(196,225,256,289),(8,12,18,27),(4,5,6,7)]:
        inv=invariants(gens); inv['geometry']=apery_geometry(gens,inv); examples.append(inv)
    result={'method':'residue shortest paths and squarefree divisor graph',
            'range':'all minimal four-generated semigroups with sorted generators between 2 and 28',
            'graph_configurations':graph_check(),'counts':dict(stats),'violations':violations,
            'all_legal_orders_up_to_20':dict(order_stats),'r1_examples':special_orders,
            'small_order_ideals':small_order_ideals(),
            'examples':examples,'elapsed_seconds':time.perf_counter()-start}
    (ROOT/'independent_checks.json').write_text(json.dumps(result,ensure_ascii=False,indent=2),encoding='utf-8')
    (ROOT/'independent_semigroups.json').write_text(json.dumps(records,ensure_ascii=False),encoding='utf-8')
    print(json.dumps(result,ensure_ascii=False,indent=2))

if __name__=='__main__':main()
