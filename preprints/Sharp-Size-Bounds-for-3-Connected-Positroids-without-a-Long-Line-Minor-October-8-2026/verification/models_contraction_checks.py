from models_exact_checks import construct, ROOT
from itertools import combinations
import json

def check(source,target,label,cm,mapping):
    sn,_,_,sr=source;tn,_,_,tr=target
    si={name:i for i,name in enumerate(sn)}
    assert set(mapping)==set(tn),(label,tn,mapping)
    mappedbits=[1<<si[mapping[name]] for name in tn]
    assert len(set(mappedbits))==len(mappedbits)
    bad=[]
    for mask in range(1<<len(tn)):
        om=sum(mappedbits[i] for i in range(len(tn)) if mask&(1<<i))
        if sr(om|cm)-sr(cm)!=tr(mask):bad.append(mask)
    assert not bad,(label,bad[:5])
    return dict(label=label,compared_subset_ranks=1<<len(tn),passed=True)

def uniform(names,r=2):
    return names,None,None,lambda mask:min(r,mask.bit_count())

results=[]
for r,t in [(3,2),(3,3),(4,2),(4,3),(5,2)]:
    src=construct('G',r,t)
    for ei in range(r):
        cm=1<<(r+ei*(t-1))
        junctions=[ei]+[(ei+i)%r for i in range(2,r)]
        oldedges=[(ei+i)%r for i in range(1,r)]
        if r==3:
            retained=[f'v{i}' for i in junctions]+[f'e{i}f{j}' for i in oldedges for j in range(t-1)]
            target=uniform(retained);mapping={n:n for n in retained}
        else:
            target=construct('G',r-1,t)
            mapping={f'v{k}':f'v{i}' for k,i in enumerate(junctions)}
            mapping.update({f'e{k}f{j}':f'e{i}f{j}' for k,i in enumerate(oldedges) for j in range(t-1)})
        results.append(check(src,target,f'G({r},{t}) edge {ei}',cm,mapping))

for r,t in [(3,2),(3,3),(4,2),(4,3),(5,2)]:
    for size in range(1,r):
        for inside in combinations(range(1,r),size):
            C=[0,*inside,r];src=construct('A',r,t,C)
            for ei in range(r):
                cm=1<<(r+1+ei*(t-1));heavy=len(C)==3 and ei in C and ei+1 in C
                if heavy:
                    merged=set(C);junctions=[ei]+[j for j in range(r+1) if j not in merged]
                    oldedges=[j for j in range(r) if j!=ei]
                    if r==3:
                        retained=[f'v{i}' for i in junctions]+[f'e{i}f{j}' for i in oldedges for j in range(t-1)]
                        target=uniform(retained);mapping={n:n for n in retained}
                    else:
                        target=construct('G',r-1,t)
                        mapping={f'v{k}':f'v{i}' for k,i in enumerate(junctions)}
                        mapping.update({f'e{k}f{j}':f'e{i}f{j}' for k,i in enumerate(oldedges) for j in range(t-1)})
                else:
                    junctions=[j for j in range(r+1) if j!=ei+1]
                    transform=lambda j:j if j<=ei else j-1
                    nc=sorted({transform(j) for j in C})
                    oldedges=[j for j in range(r) if j!=ei]
                    target=construct('A',r-1,t,nc)
                    mapping={f'v{k}':f'v{i}' for k,i in enumerate(junctions)}
                    mapping.update({f'e{k}f{j}':f'e{i}f{j}' for k,i in enumerate(oldedges) for j in range(t-1)})
                results.append(check(src,target,f'A({r},{t},{C}) edge {ei} heavy={heavy}',cm,mapping))

for paths in [(1,1,1),(1,1,2),(1,2,1),(2,1,1),(1,1,3),(1,2,2),(2,2,1)]:
    r=sum(paths)+1;src=construct('B',r,2,paths=paths);jn=sum(paths)+3
    edgeoffset=[0,paths[0],paths[0]+paths[1]]
    for pi,length in enumerate(paths):
        for localedge in range(length):
            ei=edgeoffset[pi]+localedge;cm=1<<(jn+ei)
            if length>1:
                np=list(paths);np[pi]-=1;target=construct('B',r-1,2,paths=np)
                mapping={}
                for pj,newlength in enumerate(np):
                    for nj in range(newlength+1):
                        oldj=nj if pj!=pi or nj<=localedge else nj+1
                        mapping[f'p{pj}v{nj}']=f'p{pj}v{oldj}'
                newoffset=[0,np[0],np[0]+np[1]]
                for pj,newlength in enumerate(np):
                    for ej in range(newlength):
                        oldej=ej if pj!=pi or ej<localedge else ej+1
                        mapping[f'e{newoffset[pj]+ej}f0']=f'e{edgeoffset[pj]+oldej}f0'
            else:
                p2=(pi+1)%3;p3=(pi+2)%3
                junctions=[f'p{p2}v{j}' for j in reversed(range(paths[p2]+1))]+[f'p{p3}v{j}' for j in reversed(range(paths[p3]+1))]
                a_length=paths[p2];b_length=paths[p3];C=[0,a_length,a_length+1,a_length+b_length+1]
                target=construct('A',r-1,2,C)
                mapping={f'v{k}':n for k,n in enumerate(junctions)}
                for k,ej in enumerate(reversed(range(paths[p2]))):mapping[f'e{k}f0']=f'e{edgeoffset[p2]+ej}f0'
                mapping[f'e{a_length}f0']=f'p{pi}v0'
                for k,ej in enumerate(reversed(range(paths[p3]))):mapping[f'e{a_length+1+k}f0']=f'e{edgeoffset[p3]+ej}f0'
            results.append(check(src,target,f'B{paths} edge {ei}',cm,mapping))
(ROOT/'models-contraction-checks.json').write_text(json.dumps(results,indent=2),encoding='utf-8')
print(f'{len(results)} contraction isomorphisms passed; {sum(x["compared_subset_ranks"] for x in results)} exact subset ranks compared.')
