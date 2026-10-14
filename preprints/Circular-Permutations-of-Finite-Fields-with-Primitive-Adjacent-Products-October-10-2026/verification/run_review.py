"""Replay the finite-field certificates. Python stdlib and a C++17 compiler suffice."""
from pathlib import Path
import argparse, hashlib, json, subprocess, sys, time, datetime
sys.dont_write_bytecode=True

ROOT=Path(__file__).resolve().parent
H=lambda p:hashlib.sha256(Path(p).read_bytes()).hexdigest()
def require(test,message):
    if not test:raise RuntimeError(message)

def main():
    parser=argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--compiler',default='g++',help='C++ compiler path, or zig executable')
    parser.add_argument('--work-directory',type=Path,default=ROOT/'run')
    args=parser.parse_args()
    work=args.work_directory.resolve();work.mkdir(parents=True,exist_ok=True)
    src=ROOT/'source';sys.path.insert(0,str(src))
    from strict_io import orders,parse_certificates,bind_replay,bind_fallback,bind_extra_counts,unique_json
    manifest=unique_json(ROOT/'MANIFEST.json')
    for name,meta in manifest['files'].items():
        p=ROOT/name
        require(p.is_file() and p.stat().st_size==meta['bytes'] and H(p)==meta['sha256'],'bundle hash differs: '+name)
    start=time.perf_counter()
    payload=unique_json(ROOT/'certificate_inputs.json')
    for name,content in payload.items():
        require(Path(name).name==name,'input basename differs')
        (work/name).write_bytes(content.encode('ascii'))
    expected=orders(work/'AUDITED_RESIDUAL_ORDERS.csv')
    rows=parse_certificates(work/'CERTIFICATES.tsv',expected)
    require({int(k):tuple(v) for k,v in unique_json(work/'SELECTED_ORDERS.json').items()}==expected,'order set differs')
    prior={int(k):v for k,v in unique_json(ROOT/'expected_reports.json').items()}
    bind_replay(prior,rows,work)
    bind_fallback(unique_json(work/'FALLBACK_RESULTS.json'),rows,work)
    zig=Path(args.compiler).name.lower() in ('zig','zig.exe')
    compiler=[args.compiler]+(['c++'] if zig else [])
    def compile_one(name):
        exe=work/(name+('.exe' if sys.platform=='win32' else '.bin'))
        subprocess.run(compiler+['-O2','-std=c++17',str(src/(name+'.cpp')),'-o',str(exe)],check=True)
        return exe
    verifier=compile_one('verify_field')
    order_reports=[]
    for name,outfile in [('independent_order_audit','INDEPENDENT_RESIDUAL_ORDERS.csv'),
                         ('audit_residual_orders','AUDITED_RESIDUAL_ORDERS.csv')]:
        exe=compile_one(name)
        folder=work/name;folder.mkdir(exist_ok=True)
        command=[str(exe)]+([str(work/'AUDITED_RESIDUAL_ORDERS.csv')] if name=='audit_residual_orders' else [])
        cp=subprocess.run(command,cwd=folder,check=True,capture_output=True,text=True)
        require((folder/outfile).read_bytes().replace(b'\r\n',b'\n')==(work/'AUDITED_RESIDUAL_ORDERS.csv').read_bytes(),'residual catalogue differs: '+name)
        order_reports.append({'algorithm':name,'report':json.loads(cp.stdout),'all_six_columns_equal':True})
    reports={};counts={}
    for index,(q,row) in enumerate(sorted(rows.items()),1):
        cp=subprocess.run([str(verifier),f'field_{q}.tsv',str(q),str(row['p']),str(row['degree']),'5000000'],cwd=work,check=True,capture_output=True,text=True)
        d=json.loads(cp.stdout)
        receipt=unique_json(work/'EXTRA_COUNTER_USAGE_verifier.json')
        require(receipt=={'implementation':'verifier','q':q,'checks_completed':d['extra_checks'],'allowance':5000000},'extra receipt differs')
        d['uncovered_sha256']=H(work/row['uncovered_file']);d['extra_sha256']=H(work/row['extra_file'])
        require(d==prior[q],'field result differs: '+str(q))
        reports[q]=d;counts[q]=d['extra_checks']
        if index%400==0 or index==len(rows):print(f'{index}/{len(rows)} fields: PASS',flush=True)
    bind_replay(reports,rows,work)
    require(bind_extra_counts(counts,reports)==1302,'additional count differs')
    cp=subprocess.run([sys.executable,'-B',str(src/'verify_fallback.py'),str(work)],check=True,capture_output=True,text=True)
    fallback=json.loads(cp.stdout)
    require(fallback=={'status':'PASS','instances':31,'positive_cycles':30,'accepted_negative':1},'fallback result differs')
    result={'status':'PASS','fields':len(rows),'nonzero_offsets':sum(q-1 for q in rows),
            'compact_positive_offsets':sum(d['covered'] for d in reports.values()),'fallback':fallback,
            'extra_checks':sum(counts.values()),'order_replays':order_reports,
            'elapsed_seconds_including_compile_and_order_replays':time.perf_counter()-start,
            'finished_utc':datetime.datetime.now(datetime.timezone.utc).isoformat()}
    (work/'RESULT.json').write_text(json.dumps(result,indent=2),encoding='utf-8')
    (work/'FIELD_REPORTS.json').write_text(json.dumps(reports,indent=2),encoding='utf-8')
    print(json.dumps(result,indent=2),flush=True)

if __name__=='__main__':main()
