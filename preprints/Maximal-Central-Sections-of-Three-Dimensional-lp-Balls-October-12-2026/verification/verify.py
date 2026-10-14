from pathlib import Path
import subprocess,sys,json,hashlib
ROOT=Path(__file__).resolve().parent
manifest=json.loads((ROOT/'MANIFEST.json').read_text(encoding='utf-8'))
for row in manifest['files']:
    data=(ROOT/row['path']).read_bytes()
    assert len(data)==row['bytes']
    assert hashlib.sha256(data).hexdigest()==row['sha256'],row['path']
out=ROOT/'results';out.mkdir(exist_ok=True)
tasks=[
('near2_local',['components/near-two-and-large-exponents/logs/near2_local_full','--out','results/near2_local.json','--mutations']),
('near2_complement',['components/near-two-and-large-exponents/logs/near2_complement_full','--out','results/near2_complement.json','--mutations']),
('c4',[]),
('transition',['components/four-to-six','results/transition.json']),
('branch',[]),
('bridge_local',['components/near-two-and-large-exponents/logs/bridge_local_full','--out','results/bridge_local.json','--mutations']),
('bridge_complement',['components/near-two-and-large-exponents/logs/bridge_complement_full','--out','results/bridge_complement.json','--mutations']),
('tail',['components/near-two-and-large-exponents','results/tail.json']),
]
for name,args in tasks:
    job=subprocess.run([sys.executable,'-X','utf8',str(ROOT/'checks'/(name+'.py')),*args],cwd=ROOT,capture_output=True,text=True,encoding='utf-8')
    (out/(name+'.stdout')).write_text(job.stdout,encoding='utf-8')
    (out/(name+'.stderr')).write_text(job.stderr,encoding='utf-8')
    if job.returncode:
        print(job.stdout);print(job.stderr);raise SystemExit(job.returncode)
    result=json.loads((out/(name+'.json')).read_text(encoding='utf-8'))
    assert 'PASS' in result['status']
    print(name+': '+result['status'],flush=True)
print('All selected saved certificates satisfy the exact checks.')
