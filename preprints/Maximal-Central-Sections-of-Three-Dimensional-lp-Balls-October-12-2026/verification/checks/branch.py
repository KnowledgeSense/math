#!/usr/bin/env python3
"""Exact branch checker; exact binary-rational interpretation of 17-digit endpoints."""
from fractions import Fraction as F
from pathlib import Path
from datetime import datetime,timezone
import re,json,hashlib
root=Path(__file__).resolve().parents[1]/'components/four-to-six';log=root/'logs/branch_interval_probe.stdout';text=log.read_text();rows=re.findall(r'derivative (\d+)\s+\[([^,]+), ([^\]]+)\]',text);assert len(rows)==200 and sorted(int(j) for j,_,_ in rows)==list(range(200));worst=F(-100)
for j,lo,hi in rows:
 a,b=map(lambda x:F.from_float(float(x)),(lo,hi));assert a<=b<F(-1,50);worst=max(worst,b)
ends={}
for j,lo,hi in re.findall(r'endpoint (\d+)/100\s+\[([^,]+), ([^\]]+)\]',text):ends[int(j)]=[F.from_float(float(x)) for x in (lo,hi)]
assert set(ends)=={499,500};assert F(299,10**6)<ends[499][0]<=ends[499][1]<F(303,10**6);assert F(-67,10**6)<ends[500][0]<=ends[500][1]<F(-64,10**6)
out={'status':'PASS, exact branch comparison','timestamp_utc':datetime.now(timezone.utc).isoformat(),'all_200_derivative_upper_below':'-1/50','endpoint_499_100_enclosed_by':['299/1000000','303/1000000'],'endpoint_5_enclosed_by':['-67/1000000','-64/1000000'],'worst_derivative_upper_exact':str(worst),'producer_sha256':hashlib.sha256((root/'code/probe-branch-intervals.cpp').read_bytes()).hexdigest(),'log_sha256':hashlib.sha256(log.read_bytes()).hexdigest(),'checker_sha256':hashlib.sha256(Path(__file__).read_bytes()).hexdigest()};(root.parents[1]/'results/branch.json').write_text(json.dumps(out,indent=2));print(json.dumps(out,indent=2))
