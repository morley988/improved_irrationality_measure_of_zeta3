"""Replay the finite certificates for the manuscript's mu(zeta(3)) < 4.974 theorem."""
import hashlib
import json
import subprocess
import sys
from fractions import Fraction as Q
from pathlib import Path

if not __debug__:
    raise RuntimeError('Run without Python optimization flags; certificate assertions must be enabled.')
root=Path(__file__).resolve().parent
out=root/'replayed'
out.mkdir(exist_ok=True)
arith=out/'arithmetic_certificate.json'
cells=out/'arithmetic_cells.tsv'
analytic=out/'analytic_certificate.json'
subprocess.run([sys.executable,str(root/'exact_arithmetic.py'),
                '--s1','2/25','--s2','8/25','--delta','51/50','--Q','500',
                '--output',str(arith),'--cells',str(cells)],check=True,cwd=root)
a=json.loads(arith.read_text())
expected=json.loads((root/'certificates/arithmetic_certificate.json').read_text())
assert Q(a['arithmetic_upper'])==Q(expected['arithmetic_upper'])
assert hashlib.sha256(cells.read_bytes()).hexdigest()==expected['cell_sha256']==a['cell_sha256']
# Check coverage and every exact affine-cell area independently of the integrator.
prev=Q(1,500);total=0;count=0;scale=a['scale']
for line in cells.read_text().splitlines():
    l,r,c,d,k=line.split();l,r,c,d=map(Q,(l,r,c,d));k=int(k)
    assert l==prev and r>l
    area=(r-l)*(c+d*(l+r)/2)
    assert Q(k,scale)>=area and Q(k-1,scale)<area
    total+=k;count+=1;prev=r
assert prev==Q(67,25) and count==a['accepted_cells']
assert Q(total,scale)+Q(51,6250)==Q(a['arithmetic_upper'])
subprocess.run([sys.executable,str(root/'certify_analytic.py'),
                '--arithmetic',str(arith),'--output',str(analytic)],check=True,cwd=root)
b=json.loads(analytic.read_text())
assert b['passed']
slack=Q(b['simple_decisive_margin_lower'])
endpoint_upper=Q(b['simple_envelope_at_T']['upper'])
assert slack>0 and Q(b['simple_envelope_at_T']['lower'])>0
lam=Q(17,25);T=Q(17,125)
bound=lam*endpoint_upper/(slack+T*endpoint_upper)
assert bound==Q(b['transfer_bound_rational']) and bound<Q(2487,500)
print('\nPASS: finite certificate inequalities for the manuscript theorem.')
print('Certified rational upper bound:',bound)
print('Decimal comparison:',float(bound),'< 4.974')
print('These finite checks accompany the mathematical proofs in the report; they are not a proof-assistant formalization.')
