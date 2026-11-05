import json, sys, math, functools
from pathlib import Path
from fractions import Fraction
from flint import fmpq_mat
out=Path(sys.argv[1]); raw=json.loads((out/'dual-float.json').read_text());m=len(raw)
A=[[int(row['coefficients'].get(str(j),0)) for row in raw]+[0] for j in range(108)]
A += [[1]*m+[1]]
rr, rank=fmpq_mat(A).rref()
print('rref rank',rank,'support',m,flush=True)
w=[None]*m
for i in range(rank):
 pivot=next((j for j in range(m) if rr[i,j]),None)
 if pivot is None:
  assert not rr[i,m];continue
 assert all(not rr[i,j] for j in range(m) if j!=pivot),'nonunique'
 w[pivot]=Fraction(str(rr[i,m]))
assert all(v is not None and v>=0 for v in w)
assert sum(w)==1
for j in range(108):assert sum(wk*int(row['coefficients'].get(str(j),0)) for wk,row in zip(w,raw))==0
coeffs=[[sum(wk*int(row['components'][k].get(str(j),0)) for wk,row in zip(w,raw))/36 for j in range(108)]for k in range(4)]
assert all(sum(coeffs[k][j]for k in range(4))==0 for j in range(108))
for wk,row in zip(w,raw):row['weight_exact']=str(wk)
record={'support':raw,'window_functionals':[[str(v)for v in ck]for ck in coeffs],'exact_verified':True,'integer_row_denominator':36,'positive_weight_sum':'1','homogeneous_weighted_drift_coefficient_sum':'0'}
(out/'DUAL_EXACT.json').write_text(json.dumps(record,indent=2)+'\n')
print('verified exact91-row positive dual; maximum denominator digits',max(len(str(v.denominator))for v in w))
print('positive weights',sum(v>0 for v in w),'sum',sum(w))
for k,c in enumerate(coeffs):print('functional',k,'nonzero',sum(v!=0 for v in c),'abs_sum',sum(abs(v)for v in c))
