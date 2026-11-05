import itertools, json, sys
from pathlib import Path
import numpy as np
from scipy import sparse
from scipy.optimize import linprog

out=Path(sys.argv[1]); out.mkdir(parents=True,exist_ok=True)
T=list(itertools.product(range(3),repeat=3))
L=list(itertools.product(range(2),repeat=2))
keys=[a+b for a in T for b in L]
ix={k:j for j,k in enumerate(keys)}
def passes(a,b,r): return a==b if r else b<=a
rows=[]; stencils=[]; components=[]
for x in itertools.product(range(3),repeat=6):
 for r in itertools.product(range(2),repeat=5):
  if not passes(x[0],x[1],r[0]) or not passes(x[1],x[2],r[1]) or passes(x[2],x[3],r[2]): continue
  comp=[]
  for k in range(4):
   d={ix[(x[k],x[k+1],x[k+2],r[k],r[k+1])]:36}
   for a,b,z in itertools.product(range(3),range(3),range(2)):
    xx=list(x);rr=list(r);xx[2]=a;xx[3]=b;rr[2]=z
    q=ix[(xx[k],xx[k+1],xx[k+2],rr[k],rr[k+1])]
    d[q]=d.get(q,0)-(1 if z else 3)
   comp.append(d)
  d={}
  for c in comp:
   for j,v in c.items():d[j]=d.get(j,0)+v
  d={j:v for j,v in d.items() if v}
  rows.append(d);stencils.append([x,r]);components.append(comp)
ri=[];ci=[];vs=[]
for i,d in enumerate(rows):
 for j,v in d.items():ri.append(i);ci.append(j);vs.append(v)
A=sparse.csr_matrix((vs,(ri,ci)),shape=(len(rows),len(keys)),dtype=float)
print('Shape',A.shape,'nnz',A.nnz,flush=True)
res=linprog(np.zeros(len(keys)),A_ub=-A,b_ub=-np.ones(len(rows))*36,bounds=[(None,None)]*len(keys),method='highs')
summary={'rows':len(rows),'variables':len(keys),'nonzeros':A.nnz,'status':res.status,'message':res.message,'scope':'homogeneous bulk width-2 profile table only'}
print(summary,flush=True)
if res.success:
 summary['minimum_raw_drift']=float((A@res.x).min()/36)
 (out/'primal.json').write_text(json.dumps(dict(zip(map(str,keys),map(float,res.x))),indent=2))
else:
 eq=sparse.vstack([A.T,sparse.csr_matrix(np.ones((1,A.shape[0])))],format='csr')
 rhs=np.r_[np.zeros(len(keys)),1.]
 dual=linprog(np.zeros(len(rows)),A_eq=eq,b_eq=rhs,bounds=(0,None),method='highs')
 summary['dual_status']=dual.status;summary['dual_message']=dual.message
 if dual.success:
  support=np.flatnonzero(dual.x>1e-9)
  summary['dual_support']=len(support);summary['dual_residual']=float(np.abs(A.T@dual.x).max())
  record=[]
  for k in support:record.append({'row':int(k),'stencil':stencils[k],'weight_float':float(dual.x[k]),'coefficients':rows[k],'components':components[k]})
  (out/'dual-float.json').write_text(json.dumps(record,indent=2))
  np.save(out/'dual-matrix.npy',np.c_[A[support].toarray().T,np.zeros(len(keys))])
 print('dual',dual.status,dual.message,flush=True)
(out/'SUMMARY.json').write_text(json.dumps(summary,indent=2)+'\n')
