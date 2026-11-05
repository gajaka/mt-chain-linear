"""Finite window-potential LP proposals and exact basis certificates.

The external numerical solver selects a basis only. Exact primal/dual checks
below and the separately implemented stdlib verifier establish the result.
"""
import argparse
from collections import Counter
import hashlib
from itertools import product
import json
from pathlib import Path
import platform
import sys
import time

import flint
from flint import fmpq, fmpq_mat
import highspy
import numpy as np
import scipy
from scipy.sparse import coo_matrix, save_npz

ROOT = Path(__file__).resolve().parents[1]


def sha(path):
    return hashlib.sha256(Path(path).read_bytes()).hexdigest()


def save(path, value):
    with Path(path).open('x') as f:
        json.dump(value, f, indent=2, sort_keys=True)
        f.write('\n')


def first_failure(x, weak):
    return next((i for i, w in enumerate(weak)
                 if (x[i] != x[i+1] if w else x[i] < x[i+1])), None)


def key(i, x, w, width):
    return i, tuple(x[i:i+width+1]), tuple(w[i:i+width])


def model(n, width):
    assert 1 <= width <= n and n >= 2
    states = [(tuple((2,)+xs+(0,)), tuple(ws))
              for xs in product(range(3), repeat=n-1)
              for ws in product(range(2), repeat=n)]
    index = {state: j for j, state in enumerate(states)}
    keys = sorted({key(i, x, w, width) for x, w in states
                   for i in range(n-width+1)})
    columns = {k: j+1 for j, k in enumerate(keys)}
    variables = [{'kind': 'offset'}] + [
        {'kind': 'window', 'i': i, 'thresholds': list(xs), 'weak': list(ws)}
        for i, xs, ws in keys]
    selected = [first_failure(x, w) for x, w in states]
    features = [([0]+[columns[key(i,x,w,width)] for i in range(n-width+1)])
                if fail is not None else []
                for (x,w), fail in zip(states,selected)]
    objective = [0]*len(variables)
    denominator = 3**(n-1)*4**n
    total_mass = 0
    rows, rhs, descriptions = [], [], []
    for s, ((x,w), chosen, phi) in enumerate(zip(states,selected,features)):
        mass = 3**(n-sum(w))
        total_mass += mass
        for j in phi:
            objective[j] += mass
        if chosen is None:
            continue
        coefficients = Counter({j:36 for j in phi})
        total_draw_mass = 0
        for a,b,t in product(range(3),range(3),range(2)):
            xx, ww = list(x), list(w)
            if chosen > 0:
                xx[chosen] = a
            if chosen+1 < n:
                xx[chosen+1] = b
            ww[chosen] = t
            multiplicity = 1 if t else 3
            total_draw_mass += multiplicity
            target = index[(tuple(xx),tuple(ww))]
            for j in features[target]:
                coefficients[j] -= multiplicity
        assert total_draw_mass == 36
        rows.append({j:int(v) for j,v in coefficients.items() if v})
        rhs.append(36)
        descriptions.append((s,'drift'))
        rows.append({j:1 for j in phi})
        rhs.append(0)
        descriptions.append((s,'nonnegative'))
    assert total_mass == denominator
    rr,cc,vv = [],[],[]
    for k,row in enumerate(rows):
        for j,value in row.items():
            rr.append(k); cc.append(j); vv.append(value)
    matrix = coo_matrix((np.array(vv,dtype=np.int64),(rr,cc)),
                        shape=(len(rows),len(variables))).tocsr()
    return states, variables, rows, rhs, descriptions, objective, denominator, matrix


def rational_dot(row, values):
    return sum((values[j]*c for j,c in row.items()),fmpq(0))


def main():
    parser = argparse.ArgumentParser()
    parser.add_argument('--n',type=int,required=True)
    parser.add_argument('--width',type=int,required=True)
    parser.add_argument('--out',type=Path,required=True)
    parser.add_argument('--time-limit',type=float,default=180)
    parser.add_argument('--solver',choices=('simplex','ipm'),default='simplex')
    args = parser.parse_args()
    out = args.out.resolve()
    out.mkdir(parents=True,exist_ok=False)
    start = time.monotonic()
    inputs = {'n':args.n,'width':args.width,
              'spec_sha256':sha(ROOT/'SPEC.md'), 'script_sha256':sha(__file__),
              'python':sys.executable,'python_version':platform.python_version(),
              'numpy':np.__version__,'scipy':scipy.__version__,
              'highspy':highspy.Highs().version(),'python_flint':flint.__version__,
              'command':sys.argv}
    save(out/'INPUTS.json',inputs)
    data = model(args.n,args.width)
    states,variables,rows,rhs,descriptions,objective,denominator,matrix = data
    save_npz(out/'matrix.npz',matrix)
    build_seconds = time.monotonic()-start
    lp = highspy.HighsLp()
    lp.num_col_,lp.num_row_ = matrix.shape[1],matrix.shape[0]
    lp.col_cost_ = np.array(objective,dtype=float)/denominator
    lp.col_lower_ = np.full(lp.num_col_,-highspy.kHighsInf)
    lp.col_upper_ = np.full(lp.num_col_,highspy.kHighsInf)
    lp.row_lower_ = np.array(rhs,dtype=float)
    lp.row_upper_ = np.full(lp.num_row_,highspy.kHighsInf)
    lp.a_matrix_.format_ = highspy.MatrixFormat.kRowwise
    lp.a_matrix_.start_ = matrix.indptr
    lp.a_matrix_.index_ = matrix.indices
    lp.a_matrix_.value_ = matrix.data.astype(float)
    solver = highspy.Highs()
    for name,value in [('output_flag',False),('solver',args.solver),('threads',1),
                       ('time_limit',args.time_limit),
                       ('primal_feasibility_tolerance',1e-9),
                       ('dual_feasibility_tolerance',1e-9)]:
        assert solver.setOptionValue(name,value) == highspy.HighsStatus.kOk
    assert solver.passModel(lp) == highspy.HighsStatus.kOk
    solver.run()
    status = solver.getModelStatus()
    solution,basis = solver.getSolution(),solver.getBasis()
    save(out/'NUMERICAL.json',{'status':str(status),'objective':solver.getObjectiveValue(),
                              'primal':list(solution.col_value),
                              'row_dual':list(solution.row_dual),
                              'column_basis':[str(s) for s in basis.col_status],
                              'row_basis':[str(s) for s in basis.row_status]})
    result={'n':args.n,'width':args.width,'status':'UNKNOWN',
            'profile_states':len(states),'variables':len(variables),'rows':len(rows),
            'build_seconds':build_seconds,'numeric_seconds':solver.getRunTime(),
            'numerical_status':str(status),'numerical_objective':solver.getObjectiveValue(),
            'exact_primal':False,'exact_dual':False,'exact_optimum':False,
            'lean_runs':0,'nanoda_runs':0}
    try:
        if status != highspy.HighsModelStatus.kOptimal:
            raise ValueError('Numerical solve not optimal; no infeasibility claim')
        basic_columns=[j for j,s in enumerate(basis.col_status)
                       if s==highspy.HighsBasisStatus.kBasic]
        tight_rows=[k for k,s in enumerate(basis.row_status)
                    if s!=highspy.HighsBasisStatus.kBasic]
        assert len(basic_columns)==len(tight_rows)>0
        assert all(abs(solution.col_value[j]) < 1e-7
                   for j,s in enumerate(basis.col_status)
                   if s!=highspy.HighsBasisStatus.kBasic)
        assert all(basis.row_status[k]==highspy.HighsBasisStatus.kLower for k in tight_rows)
        square=fmpq_mat([[int(rows[k].get(j,0)) for j in basic_columns] for k in tight_rows])
        exact=square.solve(fmpq_mat([[rhs[k]] for k in tight_rows]))
        primal=[fmpq(0) for _ in variables]
        for j,value in zip(basic_columns,exact.entries()):
            primal[j]=value
        dual_basic=square.transpose().solve(fmpq_mat([[objective[j]] for j in basic_columns]))
        dual={k:dual_basic[t,0]/denominator for t,k in enumerate(tight_rows)
              if dual_basic[t,0]}
        slacks=[rational_dot(row,primal)-b for row,b in zip(rows,rhs)]
        assert min(slacks)>=0, 'Reconstructed primal violates an exact row'
        assert min(dual.values())>=0, 'Reconstructed dual has negative weight'
        lhs=[fmpq(0) for _ in variables]
        for k,y in dual.items():
            for j,a in rows[k].items():
                lhs[j]+=a*y
        assert all(lhs[j]==fmpq(objective[j],denominator) for j in range(len(variables))), 'Dual column mismatch'
        primal_value=sum((v*c for v,c in zip(primal,objective)),fmpq(0))/denominator
        dual_value=sum((y*rhs[k] for k,y in dual.items()),fmpq(0))
        assert primal_value==dual_value,'Nonzero exact gap'
        support=[]
        for k,y in sorted(dual.items()):
            s,kind=descriptions[k]; x,w=states[s]
            support.append({'thresholds':list(x[1:-1]),'weak':list(w),
                            'kind':kind,'weight':str(y)})
        certificate={'n':args.n,'width':args.width,'variables':variables,
                     'primal':[str(x) for x in primal],'dual':support,
                     'objective':str(primal_value),'objective_denominator':denominator}
        save(out/'CERTIFICATE.json',certificate)
        result.update(status='EXACT_OPTIMUM',exact_primal=True,exact_dual=True,
                      exact_optimum=True,exact_objective=str(primal_value),
                      objective_per_n=str(primal_value/args.n),
                      dual_support=len(dual),basis_dimension=len(basic_columns),
                      minimum_primal_slack=str(min(slacks)),
                      certificate_sha256=sha(out/'CERTIFICATE.json'))
    except Exception as error:
        result['exact_reconstruction_error']=repr(error)
    result['input_hashes_unchanged']=(sha(__file__)==inputs['script_sha256'] and
                                    sha(ROOT/'SPEC.md')==inputs['spec_sha256'])
    result['elapsed_seconds']=time.monotonic()-start
    save(out/'RESULT.json',result)
    print(json.dumps(result,indent=2),flush=True)
    return 0 if result['exact_optimum'] else 2


if __name__=='__main__':
    sys.exit(main())
