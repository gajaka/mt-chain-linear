# Moser-Tardos resampling: linear cost and certificate complexity

A Lean formalization of Moser-Tardos (MT) resampling, probability and expected
cost, with a concrete chain whose expected redraw count is Theta(n). The main
case study separates actual process cost from the budgets available to
restricted drift certificates. Scientific novelty remains open for review.

For a first reading, start with the [process and linear-cost proof](REPORT.md),
then the [certificate separation](research/certificate-existence/README.md)
and the [literature questions](research/certificate-existence/LITERATURE.md).

## Main results

All costs count redraw operations, excluding initialization. Certificate
budgets mean `E_initial[V]/delta`, with positive drift scale delta.

| Result | Statement | Guide |
|---|---|---|
| Uniform chain | For n>=2, `n/18 <= E[T_n] <= 1054*n`, and `IsTheta` | [Process and proof](REPORT.md) |
| Coordinate-separable certificates | Explicit certificates for every n>=2; every certificate has exponential normalized initial budget | [Certificate study](research/certificate-existence/README.md) |
| One bridge per summand | Class inhabited for every n>=2; budget at least `n^2/1248` for n>=10 | [Certificate study](research/certificate-existence/README.md) |
| Window hierarchy (optional followup) | Seven exact finite optima across widths; a width-two all-length Omega(n^2) paper obstruction | [Window locality](research/window-locality/README.md) |
| Biased redraws (optional followup) | Static p=2/3 has Theta(n) cost under matching initialization; restricted history-dependent policies have linear upper bounds | [Biased study](research/biased-resampling/README.md) |

For the coordinate-separable class, the explicit upper budget is
`3*9^(n-2)+1`. Every certificate, for n>=4, has budget at least
`(5^(floor((n-4)/2)+1)-3)/36`. Both restricted classes are therefore nonempty;
these are not lower bounds over an assumed, possibly empty certificate class.
The optimal exponential rate is open. Quadratic attainment for the larger
one-bridge and width-two classes is not established.

## The chain and its probability law

There are n bridges with fixed endpoints X_0=2 and X_n=0. Internal thresholds
lie in {0,1,2}; each bridge has one of four raw labels. With zero-based indices,

```text
bridge i passes iff
    X_i = X_(i+1)       when R_i = 1 (weak),
    X_(i+1) <= X_i      otherwise (three strong labels).
```

All mutable coordinates start independently and uniformly. At each active
step, select the least failed bridge and independently redraw its mutable
endpoint thresholds and its own label. Other coordinates remain fixed.
There are 36 raw draws, with the unused draw ignored at a fixed endpoint.
See [Chain.lean](formal/mt/core/Chain.lean) and
[ChainKernel.lean](formal/mt/core/ChainKernel.lean).

The linear upper proof uses permanent barriers and the proved conditional
completion law of unretained coordinates through observation histories,
including rollback. Its expected-cost theorem is proved from the explicit
finite transition kernel. The current lower-bound proof uses the established
quadratic finiteness result.

For the canonical dependency path, endpoint failure marginals are 1/6 and
interior marginals are 5/12. Exact Shearer calculations put n=2,3 inside the
region, n=4 on its boundary, and n>=5 outside. This classification is a written
calculation, not a separate Lean theorem or a novelty argument.

## What a restricted certificate means

A certificate has V>=0, V=0 on Good states, and expected decrease at least
`delta>0` at every active full state. Only the fresh redraw is averaged.
Its budget is `E_initial[V]/delta`, under the same uniform law as the chain.
The permitted active-state scores are

```text
Coordinate-separable: c + sum_j f_j(X_j) + sum_i g_i(R_i).
One bridge per term: c + sum_i h_i(X_i, X_(i+1), R_i).
```

The global reset on Good states is part of both definitions. The obstruction
restricts potential shape; it does not exclude additive drift with arbitrary
nonseparable potentials. The chain's linear proof uses a different drift
obligation, justified by its conditional completion law.

The biased study changes threshold draws to `((1-p)/2,(1-p)/2,p)` while keeping
labels uniform. At static p=2/3 with matching biased product initialization,
`n/24 <= E[T] <= 3n-2`. Under the original uniform start, the upper bound is
`5n-4`. History-dependent failed-target selection and biases in [2/3,1] have
linear upper bounds, not an all-policy Theta(n) theorem. The certificate
obstruction is specific to the uniform law under which it is proved.

## Questions for independent review

1. **Does HLS Theorem 1.6, or another known MT theorem, imply O(n) for this
   exact event system, initialization, scheduler and redraw law?** Our scoped
   [literature comparison](research/certificate-existence/LITERATURE.md)
   excludes that particular HLS criterion for the canonical encoding when
   n>=5. The criterion exclusion is a written argument, not a Lean theorem.
2. **Is the nonvacuous exponential separation for restricted certificates
   already known?** The question includes the global Good reset and the
   full-state pointwise-drift requirement, not additive drift in general.

References and corrections are welcome. No priority or practical-superiority
claim is made.

## MT, HLS and probability theory

The [theory library](library/README.md) provides the general definitions and
conditional theorems used to study resampling systems:

| Area | Source |
|---|---|
| Product spaces, resampling, trajectories and initialization | [MT Process](library/MT/MoserTardos/Process/) |
| Probability, independence, witnesses and counting | [MoserTardos](library/MT/MoserTardos/) |
| Expected cost, convergence, termination and drift | [MT Bounds](library/MT/MoserTardos/Bounds/) |
| Local-lemma and Shearer criteria | [LLL](library/MT/LLL/), [Shearer](library/MT/Shearer/) |
| HLS probability, witness-DAG and budget arguments | [HLS](library/MT/HLS/) |
| Repair hazards and stable observable algebras | [Repair](library/MT/Repair/) |
| History-dependent MT and HLS selection | [Policy](library/MT/Integration/Policy/) |

[GenericMT.lean](library/GenericMT.lean) is the entry point for these theories
and their required definitions. Theorems retain their stated hypotheses.
The concrete chain has its own finite-kernel proof; the presence of the
general library does not assert a new instantiation or extend the chain's
bound to other processes.

## Verification and reproduction

| Part | Evidence |
|---|---|
| MT, HLS, Shearer, LLL, hazards and observable algebras | Lean build and source-inventory checks |
| Uniform chain and restricted-certificate results | Lean proofs; independent Nanoda replays of selected roots and their proof closures |
| Biased and history-dependent results | Lean proofs and raw proof-dependency audit; no new Nanoda replay |
| Finite window optima and local algebraic identity | Independent exact rational checks |
| Width-two all-length obstruction | Paper argument with internal review; not Lean/Nanoda |

One [fixed barrier policy](experiments/barrier-guided-bias/README.md) lost to
static p=1 for n=2,...,5 under common uniform initialization. This bounded
comparison does not exclude every possible barrier-dependent policy.

Pinned tools: Lean `leanprover/lean4:v4.35.0` and Mathlib
`56a005855ea17e0b0958f73ec801ae140b0a1679`.

```sh
lake exe cache get
make check
```

This builds the mathematical workspaces with warnings treated as errors,
checks source identities, and verifies the saved rational certificates.
It does not perform a fresh Nanoda replay. [TOOLING.md](TOOLING.md) describes
independent replay, the allowed axioms and the exact scope of each audit.
The whole project is not covered by a blanket second-kernel claim.
Project code and documentation are licensed under [MIT](LICENSE). See
[source and dependency notices](THIRD_PARTY_NOTICES.md) for external materials.
