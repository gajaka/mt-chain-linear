# A barrier-position policy versus static bias

The preselected policy **does not beat the best static law** for any of the
tested sizes n = 2, 3, 4, 5. In every case, the valid constant law p = 1 is
strictly cheaper. This is a negative result for this particular policy, not
an impossibility result for barrier-dependent policies in general.

## What was compared

The process is the original least-failed bridge chain. Initialization is
uniform on every internal threshold and all four raw labels, in EVERY arm.
Only the repair distribution changes:

- static p: each mutable threshold is redrawn with probabilities
  ((1-p)/2, (1-p)/2, p), independently;
- barrier policy: use p = 1 when the zero-based least failure i equals the
  permanent barrier height F, and p = 0 when i > F.

The selected bridge's label remains uniform on the original four labels.
The fixed endpoints remain 2 and 0. The policy was written in
[PROTOCOL.md](PROTOCOL.md) before its outcomes were computed, and was not tuned.

## Results

Each number below is a decimal display of an exactly checked rational mean.
The cost is redraw count, excluding initialization, not elapsed program time.

| n | Uniform repair p = 1/3 | Static p = 2/3 | Static p = 1 | Barrier policy | Barrier excess over p = 1 |
|---|---:|---:|---:|---:|---:|
| 2 | 0.4333333333 | 0.4254385965 | 0.4166666667 | 0.4500000000 | 8.00% |
| 3 | 1.0956757703 | 0.9755741600 | 0.7847222222 | 0.8256845238 | 5.22% |
| 4 | 2.4263623808 | 1.8673473077 | 1.2737268519 | 1.2874079934 | 1.07% |
| 5 | 4.5248962544 | 2.9662979696 | 1.8086902006 | 1.9147007203 | 5.86% |

The decisive comparisons are rational, not rounded:

| n | Barrier mean | Static p = 1 mean | Exact positive difference |
|---|---|---|---|
| 2 | 9/20 | 5/12 | 1/30 |
| 3 | 27743/33600 | 113/144 | 4129/100800 |
| 4 | 221907941/172368000 | 2201/1728 | 2358191/172368000 |
| 5 | 63217133900515501/33016718085120000 | 37505/20736 | 3500119443415501/33016718085120000 |

The supplementary grid is p = k/12 for k = 0, ..., 12. Its best tested value
is p = 1 for each n. **No global optimum over the continuous interval [0,1]
has been certified.** It is unnecessary for the negative conclusion:

    inf_{0 <= p <= 1} E[T_static(p)] <= E[T_static(1)] < E[T_barrier].

Thus even a better, untested static value could only strengthen this comparison.
At n = 3, 4, 5 the policy improves on p = 2/3; comparing only against that
one bias would have given a misleading impression of adaptive advantage.

## Why the calculation is exact

There are 3^(n-1) * 2^n profile states: 12, 72, 432 and 2592. The three strong
raw labels have identical pass, selection, update and barrier behavior and
are grouped with mass 3/4; the weak label has mass 1/4. In particular, profile
states are not uniformly distributed at initialization.

`run.py` solves the finite absorbing chain over rational numbers, by strongly
connected components. `verify.py` is a separate, stdlib-only implementation.
It reconstructs all 36 original raw draws, including ignored endpoint draws,
and checks every rational Bellman equation:

    h(s) = 0                              on Good states
    h(s) = 1 + sum_t P(s,t) * h(t)         on active states

It also checks nonnegativity, probability normalization, the original
initialization, and that every state has a positive-probability path to Good.
For a finite chain the latter excludes closed active recurrent classes and
ensures absorption with finite mean; the Bellman solution is therefore the
expected remaining redraw count. The checked average is sum_s pi_uniform(s)h(s).
Two corrupted-certificate controls must be rejected.

These are executable rational certificates, **not new Lean or Nanoda proofs**.
The correspondence between this implementation and the Lean definitions was
reviewed; a SHA-256 binding identifies those definitions, but is not itself a
formal refinement proof. The sealed biased-resampling theorem only covers
p >= 2/3, so it is not used to justify the policy's p = 0 branch.

The older `/tmp/mtcheck/exact.py` uses floating-point iteration and ties its
initial distribution to its repair distribution. It is not the certificate
generator for this comparison.

## Reproduce

Verify the stored results with Python 3.9 or newer; no third-party package is
needed:

```sh
python3 -B experiments/barrier-guided-bias/verify.py
```

To regenerate, use Python with `python-flint` installed. Supply a fresh output
directory; existing evidence is never overwritten:

```sh
python3 -B experiments/barrier-guided-bias/run.py --output /tmp/barrier-bias-rerun
python3 -B experiments/barrier-guided-bias/verify.py --data /tmp/barrier-bias-rerun
```

The generator records its interpreter, library version, source hashes and
per-arm elapsed solve time. Solve times describe the calculation, not an
algorithmic speedup. Exact vectors and expectations are in
[evidence/RESULT.json](evidence/RESULT.json); the independent check is in
[evidence/VERIFICATION.json](evidence/VERIFICATION.json).

## Consequence

This policy supplies no reason to start a new formalization. The experiment
stops here, without a replacement policy, larger n, or new benchmark. It does
not show that no useful barrier-dependent policy exists, nor does it change
the sealed uniform or biased chain theorems. In particular it establishes
neither an all-n comparison, a practical PPG advantage, nor scientific novelty.
