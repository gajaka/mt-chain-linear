# Boot347: offline command association and fixed-window diagnostics

The historical log replay is complete. It establishes compatible time and
actuator-value associations for three of four recorded GEO perturbations, with
an explicit unresolved fourth association. It also shows why a complete-log
PASS cannot be reused as a certificate for each actuator step.

This is a separate exploratory application study in `mt-chain-linear`.
The subject is one recorded boot, without hardware access, a controller change,
an MT repair loop, or a newly proved PPG acceptance contract.

## Inputs and method

The [plan](PLAN.json) binds seven inputs, including the unchanged boot347 CSV,
serial log, historical numerical-check sources and archived report. Its hash is
`089a39726e531a6d7f686a9dd80cec4d88ba8f28ffefc13df4d022867bcb449c`.
Boot347 was named before looking at window outcomes. Earlier read-only source
reviews had already inspected some events and clock anchors. This is therefore
an exploratory analysis with frozen rules, not a held-out discovery experiment.

The [executor](replay.py) uses only Python's standard library. It does not import
the historical research modules. Original files under `~/Downloads/luces` are
read-only inputs. Every input hash is checked before and after execution.

The source CSV has 1,157 rows with strictly increasing timestamps and boot ID
347. The serial log has 10,961 physical lines. The registered tolerant prefix
grammar extracts 10,852 timestamped records, including 23 physical lines that
contain multiple prefixes. Fourteen embedded prefixes directly follow truncated
alphanumeric text and would be missed by a word-boundary parser. Small backwards
uptime interleavings are retained in source order, rather than silently sorted.

Analysis begins at the first explicit SNTP synchronization. It cuts a segment
whenever an adjacent parsed uptime gap exceeds 30 seconds or decreases by more
than one second. All resulting segments and all recorded GEO perturbations are
reported. Segment choice does not use certificate outcomes.

## Clock correspondence is empirical

Fifty-eight spectrum records carry a plausible Unix epoch. Their observed
offsets give:

```text
sensor epoch - ESP uptime seconds

minimum: 1783816405.569
maximum: 1783816406.579
median:  1783816406.089
spread:              1.010 seconds
```

The SNTP record at raw physical line 462 gives a coarse offset of
`1783816406.309`, inside that envelope. The source's `SPECTRUM received` fields
are recorded literally; in these messages the plausible epoch is in the field
printed as `valid`, while `time` is zero.

This is observed clock compatibility, not a proved latency bound or a verified
interpretation of CSV sampling time. Sensor acquisition, message receipt,
controller state and CSV writing can occur at different times. No extra timing
tolerance was tuned to make actuator values agree.

For each segment, rows are selected only when their CSV timestamps fall inside
the segment for every offset in the observed envelope. This condition is
conditional on that empirical envelope; it does not turn it into a universal
clock guarantee. See [CLOCK.json](evidence/attempt-002/CLOCK.json).

## Capture coverage and the longest segment

There are **23 observed gaps above 30 seconds**, yielding 24 segments. A gap is
a gap in the captured serial evidence, not proof that the controller stopped.
The original CSV remains a separate, much denser data record.

Only 59 of the 1,157 CSV row timestamps lie inside those serial segments under
the chosen empirical rule. The other rows are retained in the input and are
unassigned by this association rule; they are not deleted or called invalid.

The longest segment is selected by duration:

| Item | Value |
| --- | --- |
| Raw physical lines | 462 through 4922, ending before the next embedded record on line 4922 |
| Uptime range | 9,691 through 489,741 ms |
| Duration | 480.05 seconds |
| Assigned CSV physical lines | 2 through 29: 28 data rows |
| Night rows eligible for OBS/MRG | 27 |
| Logged sent actuator commands | 59 |

The first CSV row is an initialization-like row with elevation 45 and PWM 0.
It is retained and does not enter the night/overlap filters. There is no claim
that this segment includes every physical event: no observed large gap is
weaker than complete capture.

## All four recorded GEO perturbations

Each recorded GEO event has a following sent-command record and Hue record in
the same segment, within the fixed five-second association limit. PWM and CCT
payloads agree. These are logged command/acknowledgement values, not an
independent proof of the physical lamp response.

| GEO raw line | Sent line | Hue line | Sent PWM / CCT | First CSV row after the empirical event interval |
| ---: | ---: | ---: | --- | --- |
| 5569 | 5572 | 5573 | 24% / 2200 K | Physical row 329: 24% / 2200 K |
| 6139 | 6142 | 6143 | 26% / 2200 K | Physical row 508: 26% / 2200 K |
| 6321 | 6324 | 6325 | 24% / 2200 K | Physical row 665: 24% / 2200 K |
| 6386 | 6388 | 6389 | 24% / 2200 K | Physical row 666: 18% / 2200 K |

For the last event, the nearby row with matching 24% PWM is row 665, whose
timestamp is **before** that event under the entire observed offset envelope:

```text
GEO at line 6321: empirical epoch [1783827822.080, 1783827823.090]
CSV row 665:                     1783827829, PWM 24%, CCT 2200 K
GEO at line 6386: empirical epoch [1783827830.100, 1783827831.110]
CSV row 666:                     1783827847, PWM 18%, CCT 2200 K
```

A nearest-matching-value rule could incorrectly associate the already recorded
row 665 with the later command. The time-aware output preserves its BEFORE
relationship instead. It does not diagnose a controller error from this
disagreement.

The final two GEO events occur in one 46.95-second serial segment with six
sent commands and only three CSV rows (physical rows 664 through 666). There
are insufficient observations to isolate every command's effect. The first
two GEO-containing segments also have no assigned CSV rows strictly inside
their short captured intervals; their compatible later rows lie beyond those
intervals. Missing intervening commands and timestamp semantics remain open.

Full associations are in [GEO_JOINS.json](evidence/attempt-002/GEO_JOINS.json);
[COMMANDS.json](evidence/attempt-002/COMMANDS.json) retains all 127 observed sent
commands after synchronization, not just four favorable examples.

## Existing numerical checks on all segments

The same historical formula and threshold is recomputed on each segment's
fixed row list. Changing the input window changes what the statistic describes;
these outputs are **window diagnostics**, not an automatic restriction or reuse
of the original full-log certificate. N/A is retained as unavailable evidence.

| Check | Existing eligibility and predicate |
| --- | --- |
| OBS | At least 20 rows with elevation below -3; any population channel std above 2 |
| MRG | Same night filter/minimum; maximum channel std divided by the floored minimum std exceeds 1 |
| DATL | At least 10 rows in closed [-4,0]; positive-lux fraction above 0.3 and maximum sample channel std above 1 |
| C14 | At least 5 rows in open (-4,-2); every row has spectral sum above 10 and geometry kappa below 100 |
| C19 | At least 10 rows in open (-5,10); sample cloud-cover std below 20 |
| GEN | At least 60 rows in open (-3,8); signed velocity cosine above 0, with the original thirds and nonzero-norm rule |

All six checks pass when recomputed over the complete boot. That does not
supply each short segment with the samples required by its own check.

| Check | PASS segments | FAIL segments | N/A segments |
| --- | ---: | ---: | ---: |
| OBS | 1 | 0 | 23 |
| MRG | 1 | 0 | 23 |
| DATL | 0 | 0 | 24 |
| C14 | 0 | 0 | 24 |
| C19 | 1 | 0 | 23 |
| GEN | 0 | 0 | 24 |

The longest segment passes OBS (`max_std = 26.8947549973`, 9 responsive channels)
and MRG (`max_snr = 29.3532129606`). Its other four checks are N/A. A later
225.38-second segment has 13 assigned CSV rows and passes C19. Every
GEO-containing segment is N/A for all six checks. These are insufficiency
results, not evidence that the controller violated those predicates.

The historical C5 is excluded as a discriminating upper-bound check: its source
first filters `geo_kappa < 100`, then checks that the remaining maximum is below
200 (`cert_runner/certs/dynamics.py:65-72`). That filtered maximum cannot test
the advertised bound over all original observations. The source was not changed.

## Consequences for PPG certification

The data support reconstruction of observed commands, their reported payloads,
capture boundaries and some eligible numerical diagnostics. They do not provide
a complete per-command certification journal.

In particular:

- A full-boot GEN value (here about 0.99817) cannot be substituted for a local
  GEN test lacking its 60 eligible rows. GEN also recomputes its three chunks
  when the window changes; no stable-reuse theorem is supplied here.
- N/A cannot justify acceptance under a contract requiring that predicate.
  This observation does not claim a newly implemented or proved PPG policy.
- These six historical screens are distinct from the current formal local-plan
  family of eight indexed checks. The latter needs coupling-derived inputs and
  explicit protected observations; it is not instantiated by labeling these
  six outputs as its certificates.
- No physical causal effect, permanent parameter repair, PPG-guided decision,
  sparse-check saving or probabilistic MT bound follows from this replay.

The earlier measured five-candidate coupling repair remains its own verified
snapshot example. This study adds a bounded examination of the evidence needed
to interpret actual controller-command logs.

## Reproduction and verification

From the `mt-chain-linear` root, choose a new output directory:

```sh
python3 experiments/luces-log-replay/replay.py \
  --output experiments/luces-log-replay/evidence/attempt-new
```

The saved successful run is [attempt-002](evidence/attempt-002/RESULT.json).
Its output and error streams are retained under `attempt-002-logs`.
The first executor version tried to parse every CSV field as a float and
stopped on the string `NIGHT` before serial or diagnostic analysis. Its source
is preserved under `provenance/replay-v1.py` and its failed attempt has a
[failure record](evidence/attempt-001/FAILURE.json). The correction reads only
the explicitly needed numeric columns; source inputs and frozen plan stayed
unchanged. No failed attempt is counted as a scientific result.

The local mathematical core, copied PPGraph library, prior receipts, source
logs and original research scripts were not modified. This replay does not
add a Lean/PVS theorem or rerun an existing proof.
