/-
  PPGraphMoserTardosLogSpace.lean
  Algorithmic Lovász Local Lemma (Moser-Tardos)

  Layer 4, Part A: the probability space over which the log is
  genuinely random -- Alon-Spencer's C[v,t] construction (The
  Probabilistic Method, 4th ed., §5.7, p.84: an independent coin flip
  per (variable, time) pair). Formalized as ONE flat `Measure.infinitePi`
  over the combined index (t, v) : ℕ × V, rather than a nested product
  (a measure over `MTState S` per time step, then a further product
  over time) -- this matches the book's own indexing directly and
  avoids a second product-measure layer with its own independence
  bookkeeping.

  `Measure.pi` (Mathlib.MeasureTheory.Constructions.Pi) is NOT usable
  here: that file fixes `[Fintype ι]` as a section variable throughout
  (confirmed by reading the source directly), so it only builds FINITE
  products. The tool that actually works for an arbitrary index type
  (here ℕ × V, in general infinite) is `Measure.infinitePi`
  (Mathlib.Probability.ProductMeasure), built via the Ionescu-Tulcea
  theorem: `Measure.infinitePi μ` is a probability measure on `Π i, X i`
  whenever every `μ i` is one, for ANY index type `ι` -- no Fintype or
  Countable constraint needed on the public API.

  Builds on PPGraphMoserTardos.lean (VarSpaces, MTState). Deliberately
  stops at the sample space + the per-time-step projection
  (`freshState`) and its measurability -- constructing the actual
  random trajectory/log from this space, and showing THAT is
  measurable at each t, is a separate follow-up file.

  Author: Dragan Stosic, 2026.
-/

module

public import Mathlib.Tactic
public import Mathlib.Probability.ProductMeasure
public import PPGraph.MoserTardos.Process.Basic

@[expose] public section

set_option linter.unusedVariables false
set_option linter.unusedSectionVars false

open MeasureTheory

variable {V : Type} [DecidableEq V]

-- -------------------------------------------------------------------
-- The log-generating sample space
-- -------------------------------------------------------------------

/-- `MeasurableSpace (S.space v)`, registered as a genuine (searchable)
    instance rather than left as a bare structure field: `VarSpaces`
    already carries `measSpace : ∀ v, MeasurableSpace (space v)`, but a
    structure FIELD is not itself found by typeclass search -- Lean
    needs an actual `instance` before it will use it automatically to
    resolve `MeasurableSpace (S.space v)` (or `S.space p.2`, `.1`, ...)
    wherever it comes up, including under Mathlib's own Pi-space
    instance, which expects to find `∀ a, MeasurableSpace (X a)` by
    search, not by being handed the family explicitly. -/
instance instMeasurableSpaceSpace (S : VarSpaces V) (v : V) :
    MeasurableSpace (S.space v) :=
  S.measSpace v

/-- The sample space underlying a genuinely random log: one independent
    draw per (time step, variable) pair -- Alon-Spencer's C[v,t], p.84.
    Flat over `ℕ × V` (see file docstring for why, over the nested
    alternative).

    Declared `abbrev`, not `def`: a plain `def` is opaque to typeclass
    search, so Lean could not see through it to find
    `MeasurableSpace (∀ p, S.space p.2)` via `instMeasurableSpaceSpace`
    + Mathlib's generic `MeasurableSpace.pi` -- confirmed by an actual
    compile error (`failed to synthesize ... MeasurableSpace (LogSpace S)`)
    when this was a `def`. As an `abbrev` it unfolds transparently
    during search, giving ONE canonical derivation path (no separately
    -declared, possibly-mismatched second instance needed). -/
abbrev LogSpace (S : VarSpaces V) : Type := ∀ p : ℕ × V, S.space p.2

/-- `MTState S = ∀ v, S.space v` (Layer 1, PPGraphMoserTardos.lean) is
    a plain `def` there, not an `abbrev` -- opaque to search the same
    way `LogSpace` was above, but that file is out of scope to change
    here. Unlike `LogSpace`, we cannot make it transparent, so its
    Pi-measurable-space instance must be declared explicitly. -/
noncomputable instance instMeasurableSpaceMTState (S : VarSpaces V) :
    MeasurableSpace (MTState S) :=
  MeasurableSpace.pi

/-- The per-coordinate measure at index (t, v): just variable v's own
    distribution, the same at every time t (the coin flips are
    identically distributed across time, only the variable governs the
    law -- matching the book, where C[v,t] ~ the same law as v itself
    for every t). -/
def μCoin (S : VarSpaces V) (p : ℕ × V) : Measure (S.space p.2) :=
  S.measure p.2

instance instIsProbabilityMeasureμCoin (S : VarSpaces V) (p : ℕ × V) :
    IsProbabilityMeasure (μCoin S p) :=
  S.isProb p.2

/-- The log measure: the infinite product of all the C[v,t], via
    Mathlib's Ionescu-Tulcea-backed `Measure.infinitePi`. -/
noncomputable def logMeasure (S : VarSpaces V) : Measure (LogSpace S) :=
  Measure.infinitePi (μCoin S)

instance instIsProbabilityMeasureLogMeasure (S : VarSpaces V) :
    IsProbabilityMeasure (logMeasure S) := by
  unfold logMeasure
  infer_instance

-- -------------------------------------------------------------------
-- Extracting the fresh state supplied at a given time step
-- -------------------------------------------------------------------

/-- The fresh state ω'_t used to supply resample values at time t:
    fix the time coordinate, read off every variable's draw. This is
    the bridge back to `MTState S` (Layer 1) and to `resample`
    (which every trajectory step calls with exactly this kind of
    fresh state as its second argument). -/
def freshState {S : VarSpaces V} (ω : LogSpace S) (t : ℕ) : MTState S :=
  fun v => ω (t, v)

/-- `freshState · t` is a measurable function of ω, for every fixed t:
    each variable's coordinate of the result is a plain Pi-evaluation
    at a fixed index `(t, v)`, and a Pi-valued function is measurable
    iff every one of its coordinate functions is
    (`measurable_pi_lambda`). This is the fact the random trajectory
    (a later file) will need at every step, to show the state it
    computes is itself a measurable function of ω. -/
theorem measurable_freshState {S : VarSpaces V} (t : ℕ) :
    Measurable (fun ω : LogSpace S => freshState ω t) := by
  apply Measurable.of_eval
  intro v
  exact measurable_pi_apply (t, v)

-- -------------------------------------------------------------------
-- Verification
-- -------------------------------------------------------------------

#check @LogSpace
#check @instMeasurableSpaceSpace
#check @μCoin
#check @instIsProbabilityMeasureμCoin
#check @logMeasure
#check @instIsProbabilityMeasureLogMeasure
#check @freshState
#check @measurable_freshState
