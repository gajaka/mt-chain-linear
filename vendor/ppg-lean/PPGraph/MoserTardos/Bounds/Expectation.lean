/-
  PPGraphMoserTardosExpectation.lean
  Algorithmic Lovász Local Lemma (Moser-Tardos), Theorem 5.7.1 groundwork.

  Expectation/integration infrastructure for T_LOG, the number of
  resampling steps the Fix-It algorithm performs before converging.
  Builds on PPGraphMoserTardosCorrespondence.lean's `RunningUntil`
  ("the process genuinely still has a violation to fix at every step
  before t") and `randStep`/`realC` (PPGraphMoserTardosRandomTrajectory.lean).

  T_LOG is defined directly as a countable sum of indicators, one per
  candidate stopping time t: `RunningUntil P ω0 ω (t+1)` holds for
  EXACTLY the first T_LOG(ω) values of t (t = 0, ..., T_LOG(ω) - 1),
  since `RunningUntil` is antitone in its own argument
  (`RunningUntil (t+1) → RunningUntil t`, immediate from its own
  `∀ s < t, ...` shape) -- so counting how many t satisfy it IS T_LOG,
  with the countable-sum-of-indicators shape making both measurability
  (`Measurable.tsum`) and the E[T_LOG] = Σ Pr[still running]
  decomposition (`lintegral_tsum`) immediate from standard measure
  theory, no bespoke stopping-time machinery needed.

  Author: Dragan Stosic, 2026.
-/

module

public import PPGraph.MoserTardos.Witness.Correspondence
public import Mathlib.MeasureTheory.Constructions.Polish.Basic

@[expose] public section

set_option linter.unusedVariables false
set_option linter.unusedSectionVars false

open MeasureTheory Classical
open scoped ENNReal

variable {V : Type} [DecidableEq V]

-- -------------------------------------------------------------------
-- Section 1: measurability of "a genuine violation was fixed at step s"
-- and of RunningUntil itself
-- -------------------------------------------------------------------

/-- The event that the picked event at real step `s` was genuinely
    violated is measurable -- split by WHICH event `realC` picked
    (finitely many, ι a Fintype), each branch a measurable intersection
    of "realC picked exactly this event" and "the real state is bad for
    it" (the latter via the standing `hbad` hypothesis). -/
theorem measurableSet_violatedAt {S : VarSpaces V} {ι : Type} [Fintype ι] [DecidableEq ι] [Nonempty ι]
    (P : MTProcess S ι) (hbad : ∀ i, MeasurableSet (P.bad i)) (ω0 : MTState S) (s : ℕ) :
    MeasurableSet {ω : LogSpace S | (randStep P ω0 ω s).1 ∈ P.bad (realC P ω0 ω s)} := by
  have heq : {ω : LogSpace S | (randStep P ω0 ω s).1 ∈ P.bad (realC P ω0 ω s)} =
      ⋃ i : ι, ({ω : LogSpace S | realC P ω0 ω s = i} ∩
        {ω : LogSpace S | (randStep P ω0 ω s).1 ∈ P.bad i}) := by
    ext ω
    simp only [Set.mem_ofPred_eq, Set.mem_iUnion, Set.mem_inter_iff]
    constructor
    · intro h
      exact ⟨realC P ω0 ω s, rfl, h⟩
    · rintro ⟨i, hi, hmem⟩
      rw [hi]
      exact hmem
  rw [heq]
  refine MeasurableSet.iUnion (fun i => MeasurableSet.inter ?_ ?_)
  · let : MeasurableSpace ι := ⊤
    have hmeas : Measurable (fun ω : LogSpace S => realC P ω0 ω s) :=
      (measurable_pickFirstViolated P hbad).comp (measurable_randStep P hbad ω0 s).1
    exact hmeas (measurableSet_singleton i)
  · exact (measurable_randStep P hbad ω0 s).1 (hbad i)

/-- `RunningUntil P ω0 ω t` is measurable in `ω` -- a finite intersection
    (over `s < t`) of the single-step events above. -/
theorem measurableSet_runningUntil {S : VarSpaces V} {ι : Type} [Fintype ι] [DecidableEq ι] [Nonempty ι]
    (P : MTProcess S ι) (hbad : ∀ i, MeasurableSet (P.bad i)) (ω0 : MTState S) (t : ℕ) :
    MeasurableSet {ω : LogSpace S | RunningUntil P ω0 ω t} := by
  have heq : {ω : LogSpace S | RunningUntil P ω0 ω t} =
      ⋂ s ∈ Finset.range t, {ω : LogSpace S | (randStep P ω0 ω s).1 ∈ P.bad (realC P ω0 ω s)} := by
    ext ω
    simp only [RunningUntil, Set.mem_ofPred_eq, Set.mem_iInter, Finset.mem_range]
  rw [heq]
  exact Finset.measurableSet_biInter _ (fun s _ => measurableSet_violatedAt P hbad ω0 s)

-- -------------------------------------------------------------------
-- Section 2: T_LOG, the number of resampling steps
-- -------------------------------------------------------------------

/-- T_LOG(ω): the number of genuine resampling steps the process
    performs before converging, as a countable sum of 0/1 indicators --
    `RunningUntil P ω0 ω (t+1)` holds for exactly `t = 0, ..., T_LOG - 1`
    (it is antitone: `RunningUntil (t+1) → RunningUntil t` directly from
    the `∀ s < t` shape, so once false it stays false), so this tsum
    literally counts how many such `t` there are -- `⊤` (via the tsum
    diverging) exactly when the process never converges. -/
noncomputable def TLog {S : VarSpaces V} {ι : Type} [Fintype ι] [DecidableEq ι] [Nonempty ι]
    (P : MTProcess S ι) (ω0 : MTState S) (ω : LogSpace S) : ℝ≥0∞ :=
  ∑' t : ℕ, {ω' : LogSpace S | RunningUntil P ω0 ω' (t + 1)}.indicator (fun _ => 1) ω

theorem measurable_TLog {S : VarSpaces V} {ι : Type} [Fintype ι] [DecidableEq ι] [Nonempty ι]
    (P : MTProcess S ι) (hbad : ∀ i, MeasurableSet (P.bad i)) (ω0 : MTState S) :
    Measurable (TLog P ω0) := by
  apply Measurable.tsum
  intro t
  exact measurable_const.indicator (measurableSet_runningUntil P hbad ω0 (t + 1))

-- -------------------------------------------------------------------
-- Section 3: E[T_LOG] and the linearity-of-expectation decomposition
-- -------------------------------------------------------------------

/-- E[T_LOG], the expected number of resampling steps -- a plain
    Lebesgue integral against the genuine random-log measure. -/
noncomputable def ETLog {S : VarSpaces V} {ι : Type} [Fintype ι] [DecidableEq ι] [Nonempty ι]
    (P : MTProcess S ι) (ω0 : MTState S) : ℝ≥0∞ :=
  ∫⁻ ω, TLog P ω0 ω ∂(logMeasure S)

/-- The result: E[T_LOG] decomposes as a sum, over every candidate
    stopping time `t`, of the probability the process is STILL running
    at `t` -- linearity of expectation over T_LOG's indicator-sum
    definition, via `lintegral_tsum` swapping the integral and the
    countable sum, then `lintegral_indicator_const` collapsing each
    term to a bare probability. This tail-sum identity is expectation
    infrastructure for a fixed initial state, not the expected-work budget
    theorem. The witness-tree probability and counting arguments are separate;
    Bounds.OccurrenceExpectation assembles their budget bound for product-table
    random initialization. No such budget bound for an arbitrary fixed start
    is asserted by this identity. -/
theorem ETLog_eq_tsum {S : VarSpaces V} {ι : Type} [Fintype ι] [DecidableEq ι] [Nonempty ι]
    (P : MTProcess S ι) (hbad : ∀ i, MeasurableSet (P.bad i)) (ω0 : MTState S) :
    ETLog P ω0 = ∑' t : ℕ, logMeasure S {ω : LogSpace S | RunningUntil P ω0 ω (t + 1)} := by
  unfold ETLog TLog
  rw [lintegral_tsum
    (fun t => (measurable_const.indicator (measurableSet_runningUntil P hbad ω0 (t + 1))).aemeasurable)]
  congr 1
  ext t
  rw [lintegral_indicator_const (measurableSet_runningUntil P hbad ω0 (t + 1)) 1, one_mul]

-- -------------------------------------------------------------------
-- Verification
-- -------------------------------------------------------------------

#check @measurableSet_violatedAt
#check @measurableSet_runningUntil
#check @TLog
#check @measurable_TLog
#check @ETLog
#check @ETLog_eq_tsum
