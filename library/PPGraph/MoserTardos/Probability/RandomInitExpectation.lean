/-
  PPGraphMoserTardosRandomInitExpectation.lean

  Step 3: the stopped process initialized from its own random table.
  Slot 0 supplies the initial state; resampling consumes slots 1, 2, ...
  according to each variable's counter, as in Alon-Spencer, Section 5.7.

  The pointwise counts reuse TLog and resamplingCount. Their measurability
  is proved for the log-dependent initial state before integrating.
  randomInitETLog is a new expectation, with initialization and resampling
  both included in the product-log law. The existing ETLog P ω0 retains
  its fixed-initial-state meaning.

  This module supplies the time and event decompositions for that law,
  and discharges the slot-zero hypothesis of trajectory correspondence.
  It does not yet prove the occurrence-probability or final MT bound.
-/

module

public import PPGraph.MoserTardos.Process.RandomInitialization
public import PPGraph.MoserTardos.Counting.ResamplingCount

@[expose] public section

open MeasureTheory Classical
open scoped ENNReal

variable {V : Type} [DecidableEq V] {S : VarSpaces V} {ι : Type}
    [Fintype ι] [DecidableEq ι] [Nonempty ι]

/-- The selected label is measurable when the initial state itself
    is a measurable function of the log. -/
theorem measurable_realC_of_measurable_init (P : MTProcess S ι)
    (hbad : ∀ i, MeasurableSet (P.bad i))
    (init : LogSpace S → MTState S) (hinit : Measurable init) (s : ℕ) :
    letI : MeasurableSpace ι := ⊤
    Measurable (fun ω : LogSpace S => realC P (init ω) ω s) := by
  let : MeasurableSpace ι := ⊤
  exact (measurable_pickFirstViolated P hbad).comp
    (measurable_randStep_of_measurable_init P hbad init hinit s).1

theorem measurableSet_violatedAt_of_measurable_init (P : MTProcess S ι)
    (hbad : ∀ i, MeasurableSet (P.bad i))
    (init : LogSpace S → MTState S) (hinit : Measurable init) (s : ℕ) :
    MeasurableSet {ω : LogSpace S |
      (randStep P (init ω) ω s).1 ∈ P.bad (realC P (init ω) ω s)} := by
  have heq : {ω : LogSpace S |
      (randStep P (init ω) ω s).1 ∈ P.bad (realC P (init ω) ω s)} =
      ⋃ i : ι, ({ω : LogSpace S | realC P (init ω) ω s = i} ∩
        {ω : LogSpace S | (randStep P (init ω) ω s).1 ∈ P.bad i}) := by
    ext ω
    simp only [Set.mem_ofPred_eq, Set.mem_iUnion, Set.mem_inter_iff]
    constructor
    · intro h
      exact ⟨realC P (init ω) ω s, rfl, h⟩
    · rintro ⟨i, hi, hmem⟩
      rw [hi]
      exact hmem
  rw [heq]
  refine MeasurableSet.iUnion (fun i => MeasurableSet.inter ?_ ?_)
  · let : MeasurableSpace ι := ⊤
    exact (measurable_realC_of_measurable_init P hbad init hinit s)
      (measurableSet_singleton i)
  · exact (measurable_randStep_of_measurable_init P hbad init hinit s).1 (hbad i)

theorem measurableSet_runningUntil_of_measurable_init (P : MTProcess S ι)
    (hbad : ∀ i, MeasurableSet (P.bad i))
    (init : LogSpace S → MTState S) (hinit : Measurable init) (t : ℕ) :
    MeasurableSet {ω : LogSpace S | RunningUntil P (init ω) ω t} := by
  have heq : {ω : LogSpace S | RunningUntil P (init ω) ω t} =
      ⋂ s ∈ Finset.range t, {ω : LogSpace S |
        (randStep P (init ω) ω s).1 ∈ P.bad (realC P (init ω) ω s)} := by
    ext ω
    simp only [RunningUntil, Set.mem_ofPred_eq, Set.mem_iInter, Finset.mem_range]
  rw [heq]
  exact Finset.measurableSet_biInter _
    (fun s _ => measurableSet_violatedAt_of_measurable_init P hbad init hinit s)

/-- The random initialization and the subsequent trajectory use the
    same table in this event. -/
def randomInitRunningEvent (P : MTProcess S ι) (t : ℕ) : Set (LogSpace S) :=
  {ω | RunningUntil P (initialStateFromLog ω) ω t}

theorem measurableSet_randomInitRunningEvent (P : MTProcess S ι)
    (hbad : ∀ i, MeasurableSet (P.bad i)) (t : ℕ) :
    MeasurableSet (randomInitRunningEvent P t) := by
  exact measurableSet_runningUntil_of_measurable_init P hbad initialStateFromLog
    measurable_initialStateFromLog t

/-- The event that real step `s` is active and selects `α`, including
    the random choice of the initial state from slot 0. -/
def randomInitResamplingEvent (P : MTProcess S ι) (α : ι) (s : ℕ) :
    Set (LogSpace S) :=
  {ω | RunningUntil P (initialStateFromLog ω) ω (s + 1) ∧
    realC P (initialStateFromLog ω) ω s = α}

theorem measurableSet_randomInitResamplingEvent (P : MTProcess S ι)
    (hbad : ∀ i, MeasurableSet (P.bad i)) (α : ι) (s : ℕ) :
    MeasurableSet (randomInitResamplingEvent P α s) := by
  have hlabel : MeasurableSet {ω : LogSpace S |
      realC P (initialStateFromLog ω) ω s = α} := by
    let : MeasurableSpace ι := ⊤
    exact (measurable_realC_of_measurable_init P hbad initialStateFromLog
      measurable_initialStateFromLog s) (measurableSet_singleton α)
  exact (measurableSet_randomInitRunningEvent P hbad (s + 1)).inter hlabel

/-- The stopped log length when the initial state is read from slot 0. -/
noncomputable def randomInitTLog (P : MTProcess S ι) (ω : LogSpace S) : ℝ≥0∞ :=
  TLog P (initialStateFromLog ω) ω

/-- Rewrite the diagonal evaluation as indicators of genuine events
    on the log space, so that their measurability can be used. -/
theorem randomInitTLog_eq_tsum_indicator (P : MTProcess S ι) (ω : LogSpace S) :
    randomInitTLog P ω = ∑' s : ℕ,
      (randomInitRunningEvent P (s + 1)).indicator (fun _ => (1 : ℝ≥0∞)) ω := by
  unfold randomInitTLog TLog
  apply tsum_congr
  intro s
  simp only [randomInitRunningEvent, Set.indicator_apply, Set.mem_ofPred_eq]

theorem measurable_randomInitTLog (P : MTProcess S ι)
    (hbad : ∀ i, MeasurableSet (P.bad i)) : Measurable (randomInitTLog P) := by
  have heq : randomInitTLog P = fun ω : LogSpace S => ∑' s : ℕ,
      (randomInitRunningEvent P (s + 1)).indicator (fun _ => (1 : ℝ≥0∞)) ω :=
    funext (randomInitTLog_eq_tsum_indicator P)
  rw [heq]
  apply Measurable.tsum
  intro s
  exact measurable_const.indicator (measurableSet_randomInitRunningEvent P hbad (s + 1))

/-- The stopped count of resamplings of `α` with random initialization. -/
noncomputable def randomInitResamplingCount (P : MTProcess S ι)
    (ω : LogSpace S) (α : ι) : ℝ≥0∞ :=
  resamplingCount P (initialStateFromLog ω) ω α

theorem randomInitResamplingCount_eq_tsum_indicator (P : MTProcess S ι)
    (ω : LogSpace S) (α : ι) :
    randomInitResamplingCount P ω α = ∑' s : ℕ,
      (randomInitResamplingEvent P α s).indicator (fun _ => (1 : ℝ≥0∞)) ω := by
  unfold randomInitResamplingCount resamplingCount
  apply tsum_congr
  intro s
  simp only [randomInitResamplingEvent, resamplingEvent, Set.indicator_apply,
    Set.mem_ofPred_eq]

theorem measurable_randomInitResamplingCount (P : MTProcess S ι)
    (hbad : ∀ i, MeasurableSet (P.bad i)) (α : ι) :
    Measurable (fun ω : LogSpace S => randomInitResamplingCount P ω α) := by
  have heq : (fun ω : LogSpace S => randomInitResamplingCount P ω α) =
      fun ω : LogSpace S => ∑' s : ℕ,
        (randomInitResamplingEvent P α s).indicator (fun _ => (1 : ℝ≥0∞)) ω :=
    funext (fun ω => randomInitResamplingCount_eq_tsum_indicator P ω α)
  rw [heq]
  apply Measurable.tsum
  intro s
  exact measurable_const.indicator (measurableSet_randomInitResamplingEvent P hbad α s)

theorem randomInitTLog_eq_sum_resamplingCount (P : MTProcess S ι) (ω : LogSpace S) :
    randomInitTLog P ω = ∑ α : ι, randomInitResamplingCount P ω α := by
  exact TLog_eq_sum_resamplingCount P (initialStateFromLog ω) ω

/-- Expected stopped log length for the product-log law, including
    random initialization. -/
noncomputable def randomInitETLog (P : MTProcess S ι) : ℝ≥0∞ :=
  ∫⁻ ω, randomInitTLog P ω ∂(logMeasure S)

noncomputable def randomInitExpectedResamplingCount (P : MTProcess S ι) (α : ι) : ℝ≥0∞ :=
  ∫⁻ ω, randomInitResamplingCount P ω α ∂(logMeasure S)

theorem randomInitETLog_eq_tsum (P : MTProcess S ι)
    (hbad : ∀ i, MeasurableSet (P.bad i)) :
    randomInitETLog P = ∑' s : ℕ, logMeasure S (randomInitRunningEvent P (s + 1)) := by
  unfold randomInitETLog
  simp_rw [randomInitTLog_eq_tsum_indicator]
  rw [lintegral_tsum (fun s => (measurable_const.indicator
    (measurableSet_randomInitRunningEvent P hbad (s + 1))).aemeasurable)]
  apply tsum_congr
  intro s
  rw [lintegral_indicator_const (measurableSet_randomInitRunningEvent P hbad (s + 1)) 1,
    one_mul]

theorem randomInitExpectedResamplingCount_eq_tsum (P : MTProcess S ι)
    (hbad : ∀ i, MeasurableSet (P.bad i)) (α : ι) :
    randomInitExpectedResamplingCount P α =
      ∑' s : ℕ, logMeasure S (randomInitResamplingEvent P α s) := by
  unfold randomInitExpectedResamplingCount
  simp_rw [randomInitResamplingCount_eq_tsum_indicator]
  rw [lintegral_tsum (fun s => (measurable_const.indicator
    (measurableSet_randomInitResamplingEvent P hbad α s)).aemeasurable)]
  apply tsum_congr
  intro s
  rw [lintegral_indicator_const (measurableSet_randomInitResamplingEvent P hbad α s) 1,
    one_mul]

/-- Event-wise decomposition of the expectation for the slot-zero law. -/
theorem randomInitETLog_eq_sum_expectedResamplingCount (P : MTProcess S ι)
    (hbad : ∀ i, MeasurableSet (P.bad i)) :
    randomInitETLog P = ∑ α : ι, randomInitExpectedResamplingCount P α := by
  unfold randomInitETLog randomInitExpectedResamplingCount
  calc
    (∫⁻ ω, randomInitTLog P ω ∂(logMeasure S)) =
        ∫⁻ ω, ∑ α : ι, randomInitResamplingCount P ω α ∂(logMeasure S) :=
      lintegral_congr (fun ω => randomInitTLog_eq_sum_resamplingCount P ω)
    _ = ∑ α : ι, ∫⁻ ω, randomInitResamplingCount P ω α ∂(logMeasure S) :=
      lintegral_finsetSum Finset.univ
        (fun α _ => measurable_randomInitResamplingCount P hbad α)

/-- The initial-state premise of trajectory correspondence is now
    automatic, since the trajectory starts from its own slot 0. -/
theorem τCheck_holds_of_randomInit_trajectory (P : MTProcess S ι)
    (ω : LogSpace S) (t : ℕ) (ht : 1 ≤ t)
    (hrun : ω ∈ randomInitRunningEvent P t) :
    τCheck P (τC P (shiftedC P (initialStateFromLog ω) ω) t) ω := by
  exact τCheck_holds_of_real_trajectory P (initialStateFromLog ω) ω t ht
    (fun v => initialStateFromLog_eq_atIdx ω v) hrun

-- -------------------------------------------------------------------
-- Verification
-- -------------------------------------------------------------------

#check @measurable_realC_of_measurable_init
#check @measurableSet_violatedAt_of_measurable_init
#check @measurableSet_runningUntil_of_measurable_init
#check @randomInitRunningEvent
#check @measurableSet_randomInitRunningEvent
#check @randomInitResamplingEvent
#check @measurableSet_randomInitResamplingEvent
#check @randomInitTLog
#check @randomInitTLog_eq_tsum_indicator
#check @measurable_randomInitTLog
#check @randomInitResamplingCount
#check @randomInitResamplingCount_eq_tsum_indicator
#check @measurable_randomInitResamplingCount
#check @randomInitTLog_eq_sum_resamplingCount
#check @randomInitETLog
#check @randomInitExpectedResamplingCount
#check @randomInitETLog_eq_tsum
#check @randomInitExpectedResamplingCount_eq_tsum
#check @randomInitETLog_eq_sum_expectedResamplingCount
#check @τCheck_holds_of_randomInit_trajectory
