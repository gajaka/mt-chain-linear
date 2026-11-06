/-
  PPGraphMoserTardosResamplingCount.lean

  Step 3: the stopped log, decomposed by resampled event.
  Alon-Spencer, The Probabilistic Method, 4th ed., Section 5.7,
  pp. 82-85 (the counting argument preceding Theorem 5.7.2).

  Each genuine step contributes to exactly one event count. Summing
  these counts gives TLog pointwise, and integrating gives the same
  decomposition for ETLog. All infinite sums take values in ENNReal;
  termination and finite expectation are not assumed.

  The finite-horizon counting theorem uses canonical witness trees
  at time s + 1 with shiftedC. Thus the first real step s = 0 is
  included, and RunningUntil excludes every step after termination.

  The expectation results here use the existing fixed-initial-state
  ETLog. They do not assert the final MT bound for that initial law.
  The book initializes from table slot 0; integrating the corresponding
  log-dependent initial state still needs its own measurability bridge.
-/

module

public import PPGraph.MoserTardos.Bounds.Expectation
public import PPGraph.MoserTardos.Witness.InjectivityBridge
public import Mathlib.Algebra.BigOperators.Ring.Finset
public import Mathlib.Topology.Algebra.InfiniteSum.ENNReal
public import Mathlib.MeasureTheory.Integral.Lebesgue.Add
public import Mathlib.MeasureTheory.Constructions.Polish.Basic

@[expose] public section

open MeasureTheory Classical
open scoped ENNReal

variable {V : Type} [DecidableEq V] {S : VarSpaces V} {ι : Type}
    [Fintype ι] [DecidableEq ι] [Nonempty ι]

/-- At real step `s`, the process has not stopped and resamples `α`. -/
def resamplingEvent (P : MTProcess S ι) (ω0 : MTState S) (α : ι) (s : ℕ) :
    Set (LogSpace S) :=
  {ω | RunningUntil P ω0 ω (s + 1) ∧ realC P ω0 ω s = α}

theorem measurableSet_realC_eq (P : MTProcess S ι)
    (hbad : ∀ i, MeasurableSet (P.bad i)) (ω0 : MTState S) (α : ι) (s : ℕ) :
    MeasurableSet {ω : LogSpace S | realC P ω0 ω s = α} := by
  let : MeasurableSpace ι := ⊤
  have hmeas : Measurable (fun ω : LogSpace S => realC P ω0 ω s) :=
    (measurable_pickFirstViolated P hbad).comp (measurable_randStep P hbad ω0 s).1
  exact hmeas (measurableSet_singleton α)

theorem measurableSet_resamplingEvent (P : MTProcess S ι)
    (hbad : ∀ i, MeasurableSet (P.bad i)) (ω0 : MTState S) (α : ι) (s : ℕ) :
    MeasurableSet (resamplingEvent P ω0 α s) := by
  exact (measurableSet_runningUntil P hbad ω0 (s + 1)).inter
    (measurableSet_realC_eq P hbad ω0 α s)

/-- `N_α`: the number of resamplings of `α` before the first successful
    state. This may be infinite; `randStep`'s continuation after success
    contributes nothing. -/
noncomputable def resamplingCount (P : MTProcess S ι) (ω0 : MTState S)
    (ω : LogSpace S) (α : ι) : ℝ≥0∞ :=
  ∑' s : ℕ, (resamplingEvent P ω0 α s).indicator (fun _ => 1) ω

theorem measurable_resamplingCount (P : MTProcess S ι)
    (hbad : ∀ i, MeasurableSet (P.bad i)) (ω0 : MTState S) (α : ι) :
    Measurable (fun ω : LogSpace S => resamplingCount P ω0 ω α) := by
  apply Measurable.tsum
  intro s
  exact measurable_const.indicator (measurableSet_resamplingEvent P hbad ω0 α s)

/-- Partition one active step by its uniquely selected event. -/
theorem runningUntil_indicator_eq_sum_resamplingEvent (P : MTProcess S ι)
    (ω0 : MTState S) (ω : LogSpace S) (s : ℕ) :
    {ω' : LogSpace S | RunningUntil P ω0 ω' (s + 1)}.indicator
        (fun _ => (1 : ℝ≥0∞)) ω =
      ∑ α : ι, (resamplingEvent P ω0 α s).indicator (fun _ => 1) ω := by
  by_cases hrun : RunningUntil P ω0 ω (s + 1) <;>
    simp [resamplingEvent, Set.indicator_apply, hrun]

/-- Count the same stopped log by time or by event. No probabilistic
    assumption on the initial state is needed for this pointwise identity. -/
theorem TLog_eq_sum_resamplingCount (P : MTProcess S ι)
    (ω0 : MTState S) (ω : LogSpace S) :
    TLog P ω0 ω = ∑ α : ι, resamplingCount P ω0 ω α := by
  calc
    TLog P ω0 ω = ∑' s : ℕ, ∑' α : ι,
        (resamplingEvent P ω0 α s).indicator (fun _ => (1 : ℝ≥0∞)) ω := by
      unfold TLog
      apply tsum_congr
      intro s
      rw [tsum_fintype]
      exact runningUntil_indicator_eq_sum_resamplingEvent P ω0 ω s
    _ = ∑' α : ι, ∑' s : ℕ,
        (resamplingEvent P ω0 α s).indicator (fun _ => (1 : ℝ≥0∞)) ω :=
      ENNReal.tsum_comm
    _ = ∑ α : ι, resamplingCount P ω0 ω α := by
      simp only [resamplingCount, tsum_fintype]

/-- Expected stopped resampling count for one event, with a fixed
    initial state as in the existing `ETLog`. -/
noncomputable def expectedResamplingCount (P : MTProcess S ι)
    (ω0 : MTState S) (α : ι) : ℝ≥0∞ :=
  ∫⁻ ω, resamplingCount P ω0 ω α ∂(logMeasure S)

theorem expectedResamplingCount_eq_tsum (P : MTProcess S ι)
    (hbad : ∀ i, MeasurableSet (P.bad i)) (ω0 : MTState S) (α : ι) :
    expectedResamplingCount P ω0 α =
      ∑' s : ℕ, logMeasure S (resamplingEvent P ω0 α s) := by
  unfold expectedResamplingCount resamplingCount
  rw [lintegral_tsum (fun s =>
    (measurable_const.indicator (measurableSet_resamplingEvent P hbad ω0 α s)).aemeasurable)]
  apply tsum_congr
  intro s
  rw [lintegral_indicator_const (measurableSet_resamplingEvent P hbad ω0 α s) 1,
    one_mul]

/-- The event-wise expectation decomposition. It is valid in ENNReal
    before establishing that either side is finite. -/
theorem ETLog_eq_sum_expectedResamplingCount (P : MTProcess S ι)
    (hbad : ∀ i, MeasurableSet (P.bad i)) (ω0 : MTState S) :
    ETLog P ω0 = ∑ α : ι, expectedResamplingCount P ω0 α := by
  unfold ETLog expectedResamplingCount
  calc
    (∫⁻ ω, TLog P ω0 ω ∂(logMeasure S)) =
        ∫⁻ ω, ∑ α : ι, resamplingCount P ω0 ω α ∂(logMeasure S) :=
      lintegral_congr (fun ω => TLog_eq_sum_resamplingCount P ω0 ω)
    _ = ∑ α : ι, ∫⁻ ω, resamplingCount P ω0 ω α ∂(logMeasure S) :=
      lintegral_finsetSum Finset.univ (fun α _ => measurable_resamplingCount P hbad ω0 α)

/-- Genuine resampling times of `α` in the first `n` candidate steps.
    In particular, time 0 is included whenever the first step is active. -/
noncomputable def resamplingTimesUpTo (P : MTProcess S ι) (ω0 : MTState S)
    (ω : LogSpace S) (α : ι) (n : ℕ) : Finset ℕ :=
  (Finset.range n).filter (fun s => ω ∈ resamplingEvent P ω0 α s)

@[simp]
theorem mem_resamplingTimesUpTo (P : MTProcess S ι) (ω0 : MTState S)
    (ω : LogSpace S) (α : ι) (n s : ℕ) :
    s ∈ resamplingTimesUpTo P ω0 ω α n ↔
      s < n ∧ RunningUntil P ω0 ω (s + 1) ∧ realC P ω0 ω s = α := by
  unfold resamplingTimesUpTo
  constructor
  · intro hs
    rcases Finset.mem_filter.mp hs with ⟨hs, hresample⟩
    exact ⟨Finset.mem_range.mp hs, hresample⟩
  · rintro ⟨hs, hresample⟩
    exact Finset.mem_filter.mpr ⟨Finset.mem_range.mpr hs, hresample⟩

/-- The finite indicator sum is the cardinality of the stopped set
    of resampling times, regarded as an ENNReal. -/
theorem sum_resamplingEvent_indicator_eq_card (P : MTProcess S ι)
    (ω0 : MTState S) (ω : LogSpace S) (α : ι) (n : ℕ) :
    (∑ s ∈ Finset.range n,
      (resamplingEvent P ω0 α s).indicator (fun _ => (1 : ℝ≥0∞)) ω) =
      ((resamplingTimesUpTo P ω0 ω α n).card : ℝ≥0∞) := by
  simp only [Set.indicator_apply, Finset.sum_boole, resamplingTimesUpTo]

/-- Connect the countable count to its finite stopped prefixes,
    without assuming that the total count is finite. -/
theorem resamplingCount_eq_iSup_card (P : MTProcess S ι)
    (ω0 : MTState S) (ω : LogSpace S) (α : ι) :
    resamplingCount P ω0 ω α =
      ⨆ n : ℕ, ((resamplingTimesUpTo P ω0 ω α n).card : ℝ≥0∞) := by
  unfold resamplingCount
  rw [ENNReal.tsum_eq_iSup_nat]
  simp_rw [sum_resamplingEvent_indicator_eq_card]

/-- The canonical tree belonging to real step `s` has τC-index `s + 1`.
    This definition alone does not assert that step `s` was active. -/
noncomputable def resamplingWitness (P : MTProcess S ι) (ω0 : MTState S)
    (ω : LogSpace S) (s : ℕ) : WTree ι :=
  WTree.canonicalize ((τC P (shiftedC P ω0 ω) (s + 1)).toWTree [])

theorem resamplingWitness_label (P : MTProcess S ι) (ω0 : MTState S)
    (ω : LogSpace S) (s : ℕ) :
    (resamplingWitness P ω0 ω s).label = realC P ω0 ω s := by
  have hraw := τC_toWTree_wellFormed_proper P (shiftedC P ω0 ω) (s + 1)
  have hcanonical := WTree.canonicalize_mem_wtreesUpTo P (fun _ => 0)
    ((τC P (shiftedC P ω0 ω) (s + 1)).toWTree []) hraw.2.1 hraw.2.2.1
  exact hcanonical.1.trans (hraw.1.trans (shiftedC_succ P ω0 ω s))

/-- Distinct real times with the same selected event give distinct
    canonical witnesses, including the first real time 0. -/
theorem resamplingWitness_ne_of_lt (P : MTProcess S ι) (ω0 : MTState S)
    (ω : LogSpace S) (s t : ℕ) (hst : s < t)
    (hlabel : realC P ω0 ω s = realC P ω0 ω t) :
    resamplingWitness P ω0 ω s ≠ resamplingWitness P ω0 ω t := by
  apply τC_canonicalize_toWTree_ne_of_lt P (shiftedC P ω0 ω) (s + 1) (t + 1)
  · omega
  · omega
  · omega
  · simpa only [shiftedC_succ] using hlabel

/-- The finite-horizon counting half of the witness-tree argument,
    now for the stopped log and canonical representatives. -/
theorem card_resamplingTimesUpTo_eq_card_witnesses (P : MTProcess S ι)
    (ω0 : MTState S) (ω : LogSpace S) (α : ι) (n : ℕ) :
    (resamplingTimesUpTo P ω0 ω α n).card =
      ((resamplingTimesUpTo P ω0 ω α n).image (resamplingWitness P ω0 ω)).card := by
  symm
  apply Finset.card_image_of_injOn
  intro s hs t ht heq
  have hs' := (mem_resamplingTimesUpTo P ω0 ω α n s).mp hs
  have ht' := (mem_resamplingTimesUpTo P ω0 ω α n t).mp ht
  have hlabel : realC P ω0 ω s = realC P ω0 ω t := hs'.2.2.trans ht'.2.2.symm
  rcases lt_trichotomy s t with hst | hst | hts
  · exact False.elim ((resamplingWitness_ne_of_lt P ω0 ω s t hst hlabel) heq)
  · exact hst
  · exact False.elim ((resamplingWitness_ne_of_lt P ω0 ω t s hts hlabel.symm) heq.symm)

/-- The full stopped count is exhausted by the cardinalities of
    distinct canonical witnesses in finite prefixes. This is still
    pointwise counting, before taking probabilities of occurrences. -/
theorem resamplingCount_eq_iSup_card_witnesses (P : MTProcess S ι)
    (ω0 : MTState S) (ω : LogSpace S) (α : ι) :
    resamplingCount P ω0 ω α = ⨆ n : ℕ,
      (((resamplingTimesUpTo P ω0 ω α n).image (resamplingWitness P ω0 ω)).card : ℝ≥0∞) := by
  simp_rw [resamplingCount_eq_iSup_card, card_resamplingTimesUpTo_eq_card_witnesses]

-- -------------------------------------------------------------------
-- Verification
-- -------------------------------------------------------------------

#check @resamplingEvent
#check @measurableSet_realC_eq
#check @measurableSet_resamplingEvent
#check @resamplingCount
#check @measurable_resamplingCount
#check @runningUntil_indicator_eq_sum_resamplingEvent
#check @TLog_eq_sum_resamplingCount
#check @expectedResamplingCount
#check @expectedResamplingCount_eq_tsum
#check @ETLog_eq_sum_expectedResamplingCount
#check @resamplingTimesUpTo
#check @mem_resamplingTimesUpTo
#check @sum_resamplingEvent_indicator_eq_card
#check @resamplingCount_eq_iSup_card
#check @resamplingWitness
#check @resamplingWitness_label
#check @resamplingWitness_ne_of_lt
#check @card_resamplingTimesUpTo_eq_card_witnesses
#check @resamplingCount_eq_iSup_card_witnesses
