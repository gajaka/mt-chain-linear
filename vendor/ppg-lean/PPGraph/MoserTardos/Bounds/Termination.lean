/-
  PPGraphMoserTardosTermination.lean

  A finite stopped log is equivalent to reaching a state avoiding every
  bad event. Finite expected stopped length consequently gives almost
  sure termination for the slot-zero initialization law and the existence
  of a good state. This does not assert almost sure termination from an
  arbitrary fixed initial state.
-/

module

public import PPGraph.MoserTardos.Bounds.OccurrenceExpectation
public import Mathlib.MeasureTheory.Integral.Lebesgue.Markov

@[expose] public section

open MeasureTheory Classical
open scoped NNReal ENNReal

/-- A state satisfying every MT constraint. -/
def MTGood {V : Type} {S : VarSpaces V} {ι : Type}
    (P : MTProcess S ι) (s : MTState S) : Prop :=
  ∀ i, s ∉ P.bad i

variable {V : Type} [DecidableEq V] {S : VarSpaces V} {ι : Type}
    [Fintype ι] [DecidableEq ι] [Nonempty ι]

/-- Once a good state has been reached, no later index contributes to
    the stopped log. The underlying, unstopped trajectory need not stay
    good after that time. -/
theorem TLog_le_of_good (P : MTProcess S ι) (ω0 : MTState S)
    (ω : LogSpace S) (T : ℕ) (hgood : MTGood P (randTraj P ω0 ω T)) :
    TLog P ω0 ω ≤ (T : ℝ≥0∞) := by
  classical
  have hstop : ∀ s, T ≤ s → ¬ RunningUntil P ω0 ω (s + 1) := by
    intro s hs hrun
    exact hgood (realC P ω0 ω T) (hrun T (Nat.lt_succ_of_le hs))
  have hzero : ∀ s ∉ Finset.range T,
      {ω' : LogSpace S | RunningUntil P ω0 ω' (s + 1)}.indicator
        (fun _ => (1 : ℝ≥0∞)) ω = 0 := by
    intro s hs
    apply Set.indicator_of_notMem
    exact hstop s (Nat.le_of_not_gt (by
      simpa only [Finset.mem_range] using hs))
  unfold TLog
  rw [tsum_eq_sum hzero]
  calc
    (∑ s ∈ Finset.range T,
        {ω' : LogSpace S | RunningUntil P ω0 ω' (s + 1)}.indicator
          (fun _ => (1 : ℝ≥0∞)) ω) ≤
        ∑ _s ∈ Finset.range T, (1 : ℝ≥0∞) := by
      apply Finset.sum_le_sum
      intro s _
      by_cases hs : RunningUntil P ω0 ω (s + 1)
      · have hmem : ω ∈
            {ω' : LogSpace S | RunningUntil P ω0 ω' (s + 1)} := hs
        rw [Set.indicator_of_mem hmem]
      · rw [Set.indicator_of_notMem hs]
        exact zero_le
    _ = (T : ℝ≥0∞) := by simp

/-- Finiteness refers to the stopped count: it is exactly the existence
    of a time at which the actual trajectory reaches a good state. -/
theorem TLog_lt_top_iff_exists_good (P : MTProcess S ι) (ω0 : MTState S)
    (ω : LogSpace S) :
    TLog P ω0 ω < ⊤ ↔ ∃ T : ℕ, MTGood P (randTraj P ω0 ω T) := by
  classical
  constructor
  · intro hfinite
    by_contra hnone
    have hbad : ∀ s : ℕ,
        (randStep P ω0 ω s).1 ∈ P.bad (realC P ω0 ω s) := by
      intro s
      by_contra hs
      exact hnone ⟨s, (randStep_notMem_bad_realC_iff P ω0 ω s).mp hs⟩
    have hrun : ∀ s : ℕ, RunningUntil P ω0 ω (s + 1) :=
      fun _ t _ => hbad t
    have hinfinite : TLog P ω0 ω = ⊤ := by
      calc
        TLog P ω0 ω = ∑' _s : ℕ, (1 : ℝ≥0∞) := by
          unfold TLog
          apply tsum_congr
          intro s
          exact Set.indicator_of_mem (hrun s) _
        _ = ⊤ := ENNReal.tsum_const_eq_top_of_ne_zero one_ne_zero
    exact hfinite.ne hinfinite
  · rintro ⟨T, hgood⟩
    exact lt_of_le_of_lt (TLog_le_of_good P ω0 ω T hgood) (by simp)

/-- A finite expectation makes the random-initialized stopped log finite
    almost everywhere under the product-log law. -/
theorem ae_randomInitTLog_lt_top (P : MTProcess S ι)
    (hbad : ∀ i, MeasurableSet (P.bad i))
    (hfinite : randomInitETLog P < ⊤) :
    ∀ᵐ ω ∂logMeasure S, randomInitTLog P ω < ⊤ := by
  exact MeasureTheory.ae_lt_top (measurable_randomInitTLog P hbad) hfinite.ne

/-- Almost every table reaches a good state when its slot zero supplies
    the initial state. -/
theorem ae_randomInit_exists_good (P : MTProcess S ι)
    (hbad : ∀ i, MeasurableSet (P.bad i))
    (hfinite : randomInitETLog P < ⊤) :
    ∀ᵐ ω ∂logMeasure S,
      ∃ T : ℕ, MTGood P (randTraj P (initialStateFromLog ω) ω T) := by
  filter_upwards [ae_randomInitTLog_lt_top P hbad hfinite] with ω hω
  exact (TLog_lt_top_iff_exists_good P (initialStateFromLog ω) ω).mp hω

/-- The measurable event of reaching a good state has probability one
    under random initialization. -/
theorem logMeasure_randomInit_termination_eq_one (P : MTProcess S ι)
    (hbad : ∀ i, MeasurableSet (P.bad i))
    (hfinite : randomInitETLog P < ⊤) :
    logMeasure S {ω | ∃ T : ℕ,
      MTGood P (randTraj P (initialStateFromLog ω) ω T)} = 1 := by
  have heq : {ω : LogSpace S | ∃ T : ℕ,
      MTGood P (randTraj P (initialStateFromLog ω) ω T)} =
      {ω | randomInitTLog P ω < ⊤} := by
    ext ω
    exact (TLog_lt_top_iff_exists_good P (initialStateFromLog ω) ω).symm
  rw [heq]
  exact (mem_ae_iff_prob_eq_one
    (measurableSet_lt (measurable_randomInitTLog P hbad) measurable_const)).mp
      (ae_randomInitTLog_lt_top P hbad hfinite)

/-- Probability one is nonzero, so a finite expectation supplies an
    actual good state, without prescribing its starting state. -/
theorem exists_MTGood_of_randomInitETLog_lt_top (P : MTProcess S ι)
    (hbad : ∀ i, MeasurableSet (P.bad i))
    (hfinite : randomInitETLog P < ⊤) : ∃ z : MTState S, MTGood P z := by
  have hne : logMeasure S {ω | ∃ T : ℕ,
      MTGood P (randTraj P (initialStateFromLog ω) ω T)} ≠ 0 := by
    rw [logMeasure_randomInit_termination_eq_one P hbad hfinite]
    exact one_ne_zero
  obtain ⟨ω, T, hT⟩ := nonempty_of_measure_ne_zero hne
  exact ⟨randTraj P (initialStateFromLog ω) ω T, hT⟩

/-- The witness-tree MT budget produces a good state through the
    finite-expectation and almost-sure-termination bridge. -/
theorem exists_MTGood_of_mt_budget [Fintype V]
    (P : MTProcess S ι) (hbad : ∀ i, MeasurableSet (P.bad i))
    (p x : ι → ℝ≥0)
    (hp : ∀ i, Measure.pi (fun v => S.measure v) (P.bad i) ≤ (p i : ℝ≥0∞))
    (h_dom : ∀ α, p α ≤ x α)
    (h_self : ∀ α, p α * ∏ β ∈ plusNeighbors P α, (1 + x β) ≤ x α) :
    ∃ z : MTState S, MTGood P z := by
  exact exists_MTGood_of_randomInitETLog_lt_top P hbad
    (randomInitETLog_lt_top P hbad p x hp h_dom h_self)

-- -------------------------------------------------------------------
-- Verification
-- -------------------------------------------------------------------

#check @MTGood
#check @TLog_le_of_good
#check @TLog_lt_top_iff_exists_good
#check @ae_randomInitTLog_lt_top
#check @ae_randomInit_exists_good
#check @logMeasure_randomInit_termination_eq_one
#check @exists_MTGood_of_randomInitETLog_lt_top
#check @exists_MTGood_of_mt_budget
