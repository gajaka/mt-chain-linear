/-
  From expected MT steps to an additive execution-cost bound.

  A measured/proved upper bound on each active step's cost turns the
  drift theorem into a bound on expected total cost. This is an abstract
  cost model, not a WCET proof for ESP32 instructions or its scheduler.
  Costs may be processor cycles, energy, or elapsed time if the model
  includes all relevant per-step overheads.

  Background: Lee--Seshia, Introduction to Embedded Systems, Ch. 16.
    https://ptolemy.berkeley.edu/books/leeseshia/
-/

module

public import PPGraph.MoserTardos.Bounds.Drift

@[expose] public section

open MeasureTheory Classical
open scoped NNReal ENNReal

namespace RepairDrift

variable {V : Type} [DecidableEq V] {S : VarSpaces V} {ι : Type}
    [Fintype ι] [DecidableEq ι] [Nonempty ι]

/-- Charge only genuine resampling steps before the first success. -/
noncomputable def mtTotalCost (P : MTProcess S ι)
    (init : LogSpace S → MTState S) (cost : MTState S → ℝ≥0)
    (ω : LogSpace S) : ℝ≥0∞ :=
  ∑' n, (mtRunningEvent P init (n + 1)).indicator
    (fun ω' => (cost (randTraj P (init ω') ω' n) : ℝ≥0∞)) ω

noncomputable def mtExpectedCost (P : MTProcess S ι)
    (init : LogSpace S → MTState S) (cost : MTState S → ℝ≥0) : ℝ≥0∞ :=
  ∫⁻ ω, mtTotalCost P init cost ω ∂logMeasure S

theorem measurable_mtTotalCost (P : MTProcess S ι)
    (hbad : ∀ i, MeasurableSet (P.bad i))
    (init : LogSpace S → MTState S) (hinit : Measurable init)
    (cost : MTState S → ℝ≥0) (hcost : Measurable cost) :
    Measurable (mtTotalCost P init cost) := by
  apply Measurable.tsum
  intro n
  exact (measurable_coe_nnreal_ennreal.comp (hcost.comp
    (measurable_randStep_of_measurable_init P hbad init hinit n).1)).indicator
    (measurableSet_runningUntil_of_measurable_init P hbad init hinit (n + 1))

theorem mtTotalCost_le_cap_mul_TLog (P : MTProcess S ι)
    (init : LogSpace S → MTState S) (cost : MTState S → ℝ≥0)
    (cap : ℝ≥0) (hcap : ∀ s, cost s ≤ cap) (ω : LogSpace S) :
    mtTotalCost P init cost ω ≤ (cap : ℝ≥0∞) * TLog P (init ω) ω := by
  rw [← activeCount_mt_eq_TLog P init ω]
  unfold mtTotalCost activeCount
  rw [← ENNReal.tsum_mul_left]
  apply ENNReal.tsum_le_tsum
  intro n
  by_cases h : ω ∈ mtRunningEvent P init (n + 1)
  · rw [Set.indicator_of_mem h, Set.indicator_of_mem h, mul_one]
    exact_mod_cast hcap _
  · rw [Set.indicator_of_notMem h, Set.indicator_of_notMem h, mul_zero]

theorem mtExpectedCost_fixed_le (P : MTProcess S ι)
    (hbad : ∀ i, MeasurableSet (P.bad i)) (ω0 : MTState S)
    (cost : MTState S → ℝ≥0) (cap : ℝ≥0) (hcap : ∀ s, cost s ≤ cap) :
    mtExpectedCost P (fun _ => ω0) cost ≤ (cap : ℝ≥0∞) * ETLog P ω0 := by
  unfold mtExpectedCost ETLog
  calc
    (∫⁻ ω, mtTotalCost P (fun _ => ω0) cost ω ∂logMeasure S) ≤
        ∫⁻ ω, (cap : ℝ≥0∞) * TLog P ω0 ω ∂logMeasure S :=
      lintegral_mono (mtTotalCost_le_cap_mul_TLog P (fun _ => ω0) cost cap hcap)
    _ = _ := lintegral_const_mul _ (measurable_TLog P hbad ω0)

theorem mtExpectedCost_randomInit_le (P : MTProcess S ι)
    (hbad : ∀ i, MeasurableSet (P.bad i))
    (cost : MTState S → ℝ≥0) (cap : ℝ≥0) (hcap : ∀ s, cost s ≤ cap) :
    mtExpectedCost P initialStateFromLog cost ≤ (cap : ℝ≥0∞) * randomInitETLog P := by
  unfold mtExpectedCost randomInitETLog
  calc
    (∫⁻ ω, mtTotalCost P initialStateFromLog cost ω ∂logMeasure S) ≤
        ∫⁻ ω, (cap : ℝ≥0∞) * randomInitTLog P ω ∂logMeasure S :=
      lintegral_mono (mtTotalCost_le_cap_mul_TLog P initialStateFromLog cost cap hcap)
    _ = _ := lintegral_const_mul _ (measurable_randomInitTLog P hbad)

theorem mtExpectedCost_fixed_le_of_drift (P : MTProcess S ι)
    (hbad : ∀ i, MeasurableSet (P.bad i)) (ω0 : MTState S)
    (cost : MTState S → ℝ≥0) (cap : ℝ≥0) (hcap : ∀ s, cost s ≤ cap)
    (potential : MTState S → ℝ≥0) (hpotential : Measurable potential)
    (δ : ℝ≥0) (hδ : 0 < δ)
    (C : MTCertificate P hbad (fun _ => ω0) measurable_const potential δ) :
    mtExpectedCost P (fun _ => ω0) cost ≤
      (cap : ℝ≥0∞) * ((potential ω0 : ℝ≥0∞) / (δ : ℝ≥0∞)) := by
  exact (mtExpectedCost_fixed_le P hbad ω0 cost cap hcap).trans
    (mul_le_mul le_rfl (ETLog_le_of_drift P hbad ω0 potential hpotential δ hδ C)
      zero_le zero_le)

theorem mtExpectedCost_fixed_lt_top_of_drift (P : MTProcess S ι)
    (hbad : ∀ i, MeasurableSet (P.bad i)) (ω0 : MTState S)
    (cost : MTState S → ℝ≥0) (cap : ℝ≥0) (hcap : ∀ s, cost s ≤ cap)
    (potential : MTState S → ℝ≥0) (hpotential : Measurable potential)
    (δ : ℝ≥0) (hδ : 0 < δ)
    (C : MTCertificate P hbad (fun _ => ω0) measurable_const potential δ) :
    mtExpectedCost P (fun _ => ω0) cost < ⊤ := by
  exact lt_of_le_of_lt (mtExpectedCost_fixed_le P hbad ω0 cost cap hcap)
    (ENNReal.mul_lt_top ENNReal.coe_lt_top
      (ETLog_lt_top_of_drift P hbad ω0 potential hpotential δ hδ C))

end RepairDrift

#check @RepairDrift.measurable_mtTotalCost
#check @RepairDrift.mtTotalCost_le_cap_mul_TLog
#check @RepairDrift.mtExpectedCost_fixed_le
#check @RepairDrift.mtExpectedCost_randomInit_le
#check @RepairDrift.mtExpectedCost_fixed_le_of_drift
#check @RepairDrift.mtExpectedCost_fixed_lt_top_of_drift
