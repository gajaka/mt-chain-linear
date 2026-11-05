/-
  The independent fair orientation coin used in He--Li--Sun Lemma 3.4.
  On disagreement, both original events must pass and the opposite order
  must fail. Proposition 3.3 then gives the averaged saving delta^2 / 2.
  This augments the proof sample space, not the resampling algorithm.
  https://arxiv.org/abs/2111.06527
-/
module

public import PPGraph.MoserTardos.Probability.Intersection
public import PPGraph.HLS.Parameters
public import Mathlib.Probability.Distributions.Bernoulli

@[expose] public section

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option backward.isDefEq.respectTransparency false

open MeasureTheory
open scoped ENNReal

namespace HLS

inductive OrientationCoin where
  | keep
  | flip
  deriving DecidableEq

instance : MeasurableSpace OrientationCoin := ⊤

instance : MeasurableSingletonClass OrientationCoin := ⟨fun _ => trivial⟩

noncomputable def coinParameter : unitInterval := ⟨1 / 2, by constructor <;> norm_num⟩

theorem coinParameter_toNNReal : unitInterval.toNNReal coinParameter = (1 / 2 : NNReal) := by
  apply NNReal.eq
  rw [unitInterval.coe_toNNReal, NNReal.coe_div]
  norm_num [coinParameter]

theorem coinParameter_symm_toNNReal :
    unitInterval.toNNReal (unitInterval.symm coinParameter) = (1 / 2 : NNReal) := by
  apply NNReal.eq
  rw [unitInterval.coe_toNNReal, unitInterval.coe_symm_eq, NNReal.coe_div]
  norm_num [coinParameter]

noncomputable def fairOrientation : Measure OrientationCoin :=
  ProbabilityTheory.bernoulliMeasure .keep .flip coinParameter

instance : IsProbabilityMeasure fairOrientation := by
  unfold fairOrientation
  infer_instance

@[simp]
theorem fairOrientation_keep : fairOrientation {OrientationCoin.keep} = 1 / 2 := by
  unfold fairOrientation
  rw [ProbabilityTheory.bernoulliMeasure_apply_of_mem_of_notMem _
    (measurableSet_singleton _) (by simp) (by simp)]
  rw [coinParameter_toNNReal]
  norm_num

@[simp]
theorem fairOrientation_flip : fairOrientation {OrientationCoin.flip} = 1 / 2 := by
  unfold fairOrientation
  rw [ProbabilityTheory.bernoulliMeasure_apply_of_notMem_of_mem _
    (measurableSet_singleton _) (by simp) (by simp)]
  rw [coinParameter_symm_toNNReal]
  norm_num

def coinChoice {U : Type*} (A B : Set U) : Set (OrientationCoin × U) :=
  ({OrientationCoin.keep} ×ˢ A) ∪ ({OrientationCoin.flip} ×ˢ B)

theorem measurableSet_coinChoice {U : Type*} [MeasurableSpace U]
    {A B : Set U} (hA : MeasurableSet A) (hB : MeasurableSet B) :
    MeasurableSet (coinChoice A B) :=
  ((measurableSet_singleton _).prod hA).union ((measurableSet_singleton _).prod hB)

theorem measure_coinChoice {U : Type*} [MeasurableSpace U] (μ : Measure U) [SFinite μ]
    {A B : Set U} (_hA : MeasurableSet A) (hB : MeasurableSet B) :
    (fairOrientation.prod μ) (coinChoice A B) = μ A / 2 + μ B / 2 := by
  have hd : Disjoint ({OrientationCoin.keep} ×ˢ A) ({OrientationCoin.flip} ×ˢ B) := by
    apply Set.disjoint_left.mpr
    intro x hx hy
    have h₁ : x.1 = OrientationCoin.keep := Set.mem_singleton_iff.mp hx.1
    have h₂ : x.1 = OrientationCoin.flip := Set.mem_singleton_iff.mp hy.1
    cases h₁.symm.trans h₂
  rw [coinChoice, measure_union hd ((measurableSet_singleton _).prod hB),
    Measure.prod_prod, Measure.prod_prod, fairOrientation_keep, fairOrientation_flip]
  simp [div_eq_mul_inv, mul_comm]

theorem measureReal_coinChoice {U : Type*} [MeasurableSpace U] (μ : Measure U)
    [IsProbabilityMeasure μ] {A B : Set U} (hA : MeasurableSet A) (hB : MeasurableSet B) :
    (fairOrientation.prod μ).real (coinChoice A B) = μ.real A / 2 + μ.real B / 2 := by
  rw [measureReal_def, measure_coinChoice μ hA hB, ENNReal.toReal_add]
  · simp [measureReal_def, ENNReal.toReal_div]
  · exact ENNReal.div_ne_top (measure_ne_top μ A) (by norm_num)
  · exact ENNReal.div_ne_top (measure_ne_top μ B) (by norm_num)

/-- Lemma 3.4's two-node estimate, including the independent orientation coin. -/
theorem coin_averaged_intersection_saving
    {X Y Z : Type*} [MeasurableSpace X] [MeasurableSpace Y] [MeasurableSpace Z]
    (μX : Measure X) (μY : Measure Y) (μZ : Measure Z)
    [IsProbabilityMeasure μX] [IsProbabilityMeasure μY] [IsProbabilityMeasure μZ]
    {A : Set (X × Y)} {B : Set (Y × Z)}
    (hA : MeasurableSet A) (hB : MeasurableSet B) (δ : ℝ) (hδ : 0 ≤ δ)
    (hintersection : δ ≤ ((μX.prod μZ).prod μY).real (jointEvent A B)) :
    (fairOrientation.prod ((μX.prod μZ).prod (μY.prod μY))).real
      (coinChoice (forwardEvent A B) (oneOrderOnly A B)) ≤
        (μX.prod μY).real A * (μY.prod μZ).real B - δ ^ 2 / 2 := by
  rw [measureReal_coinChoice _ (measurableSet_forwardEvent hA hB)
    (measurableSet_oneOrderOnly hA hB), measureReal_forwardEvent μX μY μZ hA hB]
  have hs := intersection_saving_of_lower_bound μX μY μZ hA hB δ hδ hintersection
  linarith

theorem coin_averaged_saving_le_discounts
    {X Y Z : Type*} [MeasurableSpace X] [MeasurableSpace Y] [MeasurableSpace Z]
    (μX : Measure X) (μY : Measure Y) (μZ : Measure Z)
    [IsProbabilityMeasure μX] [IsProbabilityMeasure μY] [IsProbabilityMeasure μZ]
    {A : Set (X × Y)} {B : Set (Y × Z)}
    (hA : MeasurableSet A) (hB : MeasurableSet B) (δ : ℝ) (hδ : 0 ≤ δ)
    (hintersection : δ ≤ ((μX.prod μZ).prod μY).real (jointEvent A B))
    (ha : 0 < (μX.prod μY).real A) (hb : 0 < (μY.prod μZ).real B) :
    (fairOrientation.prod ((μX.prod μZ).prod (μY.prod μY))).real
      (coinChoice (forwardEvent A B) (oneOrderOnly A B)) ≤
      (μX.prod μY).real A * (μY.prod μZ).real B *
        (1 - 2 * savingFraction ((μX.prod μY).real A) ((μY.prod μZ).real B) δ) *
        (1 - 2 * savingFraction ((μY.prod μZ).real B) ((μX.prod μY).real A) δ) :=
  (coin_averaged_intersection_saving μX μY μZ hA hB δ hδ hintersection).trans
    (pair_saving_le_discounted _ _ δ ha hb)

end HLS

#check @HLS.fairOrientation_keep
#check @HLS.coinParameter_toNNReal
#check @HLS.coinParameter_symm_toNNReal
#check @HLS.fairOrientation_flip
#check @HLS.measurableSet_coinChoice
#check @HLS.measure_coinChoice
#check @HLS.measureReal_coinChoice
#check @HLS.coin_averaged_intersection_saving
#check @HLS.coin_averaged_saving_le_discounts
