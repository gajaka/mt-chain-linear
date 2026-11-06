/-
  PPGraphMoserTardosIntersection.lean

  He--Li--Sun, Proposition 3.3: the intersection saving for two orders
  of resampling shared variables. Independent private blocks X and Z
  are kept fixed while the shared block Y is sampled twice.

  Source: "Moser-Tardos Algorithm: Beyond Shearer's Bound",
  arXiv:2111.06527, Proposition 3.3, p. 12.
  https://arxiv.org/abs/2111.06527

  This is the local probability estimate used by the stronger criterion;
  its connection to witness DAGs and the final MT convergence theorem
  is subsequent work. All spaces below are arbitrary measurable spaces.
-/

module

public import Mathlib.Probability.Moments.Variance
public import Mathlib.MeasureTheory.Measure.Prod
public import Mathlib.Tactic

@[expose] public section

set_option autoImplicit false

open MeasureTheory ProbabilityTheory Classical
open scoped ENNReal

namespace HLS

section DoubleSample

variable {U Y : Type*} [MeasurableSpace U] [MeasurableSpace Y]

/-- The same event is tested twice with independent shared-block samples. -/
def doubleEvent (C : Set (U × Y)) : Set (U × (Y × Y)) :=
  {w | (w.1, w.2.1) ∈ C ∧ (w.1, w.2.2) ∈ C}

theorem measurableSet_doubleEvent {C : Set (U × Y)} (hC : MeasurableSet C) :
    MeasurableSet (doubleEvent C) := by
  exact (hC.preimage (by fun_prop : Measurable (fun w : U × (Y × Y) =>
    (w.1, w.2.1)))).inter
      (hC.preimage (by fun_prop : Measurable (fun w : U × (Y × Y) =>
        (w.1, w.2.2))))

/-- Conditioning on the private block turns the double test into a square. -/
theorem measure_doubleEvent (μ : Measure U) (ν : Measure Y) [SFinite ν]
    {C : Set (U × Y)} (hC : MeasurableSet C) :
    (μ.prod (ν.prod ν)) (doubleEvent C) =
      ∫⁻ u, (ν (Prod.mk u ⁻¹' C)) ^ 2 ∂μ := by
  rw [Measure.prod_apply (measurableSet_doubleEvent hC)]
  apply lintegral_congr
  intro u
  have hsection : Prod.mk u ⁻¹' doubleEvent C =
      (Prod.mk u ⁻¹' C) ×ˢ (Prod.mk u ⁻¹' C) := by
    ext y
    rfl
  rw [hsection, Measure.prod_prod, pow_two]

/-- The probability of both tests is at least the square of the probability
of one test. This is the usual second-moment inequality on a probability law. -/
theorem sq_measureReal_le_doubleEvent (μ : Measure U) (ν : Measure Y)
    [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]
    {C : Set (U × Y)} (hC : MeasurableSet C) :
    ((μ.prod ν).real C) ^ 2 ≤ (μ.prod (ν.prod ν)).real (doubleEvent C) := by
  let f : U → ℝ≥0∞ := fun u => ν (Prod.mk u ⁻¹' C)
  have hf : Measurable f := measurable_measure_prodMk_left hC
  have hfr : Measurable (fun u => (f u).toReal) := hf.ennreal_toReal
  have hb (u : U) : (f u).toReal ∈ Set.Icc (0 : ℝ) 1 :=
    ⟨ENNReal.toReal_nonneg, measureReal_le_one⟩
  have hLp : MemLp (fun u => (f u).toReal) 2 μ :=
    memLp_of_bounded (Filter.Eventually.of_forall hb) hfr.aestronglyMeasurable 2
  have hv := variance_nonneg (fun u => (f u).toReal) μ
  rw [variance_eq_sub hLp] at hv
  have hmean : (∫ u, (f u).toReal ∂μ) = (μ.prod ν).real C := by
    rw [integral_toReal hf.aemeasurable
      (Filter.Eventually.of_forall (fun u => measure_lt_top ν _))]
    rw [measureReal_def, Measure.prod_apply hC]
  have hsecond : (∫ u, ((f u).toReal) ^ 2 ∂μ) =
      (μ.prod (ν.prod ν)).real (doubleEvent C) := by
    rw [measureReal_def, measure_doubleEvent μ ν hC]
    simpa only [ENNReal.toReal_pow] using
      (integral_toReal (hf.pow_const 2).aemeasurable
        (Filter.Eventually.of_forall (fun u =>
          ENNReal.pow_lt_top (measure_lt_top ν _))))
  change 0 ≤ (∫ u, ((f u).toReal) ^ 2 ∂μ) - (∫ u, (f u).toReal ∂μ) ^ 2 at hv
  rw [hmean, hsecond] at hv
  linarith

end DoubleSample

section Intersection

variable {X Y Z : Type*} [MeasurableSpace X] [MeasurableSpace Y] [MeasurableSpace Z]

/-- Both events hold with the same shared-block assignment. -/
def jointEvent (A : Set (X × Y)) (B : Set (Y × Z)) : Set ((X × Z) × Y) :=
  {w | (w.1.1, w.2) ∈ A ∧ (w.2, w.1.2) ∈ B}

/-- The first order uses Y₁ for A and an independent Y₂ for B. -/
def forwardEvent (A : Set (X × Y)) (B : Set (Y × Z)) :
    Set ((X × Z) × (Y × Y)) :=
  {w | (w.1.1, w.2.1) ∈ A ∧ (w.2.2, w.1.2) ∈ B}

/-- The first order passes, while the other order fails at least one test. -/
def oneOrderOnly (A : Set (X × Y)) (B : Set (Y × Z)) :
    Set ((X × Z) × (Y × Y)) :=
  {w | (w.1.1, w.2.1) ∈ A ∧ (w.2.2, w.1.2) ∈ B ∧
    ((w.1.1, w.2.2) ∉ A ∨ (w.2.1, w.1.2) ∉ B)}

theorem measurableSet_jointEvent {A : Set (X × Y)} {B : Set (Y × Z)}
    (hA : MeasurableSet A) (hB : MeasurableSet B) :
    MeasurableSet (jointEvent A B) := by
  exact (hA.preimage (by fun_prop : Measurable (fun w : (X × Z) × Y =>
    (w.1.1, w.2)))).inter
      (hB.preimage (by fun_prop : Measurable (fun w : (X × Z) × Y =>
        (w.2, w.1.2))))

theorem measurableSet_forwardEvent {A : Set (X × Y)} {B : Set (Y × Z)}
    (hA : MeasurableSet A) (hB : MeasurableSet B) :
    MeasurableSet (forwardEvent A B) := by
  exact (hA.preimage (by fun_prop : Measurable (fun w : (X × Z) × (Y × Y) =>
    (w.1.1, w.2.1)))).inter
      (hB.preimage (by fun_prop : Measurable (fun w : (X × Z) × (Y × Y) =>
        (w.2.2, w.1.2))))

omit [MeasurableSpace X] [MeasurableSpace Y] [MeasurableSpace Z] in
theorem doubleJoint_subset_forward (A : Set (X × Y)) (B : Set (Y × Z)) :
    doubleEvent (jointEvent A B) ⊆ forwardEvent A B := by
  intro w hw
  exact ⟨hw.1.1, hw.2.2⟩

omit [MeasurableSpace X] [MeasurableSpace Y] [MeasurableSpace Z] in
theorem oneOrderOnly_eq_sdiff (A : Set (X × Y)) (B : Set (Y × Z)) :
    oneOrderOnly A B = forwardEvent A B \ doubleEvent (jointEvent A B) := by
  ext w
  simp only [oneOrderOnly, forwardEvent, doubleEvent, jointEvent,
    Set.mem_ofPred_eq, Set.mem_sdiff]
  tauto

theorem measurableSet_oneOrderOnly {A : Set (X × Y)} {B : Set (Y × Z)}
    (hA : MeasurableSet A) (hB : MeasurableSet B) :
    MeasurableSet (oneOrderOnly A B) := by
  rw [oneOrderOnly_eq_sdiff]
  exact (measurableSet_forwardEvent hA hB).diff
    (measurableSet_doubleEvent (measurableSet_jointEvent hA hB))

/-- Private/shared blocks in this order are disjoint independent samples,
so the probability before excluding the other order is the product. -/
theorem measure_forwardEvent (μX : Measure X) (μY : Measure Y) (μZ : Measure Z)
    [SFinite μX] [SFinite μY] [SFinite μZ]
    {A : Set (X × Y)} {B : Set (Y × Z)}
    (hA : MeasurableSet A) (hB : MeasurableSet B) :
    ((μX.prod μZ).prod (μY.prod μY)) (forwardEvent A B) =
      (μX.prod μY) A * (μY.prod μZ) B := by
  rw [Measure.prod_apply (measurableSet_forwardEvent hA hB)]
  have hsection (u : X × Z) : Prod.mk u ⁻¹' forwardEvent A B =
      (Prod.mk u.1 ⁻¹' A) ×ˢ ((fun y => (y, u.2)) ⁻¹' B) := by
    ext y
    rfl
  simp_rw [hsection, Measure.prod_prod]
  rw [lintegral_prod_mul (measurable_measure_prodMk_left hA).aemeasurable
    (measurable_measure_prodMk_right hB).aemeasurable]
  rw [← Measure.prod_apply hA, ← Measure.prod_apply_symm hB]

theorem measureReal_forwardEvent (μX : Measure X) (μY : Measure Y) (μZ : Measure Z)
    [SFinite μX] [SFinite μY] [SFinite μZ]
    {A : Set (X × Y)} {B : Set (Y × Z)}
    (hA : MeasurableSet A) (hB : MeasurableSet B) :
    ((μX.prod μZ).prod (μY.prod μY)).real (forwardEvent A B) =
      (μX.prod μY).real A * (μY.prod μZ).real B := by
  simp only [measureReal_def, measure_forwardEvent μX μY μZ hA hB,
    ENNReal.toReal_mul]

/-- He--Li--Sun Proposition 3.3, on the product law of X, Z, Y₁, Y₂.
The private X and Z blocks may themselves be arbitrary product spaces. -/
theorem intersection_saving (μX : Measure X) (μY : Measure Y) (μZ : Measure Z)
    [IsProbabilityMeasure μX] [IsProbabilityMeasure μY] [IsProbabilityMeasure μZ]
    {A : Set (X × Y)} {B : Set (Y × Z)}
    (hA : MeasurableSet A) (hB : MeasurableSet B) :
    ((μX.prod μZ).prod (μY.prod μY)).real (oneOrderOnly A B) ≤
      (μX.prod μY).real A * (μY.prod μZ).real B -
        (((μX.prod μZ).prod μY).real (jointEvent A B)) ^ 2 := by
  rw [oneOrderOnly_eq_sdiff,
    measureReal_sdiff (doubleJoint_subset_forward A B)
      (measurableSet_doubleEvent (measurableSet_jointEvent hA hB)),
    measureReal_forwardEvent μX μY μZ hA hB]
  have h := sq_measureReal_le_doubleEvent (μX.prod μZ) μY
    (measurableSet_jointEvent hA hB)
  linarith

/-- A certified lower bound δ on the intersection gives a saving of δ². -/
theorem intersection_saving_of_lower_bound
    (μX : Measure X) (μY : Measure Y) (μZ : Measure Z)
    [IsProbabilityMeasure μX] [IsProbabilityMeasure μY] [IsProbabilityMeasure μZ]
    {A : Set (X × Y)} {B : Set (Y × Z)}
    (hA : MeasurableSet A) (hB : MeasurableSet B) (δ : ℝ) (hδ : 0 ≤ δ)
    (hintersection : δ ≤ ((μX.prod μZ).prod μY).real (jointEvent A B)) :
    ((μX.prod μZ).prod (μY.prod μY)).real (oneOrderOnly A B) ≤
      (μX.prod μY).real A * (μY.prod μZ).real B - δ ^ 2 := by
  have h := intersection_saving μX μY μZ hA hB
  have hs : δ ^ 2 ≤ (((μX.prod μZ).prod μY).real (jointEvent A B)) ^ 2 := by
    nlinarith [mul_nonneg (sub_nonneg.mpr hintersection) hδ]
  linarith

/-- Positive overlap makes the upper bound strictly smaller than the
independent first-order product. -/
theorem intersection_saving_strict
    (μX : Measure X) (μY : Measure Y) (μZ : Measure Z)
    [IsProbabilityMeasure μX] [IsProbabilityMeasure μY] [IsProbabilityMeasure μZ]
    {A : Set (X × Y)} {B : Set (Y × Z)}
    (hA : MeasurableSet A) (hB : MeasurableSet B)
    (hintersection : 0 < ((μX.prod μZ).prod μY).real (jointEvent A B)) :
    ((μX.prod μZ).prod (μY.prod μY)).real (oneOrderOnly A B) <
      (μX.prod μY).real A * (μY.prod μZ).real B := by
  have h := intersection_saving μX μY μZ hA hB
  nlinarith [sq_pos_of_pos hintersection]

end Intersection

end HLS

#check @HLS.measurableSet_doubleEvent
#check @HLS.measure_doubleEvent
#check @HLS.sq_measureReal_le_doubleEvent
#check @HLS.measurableSet_jointEvent
#check @HLS.measurableSet_forwardEvent
#check @HLS.doubleJoint_subset_forward
#check @HLS.oneOrderOnly_eq_sdiff
#check @HLS.measurableSet_oneOrderOnly
#check @HLS.measure_forwardEvent
#check @HLS.measureReal_forwardEvent
#check @HLS.intersection_saving
#check @HLS.intersection_saving_of_lower_bound
#check @HLS.intersection_saving_strict
