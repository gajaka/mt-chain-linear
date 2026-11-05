/- HLS Lemma 3.4: the whole-DAG probability is bounded by its refined weight. -/
module

public import PPGraph.HLS.Probability.UnitChecks
public import PPGraph.HLS.Bounds.ProductDiscount

@[expose] public section

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option backward.isDefEq.respectTransparency false

open Classical MeasureTheory
open scoped ENNReal

namespace HLS.WitnessDAG

variable {V : Type} [DecidableEq V] [Fintype V] {S : VarSpaces V}
  {ι : Type} [Fintype ι] [DecidableEq ι] [Nonempty ι]

theorem measure_originalTable_tableEvent_eq (P : MTProcess S ι) (D : HLS.WitnessDAG ι)
    (hbad : ∀ i, MeasurableSet (P.bad i)) (u : WNode ι) :
    logMeasure (augmentedSpaces (ι := ι) S)
      ((originalTable (S := S) (ι := ι)) ⁻¹' tableEvent P D u) =
      ENNReal.ofReal ((Measure.pi (fun a => S.measure a)).real (P.bad u.1)) := by
  have : ∀ a, IsProbabilityMeasure (S.measure a) := S.isProb
  calc
    _ = logMeasure S (tableEvent P D u) :=
      (Measure.map_apply (μ := logMeasure (augmentedSpaces (ι := ι) S))
        (measurable_originalTable S) (measurableSet_tableEvent P D hbad u)).symm.trans
          (congrArg (fun μ => μ (tableEvent P D u)) (map_originalTable (ι := ι) S))
    _ = Measure.pi (fun a => S.measure a) (P.bad u.1) := logMeasure_tableEvent_eq_pi P D hbad u
    _ = _ := (ENNReal.ofReal_toReal (measure_ne_top _ _)).symm

theorem measure_augmentedPairCheck_le_discount (P : MTProcess S ι)
    (hbad : ∀ i, MeasurableSet (P.bad i)) (p : ι → ℝ)
    (hprob : ∀ i, (Measure.pi (fun a => S.measure a)).real (P.bad i) = p i)
    (hp : ∀ i, 0 < p i) (O : OverlapBounds (Shearer.dependencyGraph P.footprint) p)
    (hInt : ∀ i, O.delta i ≤ (Measure.pi (fun a => S.measure a)).real
      (P.bad i ∩ P.bad (O.matching.mate i)))
    (D : HLS.WitnessDAG ι) (hD : D.Valid (Shearer.dependencyGraph P.footprint))
    (e : WNode ι × WNode ι) (he : e ∈ selectedArcs O.matching D) :
    logMeasure (augmentedSpaces S) (augmentedPairCheck P O.matching D e.1 e.2) ≤
      ENNReal.ofReal (p e.1.1 * p e.2.1 * (1 - 2 * O.discount e.1.1) * (1 - 2 * O.discount e.2.1)) := by
  obtain ⟨he, hm, _, _⟩ := Finset.mem_filter.mp (selectedArcs_subset O.matching D he)
  have hi : O.delta e.1.1 ≤ (Measure.pi (fun a => S.measure a)).real (P.bad e.1.1 ∩ P.bad e.2.1) := by
    simpa only [hm] using hInt e.1.1
  have hs := measureReal_augmentedPairCheck_le P O.matching D hD e.1 e.2 he hbad
    (O.delta e.1.1) (O.nonneg _) hi
  rw [hprob _, hprob _] at hs
  have hmv : O.matching.mate e.2.1 = e.1.1 := by rw [← hm]; exact O.matching.involutive _
  have hdv : O.delta e.2.1 = O.delta e.1.1 := by rw [← hm]; exact O.symmetric _
  have hs' : (logMeasure (augmentedSpaces S)).real (augmentedPairCheck P O.matching D e.1 e.2) ≤
      p e.1.1 * p e.2.1 * (1 - 2 * O.discount e.1.1) * (1 - 2 * O.discount e.2.1) := by
    apply hs.trans
    change _ ≤ p e.1.1 * p e.2.1 *
      (1 - 2 * savingFraction (p e.1.1) (p (O.matching.mate e.1.1)) (O.delta e.1.1)) *
      (1 - 2 * savingFraction (p e.2.1) (p (O.matching.mate e.2.1)) (O.delta e.2.1))
    rw [hm, hmv, hdv]
    exact pair_saving_le_discounted _ _ _ (hp _) (hp _)
  have hsENN := ENNReal.ofReal_le_ofReal hs'
  rw [measureReal_def, ENNReal.ofReal_toReal (measure_ne_top _ _)] at hsENN
  exact hsENN

/-- Independent units, pair saving, and half-cover yield the refined DAG weight. -/
theorem logMeasure_unitCheck_le_refinedWeight (P : MTProcess S ι)
    (hbad : ∀ i, MeasurableSet (P.bad i)) (p : ι → ℝ)
    (hprob : ∀ i, (Measure.pi (fun a => S.measure a)).real (P.bad i) = p i)
    (hp : ∀ i, 0 < p i) (O : OverlapBounds (Shearer.dependencyGraph P.footprint) p)
    (hInt : ∀ i, O.delta i ≤ (Measure.pi (fun a => S.measure a)).real
      (P.bad i ∩ P.bad (O.matching.mate i)))
    (D : HLS.WitnessDAG ι) (hD : D.Valid (Shearer.dependencyGraph P.footprint)) :
    logMeasure (augmentedSpaces S) (unitCheck P O.matching D) ≤ refinedWeight O D := by
  have hpairNN (e : WNode ι × WNode ι) :
      0 ≤ p e.1.1 * p e.2.1 * (1 - 2 * O.discount e.1.1) * (1 - 2 * O.discount e.2.1) := by
    have h₁ := O.discount_le hp e.1.1
    have h₂ := O.discount_le hp e.2.1
    exact mul_nonneg (mul_nonneg (mul_nonneg (hp _).le (hp _).le) (by linarith)) (by linarith)
  calc
    _ = (∏ u ∈ D.nodes \ arcNodes (selectedArcs O.matching D), ENNReal.ofReal (p u.1)) *
        ∏ e ∈ selectedArcs O.matching D,
          logMeasure (augmentedSpaces S) (augmentedPairCheck P O.matching D e.1 e.2) := by
      rw [logMeasure_unitCheck_eq_split_prod P O.matching D hD hbad]
      congr 1
      exact Finset.prod_congr rfl (fun u _ => by rw [measure_originalTable_tableEvent_eq P D hbad u, hprob _])
    _ ≤ (∏ u ∈ D.nodes \ arcNodes (selectedArcs O.matching D), ENNReal.ofReal (p u.1)) *
        ∏ e ∈ selectedArcs O.matching D,
          ENNReal.ofReal (p e.1.1 * p e.2.1 * (1 - 2 * O.discount e.1.1) * (1 - 2 * O.discount e.2.1)) := by
      exact mul_le_mul' le_rfl (Finset.prod_le_prod (fun e he =>
        measure_augmentedPairCheck_le_discount P hbad p hprob hp O hInt D hD e he))
    _ = ENNReal.ofReal
        ((∏ u ∈ D.nodes \ arcNodes (selectedArcs O.matching D), p u.1) *
          ∏ e ∈ selectedArcs O.matching D,
            p e.1.1 * p e.2.1 * (1 - 2 * O.discount e.1.1) * (1 - 2 * O.discount e.2.1)) := by
      rw [← ENNReal.ofReal_prod_of_nonneg (fun u _ => (hp u.1).le),
        ← ENNReal.ofReal_prod_of_nonneg (fun e _ => hpairNN e),
        ENNReal.ofReal_mul (Finset.prod_nonneg (fun u _ => (hp u.1).le))]
    _ ≤ _ := selected_pair_product_le_refined p O hp D hD

end HLS.WitnessDAG

#check @HLS.WitnessDAG.measure_originalTable_tableEvent_eq
#check @HLS.WitnessDAG.measure_augmentedPairCheck_le_discount
#check @HLS.WitnessDAG.logMeasure_unitCheck_le_refinedWeight
