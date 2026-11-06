/- The disjoint selected-pair product and the half-cover discount. -/
module

public import PPGraph.HLS.Bounds.RefinedBudget

@[expose] public section

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option backward.isDefEq.respectTransparency false

open Classical
open scoped ENNReal

namespace HLS.WitnessDAG

variable {ι : Type} [Fintype ι] [DecidableEq ι] {G : SimpleGraph ι}

theorem arcNodes_subset (M : DependencyMatching G) (D : HLS.WitnessDAG ι)
    (hD : D.Valid G) : arcNodes (matchingArcs M D) ⊆ D.nodes := by
  intro u hu
  obtain ⟨e, he, hue⟩ := Finset.mem_biUnion.mp hu
  have he' := (Finset.mem_filter.mp he).1
  simp only [Finset.mem_insert, Finset.mem_singleton] at hue
  rcases hue with rfl | rfl
  · exact (hD.supported _ _ he').1
  · exact (hD.supported _ _ he').2

theorem selected_arcNodes_subset (M : DependencyMatching G) (D : HLS.WitnessDAG ι)
    (hD : D.Valid G) : arcNodes (selectedArcs M D) ⊆ D.nodes := by
  intro u hu
  obtain ⟨e, he, hue⟩ := Finset.mem_biUnion.mp hu
  exact arcNodes_subset M D hD (Finset.mem_biUnion.mpr ⟨e, selectedArcs_subset M D he, hue⟩)

theorem prod_selected_endpoints {A : Type*} [CommMonoid A]
    (M : DependencyMatching G) (D : HLS.WitnessDAG ι) (hD : D.Valid G) (f : WNode ι → A) :
    (∏ e ∈ selectedArcs M D, f e.1 * f e.2) = ∏ u ∈ arcNodes (selectedArcs M D), f u := by
  rw [arcNodes, Finset.prod_biUnion]
  · apply Finset.prod_congr rfl
    intro e he
    have hl := (Finset.mem_filter.mp (selectedArcs_subset M D he)).2.2.1
    have hne : e.1 ≠ e.2 := by intro h; exact hl (congrArg Prod.fst h)
    simp [hne]
  · intro e he f hf hne
    exact selectedArcs_endpoints_disjoint M D hD e he f hf hne

theorem prod_nodes_by_label {A : Type*} [CommMonoid A]
    (N : Finset (WNode ι)) (f : ι → A) :
    (∏ u ∈ N, f u.1) = ∏ i : ι, (f i) ^ (N.filter (fun u => u.1 = i)).card := by
  have h := Finset.prod_fiberwise_eq_prod_filter' N Finset.univ (fun u => u.1) f
  simp only [Finset.mem_univ, Finset.filter_true, Finset.prod_const] at h
  exact h.symm

theorem selected_discount_le (p : ι → ℝ) (O : OverlapBounds G p)
    (hp : ∀ i, 0 < p i) (D : HLS.WitnessDAG ι) (hD : D.Valid G) :
    (∏ u ∈ arcNodes (selectedArcs O.matching D), (1 - 2 * O.discount u.1)) ≤
      ∏ u ∈ arcNodes (matchingArcs O.matching D), (1 - O.discount u.1) := by
  rw [prod_nodes_by_label _ (fun i => 1 - 2 * O.discount i),
    prod_nodes_by_label _ (fun i => 1 - O.discount i)]
  apply Finset.prod_le_prod₀
  · intro i _
    have hc := O.discount_le hp i
    exact pow_nonneg (by linarith) _
  · intro i _
    exact half_cover_discount _ (O.discount_nonneg hp i) (by linarith [O.discount_le hp i]) _ _
      (selectedArcs_half_incident_nodes O.matching D hD i)

theorem refinedWeight_eq_prod_discount (p : ι → ℝ) (O : OverlapBounds G p)
    (hp : ∀ i, 0 < p i) (D : HLS.WitnessDAG ι) (hD : D.Valid G) :
    refinedWeight O D = ENNReal.ofReal
      ((∏ u ∈ D.nodes, p u.1) * ∏ u ∈ arcNodes (matchingArcs O.matching D), (1 - O.discount u.1)) := by
  have hN := arcNodes_subset O.matching D hD
  have hn : ∀ u ∈ D.nodes, 0 ≤ (if u ∈ arcNodes (matchingArcs O.matching D)
      then O.prime u.1 else p u.1) := by
    intro u _
    split_ifs
    · exact le_of_lt (O.prime_pos hp _)
    · exact le_of_lt (hp _)
  have hprod : (∏ u ∈ D.nodes, if u ∈ arcNodes (matchingArcs O.matching D)
      then O.prime u.1 else p u.1) =
      (∏ u ∈ D.nodes, p u.1) * ∏ u ∈ arcNodes (matchingArcs O.matching D), (1 - O.discount u.1) := by
    simp_rw [O.prime_eq_mul hp]
    calc
      _ = ∏ u ∈ D.nodes, p u.1 * (if u ∈ arcNodes (matchingArcs O.matching D) then 1 - O.discount u.1 else 1) := by
        apply Finset.prod_congr rfl
        intro u _
        split_ifs <;> simp
      _ = _ := by rw [Finset.prod_mul_distrib, Finset.prod_ite, Finset.filter_mem_eq_inter,
        Finset.inter_eq_right.mpr hN]; simp
  rw [← hprod, ENNReal.ofReal_prod_of_nonneg hn]
  unfold refinedWeight
  exact Finset.prod_congr rfl (fun u _ => by split_ifs <;> rfl)

theorem selected_pair_product_le_refined (p : ι → ℝ) (O : OverlapBounds G p)
    (hp : ∀ i, 0 < p i) (D : HLS.WitnessDAG ι) (hD : D.Valid G) :
    ENNReal.ofReal
      ((∏ u ∈ D.nodes \ arcNodes (selectedArcs O.matching D), p u.1) *
        ∏ e ∈ selectedArcs O.matching D,
          p e.1.1 * p e.2.1 * (1 - 2 * O.discount e.1.1) * (1 - 2 * O.discount e.2.1)) ≤
      refinedWeight O D := by
  have heq : (∏ e ∈ selectedArcs O.matching D,
      p e.1.1 * p e.2.1 * (1 - 2 * O.discount e.1.1) * (1 - 2 * O.discount e.2.1)) =
      (∏ u ∈ arcNodes (selectedArcs O.matching D), p u.1) *
        ∏ u ∈ arcNodes (selectedArcs O.matching D), (1 - 2 * O.discount u.1) := by
    calc
      _ = ∏ e ∈ selectedArcs O.matching D,
          (p e.1.1 * (1 - 2 * O.discount e.1.1)) * (p e.2.1 * (1 - 2 * O.discount e.2.1)) := by
        apply Finset.prod_congr rfl
        intro e _
        ring
      _ = ∏ u ∈ arcNodes (selectedArcs O.matching D), p u.1 * (1 - 2 * O.discount u.1) :=
        prod_selected_endpoints O.matching D hD (fun u => p u.1 * (1 - 2 * O.discount u.1))
      _ = _ := Finset.prod_mul_distrib
  rw [heq, ← mul_assoc, Finset.prod_sdiff (selected_arcNodes_subset O.matching D hD),
    refinedWeight_eq_prod_discount p O hp D hD]
  apply ENNReal.ofReal_le_ofReal
  exact mul_le_mul_of_nonneg_left (selected_discount_le p O hp D hD)
    (Finset.prod_nonneg (fun u _ => le_of_lt (hp u.1)))

end HLS.WitnessDAG

#check @HLS.WitnessDAG.arcNodes_subset
#check @HLS.WitnessDAG.selected_arcNodes_subset
#check @HLS.WitnessDAG.prod_selected_endpoints
#check @HLS.WitnessDAG.prod_nodes_by_label
#check @HLS.WitnessDAG.selected_discount_le
#check @HLS.WitnessDAG.refinedWeight_eq_prod_discount
#check @HLS.WitnessDAG.selected_pair_product_le_refined
