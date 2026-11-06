/-
  HLS Theorem 3.13: summing the intersection-discounted DAG weights is
  bounded by the ordinary Shearer budget at p^- = p - delta^2 / 17.
  The proof uses the injective colored expansion and finite choice sums.
-/
module

public import PPGraph.HLS.Bounds.ChoiceSum

@[expose] public section

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option backward.isDefEq.respectTransparency false

open Classical
open scoped ENNReal

namespace HLS.WitnessDAG

variable {ι : Type} [Fintype ι] [DecidableEq ι] {G : SimpleGraph ι} {p : ι → ℝ}

noncomputable def refinedWeight (O : OverlapBounds G p) (D : HLS.WitnessDAG ι) : ℝ≥0∞ :=
  ∏ u ∈ D.nodes, if u ∈ arcNodes (matchingArcs O.matching D)
    then ENNReal.ofReal (O.prime u.1) else ENNReal.ofReal (p u.1)

theorem prime_eq_unmatched (O : OverlapBounds G p) (i : ι)
    (hi : O.matching.mate i = i) : O.prime i = p i := by
  simp [OverlapBounds.prime, primeWeight, O.unmatched i hi]

theorem refinedWeight_le_choiceSum (O : OverlapBounds G p)
    (hp : ∀ i, 0 < p i) (hp1 : ∀ i, p i ≤ 1) (D : HLS.WitnessDAG ι) (hD : D.Valid G) :
    refinedWeight O D ≤
      ∑' c : LegalChoices O.matching D, ∏ u : ↥D.nodes,
        choiceWeight O.matching (fun i => ENNReal.ofReal (O.splitUp i))
          (fun i => ENNReal.ofReal (O.splitDown i)) u.val.1 (c.val u) := by
  rw [tsum_legalChoiceWeight_eq O.matching D hD]
  unfold refinedWeight
  rw [← Finset.prod_coe_sort]
  apply Finset.prod_le_prod
  intro u _
  unfold forcedUp
  by_cases hpart : u.val ∈ arcNodes (matchingArcs O.matching D)
  · rw [ite_eq_left hpart, ite_eq_left (Or.inl hpart : forcedUp O.matching D u.val)]
    rfl
  · rw [ite_eq_right hpart]
    by_cases hm : O.matching.mate u.val.1 = u.val.1
    · rw [ite_eq_left (Or.inr hm : forcedUp O.matching D u.val)]
      exact le_of_eq (congrArg ENNReal.ofReal (prime_eq_unmatched O u.val.1 hm)).symm
    · have hforced : ¬ forcedUp O.matching D u.val := by
        intro h; exact h.elim hpart hm
      rw [ite_eq_right (not_or.mpr ⟨hpart, hm⟩)]
      have hup : ∀ i, 0 ≤ O.splitUp i := fun i => le_of_lt (O.prime_pos hp i)
      have hdn : ∀ i, 0 ≤ O.splitDown i := O.splitDown_nonneg hp hp1
      have hmulup := mul_nonneg (hdn u.val.1) (hup (O.matching.mate u.val.1))
      have hmuldn := mul_nonneg (hdn u.val.1) (hdn (O.matching.mate u.val.1))
      have hsave := ENNReal.ofReal_le_ofReal (O.four_choices_dominate hp hp1 u.val.1)
      rw [ENNReal.ofReal_add (add_nonneg (add_nonneg (hup _) (hdn _)) hmulup) hmuldn,
        ENNReal.ofReal_add (add_nonneg (hup _) (hdn _)) hmulup,
        ENNReal.ofReal_add (hup _) (hdn _), ENNReal.ofReal_mul (hdn _),
        ENNReal.ofReal_mul (hdn _)] at hsave
      exact hsave

theorem tsum_refinedWeight_le_decorated (O : OverlapBounds G p)
    (hp : ∀ i, 0 < p i) (hp1 : ∀ i, p i ≤ 1) (α : ι) :
    (∑' D : ProperFamily G Finset.univ α, refinedWeight O D.val) ≤
      ∑' C : DecoratedFamily G Finset.univ α,
        decorationWeight (fun i => ENNReal.ofReal (O.splitUp i))
          (fun i => ENNReal.ofReal (O.splitDown i)) C.1.val C.2.val := by
  calc
    _ ≤ ∑' D : ProperFamily G Finset.univ α, ∑' c : LegalChoices O.matching D.val,
        ∏ u : ↥D.val.nodes, choiceWeight O.matching (fun i => ENNReal.ofReal (O.splitUp i))
          (fun i => ENNReal.ofReal (O.splitDown i)) u.val.1 (c.val u) :=
      ENNReal.tsum_le_tsum (fun D => refinedWeight_le_choiceSum O hp hp1 D.val D.property.1)
    _ = ∑' F : ExpansionFamily O.matching α,
        decorationWeight (fun i => ENNReal.ofReal (O.splitUp i))
          (fun i => ENNReal.ofReal (O.splitDown i)) (expansionFamilyMap O.matching α F).1.val
            (expansionFamilyMap O.matching α F).2.val := by
      rw [← ENNReal.tsum_sigma]
      exact tsum_congr (fun F => (expansionFamilyMap_weight O.matching α _ _ F).symm)
    _ ≤ _ := ENNReal.tsum_comp_le_tsum_of_injective (expansionFamilyMap_injective O.matching α)
      (fun C => decorationWeight (fun i => ENNReal.ofReal (O.splitUp i))
        (fun i => ENNReal.ofReal (O.splitDown i)) C.1.val C.2.val)

/-- Weighted expansion supplies the smaller p^- budget, without a runtime premise. -/
theorem tsum_refinedWeight_le_stableBudget (O : OverlapBounds G p)
    (hp : ∀ i, 0 < p i) (hp1 : ∀ i, p i ≤ 1) (α : ι)
    (hc : Shearer.StrictCriterion G O.reduced Finset.univ) :
    (∑' D : ProperFamily G Finset.univ α, refinedWeight O D.val) ≤
      ENNReal.ofReal (Shearer.stableBudget G O.reduced Finset.univ {α}) :=
  (tsum_refinedWeight_le_decorated O hp hp1 α).trans
    (tsum_split_decoratedFamily_le_budget G p O hp hp1 Finset.univ α (Finset.mem_univ _) hc)

end HLS.WitnessDAG

#check @HLS.WitnessDAG.prime_eq_unmatched
#check @HLS.WitnessDAG.refinedWeight_le_choiceSum
#check @HLS.WitnessDAG.tsum_refinedWeight_le_decorated
#check @HLS.WitnessDAG.tsum_refinedWeight_le_stableBudget
