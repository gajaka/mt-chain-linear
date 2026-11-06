/- Exact weight preservation for the four-choice colored expansion. -/
module

public import PPGraph.HLS.Encoding.ExpansionFamily
public import Mathlib.Algebra.BigOperators.Ring.Finset

@[expose] public section

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option backward.isDefEq.respectTransparency false

open Classical
open scoped ENNReal

namespace HLS.WitnessDAG

variable {ι : Type} [Fintype ι] [DecidableEq ι] {G : SimpleGraph ι}

noncomputable def choiceWeight (M : DependencyMatching G) (up down : ι → ℝ≥0∞)
    (i : ι) : ExpansionChoice → ℝ≥0∞
  | .up => up i
  | .down => down i
  | .insertUp => down i * up (M.mate i)
  | .insertDown => down i * down (M.mate i)

theorem decorationWeight_eq_prod (up down : ι → ℝ≥0∞) (D : HLS.WitnessDAG ι)
    (R : Finset (WNode ι)) (hR : R ⊆ D.nodes) :
    decorationWeight up down D R = ∏ u ∈ D.nodes, if u ∈ R then down u.1 else up u.1 := by
  rw [Finset.prod_ite, Finset.filter_mem_eq_inter, Finset.inter_eq_right.mpr hR,
    ← Finset.sdiff_eq_filter]
  rfl

theorem expandedNodes_prod (M : DependencyMatching G) (D : HLS.WitnessDAG ι)
    (choice : WNode ι → ExpansionChoice) (up down : ι → ℝ≥0∞) :
    (∏ x ∈ expandedNodes D choice,
      if expandedDown choice x then down (expandedLabel M x) else up (expandedLabel M x)) =
    ∏ u ∈ D.nodes, choiceWeight M up down u.1 (choice u) := by
  have hd : Disjoint (D.nodes.image (fun u => (u, false)))
      ((D.nodes.filter (fun u => needsExtra (choice u))).image (fun u => (u, true))) := by
    apply Finset.disjoint_left.mpr
    intro x hx hy
    obtain ⟨u, _, hux⟩ := Finset.mem_image.mp hx
    obtain ⟨v, _, hvx⟩ := Finset.mem_image.mp hy
    have h : false = true := congrArg Prod.snd (hux.trans hvx.symm)
    cases h
  rw [expandedNodes, Finset.prod_union hd,
    Finset.prod_image (fun _ _ _ _ h => congrArg Prod.fst h),
    Finset.prod_image (fun _ _ _ _ h => congrArg Prod.fst h)]
  rw [Finset.prod_filter, ← Finset.prod_mul_distrib]
  apply Finset.prod_congr rfl
  intro u _
  cases h : choice u <;> simp [expandedDown, expandedLabel, originalDown, needsExtra, choiceWeight, h]

theorem coloredExpansion_weight (M : DependencyMatching G) (D : HLS.WitnessDAG ι)
    (hD : D.Valid G) (choice : WNode ι → ExpansionChoice) (up down : ι → ℝ≥0∞) :
    decorationWeight up down (coloredExpansion M D hD choice).1 (coloredExpansion M D hD choice).2 =
      ∏ u ∈ D.nodes, choiceWeight M up down u.1 (choice u) := by
  rw [decorationWeight_eq_prod up down _ _ (coloredExpansion_down_subset M D hD choice)]
  change (∏ w ∈ ((expandedNodes D choice).image (expansionEmbed M)).image
    (rawExpansion M D hD choice).canonicalName,
    if w ∈ (coloredExpansion M D hD choice).2 then down w.1 else up w.1) = _
  rw [Finset.image_image]
  change (∏ w ∈ (expandedNodes D choice).image (expansionName M D hD choice),
    if w ∈ (coloredExpansion M D hD choice).2 then down w.1 else up w.1) = _
  rw [Finset.prod_image (expansionName_injective M D hD choice)]
  calc
    _ = ∏ x ∈ expandedNodes D choice,
        if expandedDown choice x then down (expandedLabel M x) else up (expandedLabel M x) := by
      apply Finset.prod_congr rfl
      intro x hx
      change (if expansionName M D hD choice x ∈ (coloredExpansion M D hD choice).2
        then down (expandedLabel M x) else up (expandedLabel M x)) = _
      simp only [mem_expansionDown_iff M D hD choice x hx]
    _ = _ := expandedNodes_prod M D choice up down

theorem expansionFamilyMap_weight (M : DependencyMatching G) (α : ι)
    (up down : ι → ℝ≥0∞) (F : ExpansionFamily M α) :
    decorationWeight up down (expansionFamilyMap M α F).1.val (expansionFamilyMap M α F).2.val =
      ∏ u : ↥F.1.val.nodes, choiceWeight M up down u.val.1 (F.2.val u) := by
  change decorationWeight up down
    (coloredExpansion M F.1.val F.1.property.1 (extendChoice F.1.val F.2.val)).1
    (coloredExpansion M F.1.val F.1.property.1 (extendChoice F.1.val F.2.val)).2 = _
  rw [coloredExpansion_weight M F.1.val F.1.property.1 _ up down]
  rw [← Finset.prod_coe_sort]
  apply Finset.prod_congr rfl
  intro u _
  rw [extendChoice_mem]

end HLS.WitnessDAG

#check @HLS.WitnessDAG.decorationWeight_eq_prod
#check @HLS.WitnessDAG.expandedNodes_prod
#check @HLS.WitnessDAG.coloredExpansion_weight
#check @HLS.WitnessDAG.expansionFamilyMap_weight
