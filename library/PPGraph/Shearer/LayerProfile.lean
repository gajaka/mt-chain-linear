/-
  Layer profiles of MT witness trees. Equal profiles preserve the checks,
  occurrence counts and weights needed in the stable-sequence argument.
  The labels at any fixed depth are distinct by SameDepthIndependent.
-/
module

public import PPGraph.Shearer.Witness
public import Mathlib.Data.List.GetD

@[expose] public section

set_option autoImplicit false
set_option linter.unusedSectionVars false

open Classical

namespace Shearer

variable {V ι : Type} [DecidableEq V] [DecidableEq ι] {S : VarSpaces V}

/-- Looking beyond the last depth returns the empty layer. -/
theorem treeLayers_getD (T : GrowingTree ι) (d : ℕ) :
    (treeLayers T).getD d ∅ = treeLayer T d := by
  by_cases hd : d < treeDepth T + 1
  · simp [treeLayers, hd]
  · have hdepth : treeDepth T < d := by omega
    rw [treeLayer_eq_empty_of_depth_lt T d hdepth]
    simp [treeLayers, hd]

theorem treeLayers_eq_imp_layer_eq (T U : GrowingTree ι)
    (h : treeLayers T = treeLayers U) (d : ℕ) : treeLayer T d = treeLayer U d := by
  simpa only [treeLayers_getD] using congrArg (fun L : List (Finset ι) => L.getD d ∅) h

theorem treeLayers_eq_imp_depth_eq (T U : GrowingTree ι)
    (h : treeLayers T = treeLayers U) : treeDepth T = treeDepth U := by
  have hl := congrArg List.length h
  simp only [treeLayers, List.length_map, List.length_range] at hl
  omega

theorem lab_injOn_depth (P : MTProcess S ι) (T : GrowingTree ι)
    (hSDI : SameDepthIndependent P T) (d : ℕ) :
    Set.InjOn T.lab (T.dom.filter (fun w => w.length = d)) := by
  intro u hu v hv hlab
  obtain ⟨hu, hdu⟩ := Finset.mem_filter.mp hu
  obtain ⟨hv, hdv⟩ := Finset.mem_filter.mp hv
  by_contra hne
  exact (hSDI u v hu hv (hdu.trans hdv.symm) hne).1 hlab

/-- A sum over tree vertices is a sum over depth-label pairs. -/
theorem sum_dom_eq_sum_layers {M : Type*} [AddCommMonoid M]
    (P : MTProcess S ι) (T : GrowingTree ι) (hSDI : SameDepthIndependent P T)
    (f : ℕ → ι → M) :
    (∑ w ∈ T.dom, f w.length (T.lab w)) =
      ∑ d ∈ Finset.range (treeDepth T + 1), ∑ a ∈ treeLayer T d, f d a := by
  have hb : ∀ w ∈ T.dom, w.length ∈ Finset.range (treeDepth T + 1) := by
    intro w hw
    exact Finset.mem_range.mpr (Nat.lt_succ_of_le (Finset.le_sup (f := List.length) hw))
  rw [← Finset.sum_fiberwise_of_maps_to hb (fun w => f w.length (T.lab w))]
  apply Finset.sum_congr rfl
  intro d _
  rw [treeLayer, Finset.sum_image (lab_injOn_depth P T hSDI d)]
  apply Finset.sum_congr rfl
  intro w hw
  rw [(Finset.mem_filter.mp hw).2]

/-- Products are transported through the same injective depth-label map. -/
theorem prod_dom_eq_prod_layers {M : Type*} [CommMonoid M]
    (P : MTProcess S ι) (T : GrowingTree ι) (hSDI : SameDepthIndependent P T)
    (f : ℕ → ι → M) :
    (∏ w ∈ T.dom, f w.length (T.lab w)) =
      ∏ d ∈ Finset.range (treeDepth T + 1), ∏ a ∈ treeLayer T d, f d a := by
  have hb : ∀ w ∈ T.dom, w.length ∈ Finset.range (treeDepth T + 1) := by
    intro w hw
    exact Finset.mem_range.mpr (Nat.lt_succ_of_le (Finset.le_sup (f := List.length) hw))
  rw [← Finset.prod_fiberwise_of_maps_to hb (fun w => f w.length (T.lab w))]
  apply Finset.prod_congr rfl
  intro d _
  rw [treeLayer, Finset.prod_image (lab_injOn_depth P T hSDI d)]
  apply Finset.prod_congr rfl
  intro w hw
  rw [(Finset.mem_filter.mp hw).2]

theorem prod_map_treeLayers {M : Type*} [CommMonoid M] (T : GrowingTree ι)
    (f : Finset ι → M) :
    ((treeLayers T).map f).prod = ∏ d ∈ Finset.range (treeDepth T + 1), f (treeLayer T d) := by
  simp only [treeLayers, List.map_map, Function.comp_def]
  have h : ∀ n : ℕ, ((List.range n).map (fun d => f (treeLayer T d))).prod =
      ∏ d ∈ Finset.range n, f (treeLayer T d) := by
    intro n
    induction n with
    | zero => simp
    | succ n ih => rw [List.prod_range_succ, Finset.prod_range_succ, ih]
  exact h _

theorem sum_map_treeLayers {M : Type*} [AddCommMonoid M] (T : GrowingTree ι)
    (f : Finset ι → M) :
    ((treeLayers T).map f).sum = ∑ d ∈ Finset.range (treeDepth T + 1), f (treeLayer T d) := by
  simp only [treeLayers, List.map_map, Function.comp_def]
  have h : ∀ n : ℕ, ((List.range n).map (fun d => f (treeLayer T d))).sum =
      ∑ d ∈ Finset.range n, f (treeLayer T d) := by
    intro n
    induction n with
    | zero => simp
    | succ n ih => rw [List.sum_range_succ, Finset.sum_range_succ, ih]
  exact h _

theorem sequenceWeight_treeLayers (P : MTProcess S ι) (T : GrowingTree ι)
    (hSDI : SameDepthIndependent P T) (p : ι → ℝ) :
    sequenceWeight p (treeLayers T) = ∏ w ∈ T.dom, p (T.lab w) := by
  rw [sequenceWeight, prod_map_treeLayers]
  exact (prod_dom_eq_prod_layers P T hSDI (fun _ a => p a)).symm

/-- The number of vertices with one fixed label can be read from the layers. -/
theorem countLabel_eq_layers_sum (P : MTProcess S ι) (T : GrowingTree ι)
    (hSDI : SameDepthIndependent P T) (a : ι) :
    countLabel T a = ((treeLayers T).map (fun J => if a ∈ J then 1 else 0)).sum := by
  have h := sum_dom_eq_sum_layers P T hSDI (fun _ b => if b = a then (1 : ℕ) else 0)
  rw [sum_map_treeLayers]
  simpa [countLabel, Finset.sum_boole] using h

theorem countLabel_eq_of_treeLayers_eq (P : MTProcess S ι) (T U : GrowingTree ι)
    (hT : SameDepthIndependent P T) (hU : SameDepthIndependent P U)
    (h : treeLayers T = treeLayers U) (a : ι) : countLabel T a = countLabel U a := by
  rw [countLabel_eq_layers_sum P T hT a, countLabel_eq_layers_sum P U hU a, h]

end Shearer

#check @Shearer.treeLayers_getD
#check @Shearer.treeLayers_eq_imp_layer_eq
#check @Shearer.treeLayers_eq_imp_depth_eq
#check @Shearer.lab_injOn_depth
#check @Shearer.sum_dom_eq_sum_layers
#check @Shearer.prod_dom_eq_prod_layers
#check @Shearer.prod_map_treeLayers
#check @Shearer.sum_map_treeLayers
#check @Shearer.sequenceWeight_treeLayers
#check @Shearer.countLabel_eq_layers_sum
#check @Shearer.countLabel_eq_of_treeLayers_eq
