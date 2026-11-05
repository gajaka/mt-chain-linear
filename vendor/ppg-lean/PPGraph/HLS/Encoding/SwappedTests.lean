/-
  Reversible endpoint tests are exactly tests on states with their shared
  variables exchanged. Certificate locality justifies comparing only
  variables in the endpoint's own footprint.
-/
module

public import PPGraph.HLS.Encoding.PrefixCheck

@[expose] public section

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option backward.isDefEq.respectTransparency false

open Classical

namespace HLS.WitnessDAG

variable {V : Type} [DecidableEq V] {S : VarSpaces V} {ι : Type} [DecidableEq ι]

noncomputable def swapShared (P : MTProcess S ι) (u v : WNode ι)
    (σ τ : MTState S) : MTState S := fun a =>
  if a ∈ P.footprint u.1 ∩ P.footprint v.1 then τ a else σ a

theorem reverse_source_test_eq_swap (P : MTProcess S ι) (D : HLS.WitnessDAG ι)
    (hD : D.Valid (Shearer.dependencyGraph P.footprint)) (u v : WNode ι)
    (huv : D.Edge u v) (hrev : Acyclic (reverseArc D.Edge u v)) (ω : LogSpace S) :
    ω ∈ tableEvent P (D.reverse u v) u ↔
      swapShared P u v (tableState P D ω u) (tableState P D ω v) ∈ P.bad u.1 := by
  apply P.dep u.1
  intro a ha
  by_cases hav : a ∈ P.footprint v.1
  · simp only [swapShared, Finset.mem_inter, ha, hav, and_self, ite_true,
      tableState, readAt]
    rw [localIndex_reverse_source_shared P D hD u v huv hrev a ha hav]
  · simp only [swapShared, Finset.mem_inter, ha, hav, and_false, ite_false,
      tableState, readAt]
    rw [localIndex_reverse_source_private P D hD u v huv a hav]

theorem reverse_target_test_eq_swap (P : MTProcess S ι) (D : HLS.WitnessDAG ι)
    (hD : D.Valid (Shearer.dependencyGraph P.footprint)) (u v : WNode ι)
    (huv : D.Edge u v) (hrev : Acyclic (reverseArc D.Edge u v)) (ω : LogSpace S) :
    ω ∈ tableEvent P (D.reverse u v) v ↔
      swapShared P u v (tableState P D ω v) (tableState P D ω u) ∈ P.bad v.1 := by
  apply P.dep v.1
  intro a ha
  by_cases hau : a ∈ P.footprint u.1
  · simp only [swapShared, Finset.mem_inter, ha, hau, and_self, ite_true,
      tableState, readAt]
    rw [localIndex_reverse_target_shared P D hD u v huv hrev a hau ha]
  · simp only [swapShared, Finset.mem_inter, ha, hau, false_and, ite_false,
      tableState, readAt]
    rw [localIndex_reverse_target_private P D hD u v huv a hau]

theorem flipped_prefix_failure_forces_swapped_failure (P : MTProcess S ι)
    (D : HLS.WitnessDAG ι) (hD : D.Valid (Shearer.dependencyGraph P.footprint))
    (r u v : WNode ι) (huv : D.Edge u v) (hrev : Acyclic (reverseArc D.Edge u v))
    (ω : LogSpace S) (hω : ω ∈ tableCheck P D)
    (hfail : ω ∉ tableCheck P ((D.reverse u v).ancestorPrefix r)) :
    swapShared P u v (tableState P D ω u) (tableState P D ω v) ∉ P.bad u.1 ∨
      swapShared P u v (tableState P D ω v) (tableState P D ω u) ∉ P.bad v.1 := by
  have h := flipped_prefix_failure_localizes P D r u v ω hω hfail
  simpa only [reverse_source_test_eq_swap P D hD u v huv hrev ω,
    reverse_target_test_eq_swap P D hD u v huv hrev ω] using h

end HLS.WitnessDAG

#check @HLS.WitnessDAG.reverse_source_test_eq_swap
#check @HLS.WitnessDAG.reverse_target_test_eq_swap
#check @HLS.WitnessDAG.flipped_prefix_failure_forces_swapped_failure
