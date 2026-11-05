/-
  Prefixes preserve table indices of retained nodes. Reversal changes
  only the two endpoint tests, so passing both swapped tests and all
  original tests makes the root prefix pass as well. This justifies
  the local obstruction used by the orientation-coin argument.
-/
module

public import PPGraph.HLS.Encoding.ReversalSlots

@[expose] public section

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option backward.isDefEq.respectTransparency false

open Classical

namespace HLS.WitnessDAG

variable {V : Type} [DecidableEq V] {S : VarSpaces V} {ι : Type} [DecidableEq ι]

theorem priorReaders_prefix_eq (P : MTProcess S ι) (D : HLS.WitnessDAG ι)
    (r u : WNode ι) (hur : D.Reach u r) (a : V) :
    priorReaders P (D.ancestorPrefix r) u a = priorReaders P D u a := by
  ext w
  simp only [priorReaders, Finset.mem_filter, prefix_node_iff, prefix_edge_iff]
  constructor
  · rintro ⟨⟨hw, _⟩, ⟨hwu, _⟩, hwa⟩
    exact ⟨hw, hwu, hwa⟩
  · rintro ⟨hw, hwu, hwa⟩
    exact ⟨⟨hw, hur.head hwu⟩, ⟨hwu, hur⟩, hwa⟩

theorem localIndex_prefix_eq (P : MTProcess S ι) (D : HLS.WitnessDAG ι)
    (r u : WNode ι) (hur : D.Reach u r) (a : V) :
    localIndex P (D.ancestorPrefix r) u a = localIndex P D u a := by
  rw [localIndex, priorReaders_prefix_eq P D r u hur a]
  rfl

theorem tableState_prefix_eq (P : MTProcess S ι) (D : HLS.WitnessDAG ι)
    (r u : WNode ι) (hur : D.Reach u r) (ω : LogSpace S) :
    tableState P (D.ancestorPrefix r) ω u = tableState P D ω u := by
  funext a
  change atIdx ω a (localIndex P (D.ancestorPrefix r) u a) = atIdx ω a (localIndex P D u a)
  rw [localIndex_prefix_eq P D r u hur a]

theorem tableCheck_subset_prefix (P : MTProcess S ι) (D : HLS.WitnessDAG ι)
    (r : WNode ι) : tableCheck P D ⊆ tableCheck P (D.ancestorPrefix r) := by
  intro ω hω
  simp only [tableCheck, Set.mem_iInter, tableEvent, Set.mem_ofPred_eq] at hω ⊢
  intro u hu
  obtain ⟨hu, hur⟩ := (prefix_node_iff D r u).mp hu
  rw [tableState_prefix_eq P D r u hur ω]
  exact hω u hu

theorem tableState_reverse_other (P : MTProcess S ι) (D : HLS.WitnessDAG ι)
    (u v w : WNode ι) (hwu : w ≠ u) (hwv : w ≠ v) (ω : LogSpace S) :
    tableState P (D.reverse u v) ω w = tableState P D ω w := by
  funext a
  change atIdx ω a (localIndex P (D.reverse u v) w a) = atIdx ω a (localIndex P D w a)
  rw [localIndex, priorReaders_reverse_other P D u v w hwu hwv a]
  rfl

theorem reverse_tableCheck_of_endpoint_tests (P : MTProcess S ι) (D : HLS.WitnessDAG ι)
    (u v : WNode ι) (ω : LogSpace S) (hω : ω ∈ tableCheck P D)
    (hu : ω ∈ tableEvent P (D.reverse u v) u)
    (hv : ω ∈ tableEvent P (D.reverse u v) v) :
    ω ∈ tableCheck P (D.reverse u v) := by
  simp only [tableCheck, Set.mem_iInter] at hω ⊢
  intro w hw
  by_cases hwu : w = u
  · simpa only [hwu] using hu
  by_cases hwv : w = v
  · simpa only [hwv] using hv
  change tableState P (D.reverse u v) ω w ∈ P.bad w.1
  rw [tableState_reverse_other P D u v w hwu hwv ω]
  exact hω w hw

theorem flipped_prefix_passes_of_endpoint_tests (P : MTProcess S ι)
    (D : HLS.WitnessDAG ι) (r u v : WNode ι) (ω : LogSpace S)
    (hω : ω ∈ tableCheck P D) (hu : ω ∈ tableEvent P (D.reverse u v) u)
    (hv : ω ∈ tableEvent P (D.reverse u v) v) :
    ω ∈ tableCheck P ((D.reverse u v).ancestorPrefix r) :=
  tableCheck_subset_prefix P (D.reverse u v) r
    (reverse_tableCheck_of_endpoint_tests P D u v ω hω hu hv)

/-- Failure of the flipped root prefix forces one of the two swapped
endpoint tests to fail whenever all original tests pass. -/
theorem flipped_prefix_failure_localizes (P : MTProcess S ι)
    (D : HLS.WitnessDAG ι) (r u v : WNode ι) (ω : LogSpace S)
    (hω : ω ∈ tableCheck P D)
    (hfail : ω ∉ tableCheck P ((D.reverse u v).ancestorPrefix r)) :
    ω ∉ tableEvent P (D.reverse u v) u ∨ ω ∉ tableEvent P (D.reverse u v) v := by
  by_contra hn
  push Not at hn
  exact hfail (flipped_prefix_passes_of_endpoint_tests P D r u v ω hω hn.1 hn.2)

end HLS.WitnessDAG

#check @HLS.WitnessDAG.priorReaders_prefix_eq
#check @HLS.WitnessDAG.localIndex_prefix_eq
#check @HLS.WitnessDAG.tableState_prefix_eq
#check @HLS.WitnessDAG.tableCheck_subset_prefix
#check @HLS.WitnessDAG.tableState_reverse_other
#check @HLS.WitnessDAG.reverse_tableCheck_of_endpoint_tests
#check @HLS.WitnessDAG.flipped_prefix_passes_of_endpoint_tests
#check @HLS.WitnessDAG.flipped_prefix_failure_localizes
