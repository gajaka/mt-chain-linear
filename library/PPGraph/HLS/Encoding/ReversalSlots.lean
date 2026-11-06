/-
  The exact effect of a reversible arc on resampling-table indices.
  Shared-variable entries at its endpoints are consecutive and swapped
  by reversal. Private entries and all other nodes are unchanged.
  Source: He--Li--Sun, arXiv:2111.06527, proof of Lemma 3.4.
-/
module

public import PPGraph.HLS.Encoding.TableCheck

@[expose] public section

set_option autoImplicit false
set_option linter.unusedSectionVars false

open Classical

namespace HLS.WitnessDAG

variable {V : Type} [DecidableEq V] {S : VarSpaces V} {ι : Type} [DecidableEq ι]

theorem priorReaders_subset_of_edge (P : MTProcess S ι) (D : HLS.WitnessDAG ι)
    (hD : D.Valid (Shearer.dependencyGraph P.footprint)) (u v : WNode ι)
    (huv : D.Edge u v) (a : V) (hv : a ∈ P.footprint v.1) :
    priorReaders P D u a ⊆ priorReaders P D v a := by
  intro w hw
  obtain ⟨hw, hwu, hwa⟩ := Finset.mem_filter.mp hw
  exact Finset.mem_filter.mpr ⟨hw,
    edge_of_transGen_dependent _ D hD w v ((Relation.TransGen.single hwu).tail huv)
      (dependent_of_shared_variable P w v a hwa hv), hwa⟩

theorem priorReaders_reversible_eq_insert (P : MTProcess S ι) (D : HLS.WitnessDAG ι)
    (hD : D.Valid (Shearer.dependencyGraph P.footprint)) (u v : WNode ι)
    (huv : D.Edge u v) (hrev : Acyclic (reverseArc D.Edge u v))
    (a : V) (hu : a ∈ P.footprint u.1) (hv : a ∈ P.footprint v.1) :
    priorReaders P D v a = insert u (priorReaders P D u a) := by
  have hno := (reversible_iff_no_alternate_path D.Edge u v hD.acyclic huv).mp hrev
  ext w
  constructor
  · intro hw
    obtain ⟨hw, hwv, hwa⟩ := Finset.mem_filter.mp hw
    by_cases hwu : w = u
    · exact Finset.mem_insert.mpr (Or.inl hwu)
    have hdep := dependent_of_shared_variable P w u a hwa hu
    rcases (hD.oriented w hw u (hD.supported u v huv).1 hwu).mpr hdep with h | h
    · exact Finset.mem_insert_of_mem (Finset.mem_filter.mpr ⟨hw, h, hwa⟩)
    · have hwne : w ≠ v := edge_ne _ D hD w v hwv
      have h₁ : eraseArc D.Edge u v u w := ⟨h, by simpa using hwne⟩
      have h₂ : eraseArc D.Edge u v w v := ⟨hwv, by simpa using hwu⟩
      exact False.elim (hno ((Relation.TransGen.single h₁).tail h₂))
  · intro hw
    rcases Finset.mem_insert.mp hw with hwu | hw
    · subst w
      exact Finset.mem_filter.mpr ⟨(hD.supported u v huv).1, huv, hu⟩
    · exact priorReaders_subset_of_edge P D hD u v huv a hv hw

theorem localIndex_reversible_consecutive (P : MTProcess S ι) (D : HLS.WitnessDAG ι)
    (hD : D.Valid (Shearer.dependencyGraph P.footprint)) (u v : WNode ι)
    (huv : D.Edge u v) (hrev : Acyclic (reverseArc D.Edge u v))
    (a : V) (hu : a ∈ P.footprint u.1) (hv : a ∈ P.footprint v.1) :
    localIndex P D v a = localIndex P D u a + 1 := by
  have hunot : u ∉ priorReaders P D u a := by
    intro h
    exact hD.acyclic.irrefl _ u (Finset.mem_filter.mp h).2.1
  rw [localIndex, priorReaders_reversible_eq_insert P D hD u v huv hrev a hu hv,
    Finset.card_insert_of_notMem hunot]
  rfl

theorem priorReaders_reverse_other (P : MTProcess S ι) (D : HLS.WitnessDAG ι)
    (u v w : WNode ι) (hwu : w ≠ u) (hwv : w ≠ v) (a : V) :
    priorReaders P (D.reverse u v) w a = priorReaders P D w a := by
  ext z
  simp only [priorReaders, Finset.mem_filter, reverse_edge_iff, reverseArc, addArc, eraseArc]
  simp [reverse, hwu, hwv]

theorem priorReaders_reverse_source (P : MTProcess S ι) (D : HLS.WitnessDAG ι)
    (hD : D.Valid (Shearer.dependencyGraph P.footprint)) (u v : WNode ι)
    (huv : D.Edge u v) (a : V) :
    priorReaders P (D.reverse u v) u a =
      if a ∈ P.footprint v.1 then insert v (priorReaders P D u a)
      else priorReaders P D u a := by
  have hne := edge_ne _ D hD u v huv
  have hv := (hD.supported u v huv).2
  ext z
  by_cases ha : a ∈ P.footprint v.1
  · simp only [ha, ite_true, Finset.mem_insert, priorReaders, Finset.mem_filter,
      reverse_edge_iff, reverseArc, addArc, eraseArc]
    simp only [reverse]
    constructor
    · rintro ⟨hz, (⟨h, _⟩ | ⟨rfl, _⟩), hza⟩
      · exact Or.inr ⟨hz, h, hza⟩
      · exact Or.inl rfl
    · rintro (rfl | ⟨hz, h, hza⟩)
      · exact ⟨hv, Or.inr ⟨rfl, trivial⟩, ha⟩
      · exact ⟨hz, Or.inl ⟨h, by simp [hne]⟩, hza⟩
  · simp only [ha, ite_false, priorReaders, Finset.mem_filter,
      reverse_edge_iff, reverseArc, addArc, eraseArc]
    simp only [reverse]
    constructor
    · rintro ⟨hz, (⟨h, _⟩ | ⟨rfl, _⟩), hza⟩
      · exact ⟨hz, h, hza⟩
      · exact False.elim (ha hza)
    · rintro ⟨hz, h, hza⟩
      exact ⟨hz, Or.inl ⟨h, by simp [hne]⟩, hza⟩

theorem priorReaders_reverse_target (P : MTProcess S ι) (D : HLS.WitnessDAG ι)
    (hD : D.Valid (Shearer.dependencyGraph P.footprint)) (u v : WNode ι)
    (huv : D.Edge u v) (a : V) :
    priorReaders P (D.reverse u v) v a = (priorReaders P D v a).erase u := by
  have hne := edge_ne _ D hD u v huv
  ext z
  simp only [priorReaders, Finset.mem_filter, Finset.mem_erase,
    reverse_edge_iff, reverseArc, addArc, eraseArc]
  simp only [reverse]
  simp only [Ne.symm hne, and_false, or_false, and_true]
  tauto

theorem localIndex_reverse_source_private (P : MTProcess S ι) (D : HLS.WitnessDAG ι)
    (hD : D.Valid (Shearer.dependencyGraph P.footprint)) (u v : WNode ι)
    (huv : D.Edge u v) (a : V) (ha : a ∉ P.footprint v.1) :
    localIndex P (D.reverse u v) u a = localIndex P D u a := by
  simp [localIndex, priorReaders_reverse_source P D hD u v huv a, ha]

theorem localIndex_reverse_target_private (P : MTProcess S ι) (D : HLS.WitnessDAG ι)
    (hD : D.Valid (Shearer.dependencyGraph P.footprint)) (u v : WNode ι)
    (huv : D.Edge u v) (a : V) (ha : a ∉ P.footprint u.1) :
    localIndex P (D.reverse u v) v a = localIndex P D v a := by
  have hu : u ∉ priorReaders P D v a := fun h => ha (Finset.mem_filter.mp h).2.2
  rw [localIndex, priorReaders_reverse_target P D hD u v huv a,
    Finset.erase_eq_of_notMem hu]
  rfl

theorem localIndex_reverse_source_shared (P : MTProcess S ι) (D : HLS.WitnessDAG ι)
    (hD : D.Valid (Shearer.dependencyGraph P.footprint)) (u v : WNode ι)
    (huv : D.Edge u v) (hrev : Acyclic (reverseArc D.Edge u v))
    (a : V) (hu : a ∈ P.footprint u.1) (hv : a ∈ P.footprint v.1) :
    localIndex P (D.reverse u v) u a = localIndex P D v a := by
  have hvnot : v ∉ priorReaders P D u a := by
    intro h
    exact hD.acyclic.asymm _ u v huv (Finset.mem_filter.mp h).2.1
  rw [localIndex, priorReaders_reverse_source P D hD u v huv a, ite_eq_left hv,
    Finset.card_insert_of_notMem hvnot]
  exact (localIndex_reversible_consecutive P D hD u v huv hrev a hu hv).symm

theorem localIndex_reverse_target_shared (P : MTProcess S ι) (D : HLS.WitnessDAG ι)
    (hD : D.Valid (Shearer.dependencyGraph P.footprint)) (u v : WNode ι)
    (huv : D.Edge u v) (hrev : Acyclic (reverseArc D.Edge u v))
    (a : V) (hu : a ∈ P.footprint u.1) (hv : a ∈ P.footprint v.1) :
    localIndex P (D.reverse u v) v a = localIndex P D u a := by
  rw [localIndex, priorReaders_reverse_target P D hD u v huv a,
    priorReaders_reversible_eq_insert P D hD u v huv hrev a hu hv]
  have hunot : u ∉ priorReaders P D u a := by
    intro h
    exact hD.acyclic.irrefl _ u (Finset.mem_filter.mp h).2.1
  rw [Finset.erase_insert hunot]
  rfl

end HLS.WitnessDAG

#check @HLS.WitnessDAG.priorReaders_subset_of_edge
#check @HLS.WitnessDAG.priorReaders_reversible_eq_insert
#check @HLS.WitnessDAG.localIndex_reversible_consecutive
#check @HLS.WitnessDAG.priorReaders_reverse_other
#check @HLS.WitnessDAG.priorReaders_reverse_source
#check @HLS.WitnessDAG.priorReaders_reverse_target
#check @HLS.WitnessDAG.localIndex_reverse_source_private
#check @HLS.WitnessDAG.localIndex_reverse_target_private
#check @HLS.WitnessDAG.localIndex_reverse_source_shared
#check @HLS.WitnessDAG.localIndex_reverse_target_shared
