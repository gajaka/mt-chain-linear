/- Disjoint private/shared table queries and their exact four-block law. -/
module

public import PPGraph.HLS.Probability.FootprintBlocks
public import PPGraph.HLS.Encoding.ReversalSlots

@[expose] public section

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option backward.isDefEq.respectTransparency false

open Classical MeasureTheory

namespace HLS

variable {V : Type} [DecidableEq V] {S : VarSpaces V}

theorem four_block_query_injective (F H Z : Finset V)
    (hFH : Disjoint F H) (hHZ : Disjoint H Z) (hFZ : Disjoint F Z)
    (f g : V → ℕ) (hshared : ∀ a ∈ H, f a ≠ g a) :
    Function.Injective (fun k : FourIndex ↥F ↥H ↥Z =>
      (fourSlot (fun a => f a.val) (fun a => f a.val) (fun a => g a.val) (fun a => g a.val) k,
        fourVariable Subtype.val Subtype.val Subtype.val k)) := by
  intro x y h
  have hv := congrArg Prod.snd h
  have hn := congrArg Prod.fst h
  rcases x with (x | x) | (x | x) <;> rcases y with (y | y) | (y | y)
  all_goals simp only [fourVariable, fourSlot] at hv hn
  · exact congrArg (fun a : F => Sum.inl (Sum.inl a)) (Subtype.ext hv)
  · exact False.elim (Finset.disjoint_left.mp hFZ x.property (hv.symm ▸ y.property))
  · exact False.elim (Finset.disjoint_left.mp hFH x.property (hv.symm ▸ y.property))
  · exact False.elim (Finset.disjoint_left.mp hFH x.property (hv.symm ▸ y.property))
  · exact False.elim (Finset.disjoint_left.mp hFZ y.property (hv ▸ x.property))
  · exact congrArg (fun a : Z => Sum.inl (Sum.inr a)) (Subtype.ext hv)
  · exact False.elim (Finset.disjoint_left.mp hHZ y.property (hv ▸ x.property))
  · exact False.elim (Finset.disjoint_left.mp hHZ y.property (hv ▸ x.property))
  · exact False.elim (Finset.disjoint_left.mp hFH y.property (hv ▸ x.property))
  · exact False.elim (Finset.disjoint_left.mp hHZ x.property (hv.symm ▸ y.property))
  · exact congrArg (fun a : H => Sum.inr (Sum.inl a)) (Subtype.ext hv)
  · exact False.elim (hshared x.val x.property (hn.trans (congrArg g hv).symm))
  · exact False.elim (Finset.disjoint_left.mp hFH y.property (hv ▸ x.property))
  · exact False.elim (Finset.disjoint_left.mp hHZ x.property (hv.symm ▸ y.property))
  · exact False.elim (hshared y.val y.property (hn.symm.trans (congrArg g hv)))
  · exact congrArg (fun a : H => Sum.inr (Sum.inr a)) (Subtype.ext hv)

namespace WitnessDAG

variable {ι : Type} [DecidableEq ι]

noncomputable def pairBlockRead (P : MTProcess S ι) (D : HLS.WitnessDAG ι)
    (u v : WNode ι) (ω : LogSpace S) :
    (BlockState S (sourcePrivate P u.1 v.1) × BlockState S (targetPrivate P u.1 v.1)) ×
      (BlockState S (sharedVariables P u.1 v.1) × BlockState S (sharedVariables P u.1 v.1)) :=
  readFour Subtype.val Subtype.val Subtype.val
    (fun a => localIndex P D u a.val) (fun a => localIndex P D u a.val)
    (fun a => localIndex P D v a.val) (fun a => localIndex P D v a.val) ω

theorem pairBlockRead_map (P : MTProcess S ι) (D : HLS.WitnessDAG ι)
    (hD : D.Valid (Shearer.dependencyGraph P.footprint)) (u v : WNode ι) (he : D.Edge u v) :
    (logMeasure S).map (pairBlockRead P D u v) =
      (((blockMeasure S (sourcePrivate P u.1 v.1)).prod
        (blockMeasure S (targetPrivate P u.1 v.1))).prod
        ((blockMeasure S (sharedVariables P u.1 v.1)).prod
          (blockMeasure S (sharedVariables P u.1 v.1)))) := by
  apply map_readFour
  apply four_block_query_injective _ _ _ (source_shared_disjoint P u.1 v.1)
    (shared_target_disjoint P u.1 v.1) (source_target_disjoint P u.1 v.1)
  intro a ha
  obtain ⟨hau, hav⟩ := Finset.mem_inter.mp ha
  exact Nat.ne_of_lt (localIndex_lt_of_edge P D hD u v he a hau hav)

theorem tableEvent_source_iff_block (P : MTProcess S ι) (D : HLS.WitnessDAG ι)
    (u v : WNode ι) (ω : LogSpace S) :
    ω ∈ tableEvent P D u ↔
      joinBlocks (sourcePrivate P u.1 v.1) (sharedVariables P u.1 v.1)
        (source_shared_disjoint P u.1 v.1)
          ((pairBlockRead P D u v ω).1.1, (pairBlockRead P D u v ω).2.1) ∈ P.bad u.1 := by
  apply P.dep u.1
  intro a ha
  rw [source_footprint_eq_blocks P u.1 v.1] at ha
  rcases Finset.mem_union.mp ha with ha | ha
  · rw [joinBlocks_left _ _ _ _ a ha]
    rfl
  · rw [joinBlocks_right _ _ _ _ a ha]
    rfl

theorem tableEvent_target_iff_block (P : MTProcess S ι) (D : HLS.WitnessDAG ι)
    (u v : WNode ι) (ω : LogSpace S) :
    ω ∈ tableEvent P D v ↔
      joinBlocks (sharedVariables P u.1 v.1) (targetPrivate P u.1 v.1)
        (shared_target_disjoint P u.1 v.1)
          ((pairBlockRead P D u v ω).2.2, (pairBlockRead P D u v ω).1.2) ∈ P.bad v.1 := by
  apply P.dep v.1
  intro a ha
  rw [target_footprint_eq_blocks P u.1 v.1] at ha
  rcases Finset.mem_union.mp ha with ha | ha
  · rw [joinBlocks_left _ _ _ _ a ha]
    rfl
  · rw [joinBlocks_right _ _ _ _ a ha]
    rfl

end WitnessDAG
end HLS

#check @HLS.four_block_query_injective
#check @HLS.WitnessDAG.pairBlockRead_map
#check @HLS.WitnessDAG.tableEvent_source_iff_block
#check @HLS.WitnessDAG.tableEvent_target_iff_block
