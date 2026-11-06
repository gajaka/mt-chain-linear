/- Local dependence of the augmented checks on their disjoint coordinate blocks. -/
module

public import PPGraph.HLS.Probability.AugmentedPair
public import PPGraph.HLS.Probability.AugmentedCoordinates

@[expose] public section

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option backward.isDefEq.respectTransparency false

open Classical MeasureTheory

namespace HLS.WitnessDAG

variable {V : Type} [DecidableEq V] {S : VarSpaces V}
  {ι : Type} [Fintype ι] [DecidableEq ι] [Nonempty ι]

theorem pairBlockRead_eq_of_coordinates (P : MTProcess S ι) (D : HLS.WitnessDAG ι)
    (u v : WNode ι) (ω ω' : LogSpace S)
    (hu : ∀ q ∈ tableCoordinates P D u, ω q = ω' q)
    (hv : ∀ q ∈ tableCoordinates P D v, ω q = ω' q) :
    pairBlockRead P D u v ω = pairBlockRead P D u v ω' := by
  apply Prod.ext
  · apply Prod.ext
    · funext a
      exact hu _ (Finset.mem_image.mpr ⟨a.val, (Finset.mem_sdiff.mp a.property).1, rfl⟩)
    · funext a
      exact hv _ (Finset.mem_image.mpr ⟨a.val, (Finset.mem_sdiff.mp a.property).1, rfl⟩)
  · apply Prod.ext
    · funext a
      exact hu _ (Finset.mem_image.mpr ⟨a.val, (Finset.mem_inter.mp a.property).1, rfl⟩)
    · funext a
      exact hv _ (Finset.mem_image.mpr ⟨a.val, (Finset.mem_inter.mp a.property).2, rfl⟩)

theorem originalTable_event_depends_on_dataCoordinates (P : MTProcess S ι)
    (D : HLS.WitnessDAG ι) (u : WNode ι) (η η' : LogSpace (augmentedSpaces S))
    (h : ∀ q ∈ dataCoordinates P D u, η q = η' q) :
    originalTable η ∈ tableEvent P D u ↔ originalTable η' ∈ tableEvent P D u := by
  apply tableEvent_depends_on_coordinates P D u
  intro q hq
  exact h _ (Finset.mem_image.mpr ⟨q, hq, rfl⟩)

theorem augmentedPairRead_eq_of_coordinates (P : MTProcess S ι)
    (M : DependencyMatching (Shearer.dependencyGraph P.footprint))
    (D : HLS.WitnessDAG ι) (e : WNode ι × WNode ι)
    (η η' : LogSpace (augmentedSpaces S))
    (h : ∀ q ∈ pairCoordinates P M D e, η q = η' q) :
    augmentedPairRead P M D e.1 e.2 η = augmentedPairRead P M D e.1 e.2 η' := by
  apply Prod.ext
  · apply congrArg (relativeCoin M e.1.1)
    exact h _ (Finset.mem_union_right _ (Finset.mem_singleton_self _))
  · apply pairBlockRead_eq_of_coordinates P D e.1 e.2
    · intro q hq
      exact h _ (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_image.mpr ⟨q, hq, rfl⟩)))
    · intro q hq
      exact h _ (Finset.mem_union_left _ (Finset.mem_union_right _ (Finset.mem_image.mpr ⟨q, hq, rfl⟩)))

theorem augmentedPairCheck_depends_on_pairCoordinates (P : MTProcess S ι)
    (M : DependencyMatching (Shearer.dependencyGraph P.footprint))
    (D : HLS.WitnessDAG ι) (e : WNode ι × WNode ι)
    (η η' : LogSpace (augmentedSpaces S))
    (h : ∀ q ∈ pairCoordinates P M D e, η q = η' q) :
    η ∈ augmentedPairCheck P M D e.1 e.2 ↔ η' ∈ augmentedPairCheck P M D e.1 e.2 := by
  change augmentedPairRead P M D e.1 e.2 η ∈
    coinChoice (forwardEvent (sourceBlockBad P e.1.1 e.2.1) (targetBlockBad P e.1.1 e.2.1))
      (oneOrderOnly (sourceBlockBad P e.1.1 e.2.1) (targetBlockBad P e.1.1 e.2.1)) ↔
    augmentedPairRead P M D e.1 e.2 η' ∈
    coinChoice (forwardEvent (sourceBlockBad P e.1.1 e.2.1) (targetBlockBad P e.1.1 e.2.1))
      (oneOrderOnly (sourceBlockBad P e.1.1 e.2.1) (targetBlockBad P e.1.1 e.2.1))
  rw [augmentedPairRead_eq_of_coordinates P M D e η η' h]

end HLS.WitnessDAG

#check @HLS.WitnessDAG.pairBlockRead_eq_of_coordinates
#check @HLS.WitnessDAG.originalTable_event_depends_on_dataCoordinates
#check @HLS.WitnessDAG.augmentedPairRead_eq_of_coordinates
#check @HLS.WitnessDAG.augmentedPairCheck_depends_on_pairCoordinates
