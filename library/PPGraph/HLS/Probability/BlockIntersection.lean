/-
  Proposition 3.3 in a finite variable-product space. Events read their
  private/shared blocks; their intersection probability is the ordinary
  probability of both original events in a single assignment.
-/
module

public import PPGraph.HLS.Probability.BlockAssembly
public import PPGraph.HLS.Bounds.CoinSaving

@[expose] public section

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option backward.isDefEq.respectTransparency false

open Classical MeasureTheory

namespace HLS

variable {V : Type} [DecidableEq V] [Fintype V] {S : VarSpaces V}

theorem jointEvent_blocks_eq_preimage (F H Z : Finset V)
    (hFH : Disjoint F H) (hHZ : Disjoint H Z) (hFZ : Disjoint F Z)
    (hUZ : Disjoint (F ∪ Z) H) (A B : Set (MTState S))
    (hdepA : ∀ σ τ : MTState S, (∀ a ∈ F ∪ H, σ a = τ a) → (σ ∈ A ↔ τ ∈ A))
    (hdepB : ∀ σ τ : MTState S, (∀ a ∈ H ∪ Z, σ a = τ a) → (σ ∈ B ↔ τ ∈ B)) :
    jointEvent (joinBlocks F H hFH ⁻¹' A) (joinBlocks H Z hHZ ⁻¹' B) =
      joinThree F H Z hFZ hUZ ⁻¹' (A ∩ B) := by
  ext xyz
  have hagreeA : ∀ a ∈ F ∪ H,
      joinBlocks F H hFH (xyz.1.1, xyz.2) a = joinThree F H Z hFZ hUZ xyz a := by
    intro a ha
    rcases Finset.mem_union.mp ha with ha | ha
    · rw [joinBlocks_left _ _ _ _ a ha, joinThree_left F H Z hFZ hUZ xyz a ha]
    · rw [joinBlocks_right _ _ _ _ a ha, joinThree_middle F H Z hFZ hUZ xyz a ha]
  have hagreeB : ∀ a ∈ H ∪ Z,
      joinBlocks H Z hHZ (xyz.2, xyz.1.2) a = joinThree F H Z hFZ hUZ xyz a := by
    intro a ha
    rcases Finset.mem_union.mp ha with ha | ha
    · rw [joinBlocks_left _ _ _ _ a ha, joinThree_middle F H Z hFZ hUZ xyz a ha]
    · rw [joinBlocks_right _ _ _ _ a ha, joinThree_right F H Z hFZ hUZ xyz a ha]
  exact and_congr (hdepA _ _ hagreeA) (hdepB _ _ hagreeB)

theorem measure_jointEvent_blocks (F H Z : Finset V)
    (hFH : Disjoint F H) (hHZ : Disjoint H Z) (hFZ : Disjoint F Z)
    (hUZ : Disjoint (F ∪ Z) H) (A B : Set (MTState S))
    (hA : MeasurableSet A) (hB : MeasurableSet B)
    (hdepA : ∀ σ τ : MTState S, (∀ a ∈ F ∪ H, σ a = τ a) → (σ ∈ A ↔ τ ∈ A))
    (hdepB : ∀ σ τ : MTState S, (∀ a ∈ H ∪ Z, σ a = τ a) → (σ ∈ B ↔ τ ∈ B)) :
    (((blockMeasure S F).prod (blockMeasure S Z)).prod (blockMeasure S H))
      (jointEvent (joinBlocks F H hFH ⁻¹' A) (joinBlocks H Z hHZ ⁻¹' B)) =
        Measure.pi (fun a => S.measure a) (A ∩ B) := by
  rw [jointEvent_blocks_eq_preimage F H Z hFH hHZ hFZ hUZ A B hdepA hdepB]
  apply measure_joinThree_preimage F H Z hFZ hUZ (A ∩ B) (hA.inter hB)
  intro σ τ h
  have h₁ : ∀ a ∈ F ∪ H, σ a = τ a := by
    intro a ha
    rcases Finset.mem_union.mp ha with ha | ha
    · exact h a (Finset.mem_union_left H (Finset.mem_union_left Z ha))
    · exact h a (Finset.mem_union_right (F ∪ Z) ha)
  have h₂ : ∀ a ∈ H ∪ Z, σ a = τ a := by
    intro a ha
    rcases Finset.mem_union.mp ha with ha | ha
    · exact h a (Finset.mem_union_right (F ∪ Z) ha)
    · exact h a (Finset.mem_union_left H (Finset.mem_union_right F ha))
  exact and_congr (hdepA σ τ h₁) (hdepB σ τ h₂)

/-- The intersection saving for the actual variable-product event probabilities. -/
theorem coin_block_intersection_saving (F H Z : Finset V)
    (hFH : Disjoint F H) (hHZ : Disjoint H Z) (hFZ : Disjoint F Z)
    (hUZ : Disjoint (F ∪ Z) H) (A B : Set (MTState S))
    (hA : MeasurableSet A) (hB : MeasurableSet B)
    (hdepA : ∀ σ τ : MTState S, (∀ a ∈ F ∪ H, σ a = τ a) → (σ ∈ A ↔ τ ∈ A))
    (hdepB : ∀ σ τ : MTState S, (∀ a ∈ H ∪ Z, σ a = τ a) → (σ ∈ B ↔ τ ∈ B))
    (δ : ℝ) (hδ : 0 ≤ δ)
    (hintersection : δ ≤ (Measure.pi (fun a => S.measure a)).real (A ∩ B)) :
    (fairOrientation.prod (((blockMeasure S F).prod (blockMeasure S Z)).prod
      ((blockMeasure S H).prod (blockMeasure S H)))).real
        (coinChoice (forwardEvent (joinBlocks F H hFH ⁻¹' A) (joinBlocks H Z hHZ ⁻¹' B))
          (oneOrderOnly (joinBlocks F H hFH ⁻¹' A) (joinBlocks H Z hHZ ⁻¹' B))) ≤
      (Measure.pi (fun a => S.measure a)).real A *
        (Measure.pi (fun a => S.measure a)).real B - δ ^ 2 / 2 := by
  have hmA := hA.preimage (measurable_joinBlocks F H hFH)
  have hmB := hB.preimage (measurable_joinBlocks H Z hHZ)
  have hInt : δ ≤ (((blockMeasure S F).prod (blockMeasure S Z)).prod
      (blockMeasure S H)).real
        (jointEvent (joinBlocks F H hFH ⁻¹' A) (joinBlocks H Z hHZ ⁻¹' B)) := by
    simpa only [measureReal_def,
      measure_jointEvent_blocks F H Z hFH hHZ hFZ hUZ A B hA hB hdepA hdepB] using hintersection
  have hs := coin_averaged_intersection_saving (blockMeasure S F) (blockMeasure S H)
    (blockMeasure S Z) hmA hmB δ hδ hInt
  simpa only [measureReal_def, measure_joinBlocks_preimage F H hFH A hA hdepA,
    measure_joinBlocks_preimage H Z hHZ B hB hdepB] using hs

end HLS

#check @HLS.jointEvent_blocks_eq_preimage
#check @HLS.measure_jointEvent_blocks
#check @HLS.coin_block_intersection_saving
