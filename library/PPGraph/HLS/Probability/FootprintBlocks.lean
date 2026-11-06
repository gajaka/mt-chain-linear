/- Private/shared event blocks and the intersection estimate for MT bad events. -/
module

public import PPGraph.HLS.Probability.BlockIntersection

@[expose] public section

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option backward.isDefEq.respectTransparency false

open Classical MeasureTheory

namespace HLS

variable {V : Type} [DecidableEq V] {S : VarSpaces V} {ι : Type}

noncomputable def sourcePrivate (P : MTProcess S ι) (i j : ι) := P.footprint i \ P.footprint j
noncomputable def sharedVariables (P : MTProcess S ι) (i j : ι) := P.footprint i ∩ P.footprint j
noncomputable def targetPrivate (P : MTProcess S ι) (i j : ι) := P.footprint j \ P.footprint i

theorem source_shared_disjoint (P : MTProcess S ι) (i j : ι) :
    Disjoint (sourcePrivate P i j) (sharedVariables P i j) := by
  apply Finset.disjoint_left.mpr
  intro a hF hH
  exact (Finset.mem_sdiff.mp hF).2 (Finset.mem_inter.mp hH).2

theorem shared_target_disjoint (P : MTProcess S ι) (i j : ι) :
    Disjoint (sharedVariables P i j) (targetPrivate P i j) := by
  apply Finset.disjoint_left.mpr
  intro a hH hZ
  exact (Finset.mem_sdiff.mp hZ).2 (Finset.mem_inter.mp hH).1

theorem source_target_disjoint (P : MTProcess S ι) (i j : ι) :
    Disjoint (sourcePrivate P i j) (targetPrivate P i j) := by
  apply Finset.disjoint_left.mpr
  intro a hF hZ
  exact (Finset.mem_sdiff.mp hF).2 (Finset.mem_sdiff.mp hZ).1

theorem private_union_shared_disjoint (P : MTProcess S ι) (i j : ι) :
    Disjoint (sourcePrivate P i j ∪ targetPrivate P i j) (sharedVariables P i j) :=
  Finset.disjoint_union_left.mpr
    ⟨source_shared_disjoint P i j, (shared_target_disjoint P i j).symm⟩

theorem source_footprint_eq_blocks (P : MTProcess S ι) (i j : ι) :
    P.footprint i = sourcePrivate P i j ∪ sharedVariables P i j := by
  ext a
  simp only [sourcePrivate, sharedVariables, Finset.mem_union, Finset.mem_sdiff,
    Finset.mem_inter]
  tauto

theorem target_footprint_eq_blocks (P : MTProcess S ι) (i j : ι) :
    P.footprint j = sharedVariables P i j ∪ targetPrivate P i j := by
  ext a
  simp only [targetPrivate, sharedVariables, Finset.mem_union, Finset.mem_sdiff,
    Finset.mem_inter]
  tauto

theorem source_bad_depends_blocks (P : MTProcess S ι) (i j : ι) (σ τ : MTState S)
    (h : ∀ a ∈ sourcePrivate P i j ∪ sharedVariables P i j, σ a = τ a) :
    σ ∈ P.bad i ↔ τ ∈ P.bad i :=
  P.dep i σ τ (fun a ha => h a ((source_footprint_eq_blocks P i j) ▸ ha))

theorem target_bad_depends_blocks (P : MTProcess S ι) (i j : ι) (σ τ : MTState S)
    (h : ∀ a ∈ sharedVariables P i j ∪ targetPrivate P i j, σ a = τ a) :
    σ ∈ P.bad j ↔ τ ∈ P.bad j :=
  P.dep j σ τ (fun a ha => h a ((target_footprint_eq_blocks P i j) ▸ ha))

/-- The product-space saving is instantiated with the process's own bad events. -/
theorem coin_process_block_saving [Fintype V] (P : MTProcess S ι) (i j : ι)
    (hi : MeasurableSet (P.bad i)) (hj : MeasurableSet (P.bad j))
    (δ : ℝ) (hδ : 0 ≤ δ)
    (hInt : δ ≤ (Measure.pi (fun a => S.measure a)).real (P.bad i ∩ P.bad j)) :
    (fairOrientation.prod
      (((blockMeasure S (sourcePrivate P i j)).prod (blockMeasure S (targetPrivate P i j))).prod
        ((blockMeasure S (sharedVariables P i j)).prod
          (blockMeasure S (sharedVariables P i j))))).real
      (coinChoice
        (forwardEvent
          (joinBlocks (sourcePrivate P i j) (sharedVariables P i j) (source_shared_disjoint P i j) ⁻¹'
            P.bad i)
          (joinBlocks (sharedVariables P i j) (targetPrivate P i j) (shared_target_disjoint P i j) ⁻¹'
            P.bad j))
        (oneOrderOnly
          (joinBlocks (sourcePrivate P i j) (sharedVariables P i j) (source_shared_disjoint P i j) ⁻¹'
            P.bad i)
          (joinBlocks (sharedVariables P i j) (targetPrivate P i j) (shared_target_disjoint P i j) ⁻¹'
            P.bad j))) ≤
      (Measure.pi (fun a => S.measure a)).real (P.bad i) *
        (Measure.pi (fun a => S.measure a)).real (P.bad j) - δ ^ 2 / 2 :=
  coin_block_intersection_saving _ _ _ (source_shared_disjoint P i j)
    (shared_target_disjoint P i j) (source_target_disjoint P i j)
    (private_union_shared_disjoint P i j) _ _ hi hj
    (source_bad_depends_blocks P i j) (target_bad_depends_blocks P i j) δ hδ hInt

end HLS

#check @HLS.source_shared_disjoint
#check @HLS.shared_target_disjoint
#check @HLS.source_target_disjoint
#check @HLS.private_union_shared_disjoint
#check @HLS.source_footprint_eq_blocks
#check @HLS.target_footprint_eq_blocks
#check @HLS.source_bad_depends_blocks
#check @HLS.target_bad_depends_blocks
#check @HLS.coin_process_block_saving
