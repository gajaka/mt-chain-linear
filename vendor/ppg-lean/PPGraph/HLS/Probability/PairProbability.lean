/-
  The two-endpoint probability bound on the actual MT resampling table.
  The fair coin belongs only to the analysis. Reversing a reversible arc
  exchanges the two shared samples and preserves the private samples.
-/
module

public import PPGraph.HLS.Probability.BlockQueries
public import PPGraph.HLS.Encoding.SwappedTests

@[expose] public section

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option backward.isDefEq.respectTransparency false

open Classical MeasureTheory

namespace HLS.WitnessDAG

variable {V : Type} [DecidableEq V] {S : VarSpaces V} {ι : Type} [DecidableEq ι]

noncomputable def sourceBlockBad (P : MTProcess S ι) (i j : ι) :=
  joinBlocks (sourcePrivate P i j) (sharedVariables P i j) (source_shared_disjoint P i j) ⁻¹' P.bad i

noncomputable def targetBlockBad (P : MTProcess S ι) (i j : ι) :=
  joinBlocks (sharedVariables P i j) (targetPrivate P i j) (shared_target_disjoint P i j) ⁻¹' P.bad j

theorem measurable_pairBlockRead (P : MTProcess S ι) (D : HLS.WitnessDAG ι) (u v : WNode ι) :
    Measurable (pairBlockRead P D u v) := measurable_readFour _ _ _ _ _ _ _

theorem tableEvent_reverse_source_iff_block (P : MTProcess S ι) (D : HLS.WitnessDAG ι)
    (hD : D.Valid (Shearer.dependencyGraph P.footprint)) (u v : WNode ι)
    (he : D.Edge u v) (hrev : Acyclic (reverseArc D.Edge u v)) (ω : LogSpace S) :
    ω ∈ tableEvent P (D.reverse u v) u ↔
      ((pairBlockRead P D u v ω).1.1, (pairBlockRead P D u v ω).2.2) ∈
        sourceBlockBad P u.1 v.1 := by
  apply P.dep u.1
  intro a ha
  rw [source_footprint_eq_blocks P u.1 v.1] at ha
  rcases Finset.mem_union.mp ha with ha | ha
  · rw [joinBlocks_left _ _ _ _ a ha]
    change atIdx ω a (localIndex P (D.reverse u v) u a) = atIdx ω a (localIndex P D u a)
    rw [localIndex_reverse_source_private P D hD u v he a (Finset.mem_sdiff.mp ha).2]
  · rw [joinBlocks_right _ _ _ _ a ha]
    change atIdx ω a (localIndex P (D.reverse u v) u a) = atIdx ω a (localIndex P D v a)
    obtain ⟨hau, hav⟩ := Finset.mem_inter.mp ha
    rw [localIndex_reverse_source_shared P D hD u v he hrev a hau hav]

theorem tableEvent_reverse_target_iff_block (P : MTProcess S ι) (D : HLS.WitnessDAG ι)
    (hD : D.Valid (Shearer.dependencyGraph P.footprint)) (u v : WNode ι)
    (he : D.Edge u v) (hrev : Acyclic (reverseArc D.Edge u v)) (ω : LogSpace S) :
    ω ∈ tableEvent P (D.reverse u v) v ↔
      ((pairBlockRead P D u v ω).2.1, (pairBlockRead P D u v ω).1.2) ∈
        targetBlockBad P u.1 v.1 := by
  apply P.dep v.1
  intro a ha
  rw [target_footprint_eq_blocks P u.1 v.1] at ha
  rcases Finset.mem_union.mp ha with ha | ha
  · rw [joinBlocks_left _ _ _ _ a ha]
    change atIdx ω a (localIndex P (D.reverse u v) v a) = atIdx ω a (localIndex P D u a)
    obtain ⟨hau, hav⟩ := Finset.mem_inter.mp ha
    rw [localIndex_reverse_target_shared P D hD u v he hrev a hau hav]
  · rw [joinBlocks_right _ _ _ _ a ha]
    change atIdx ω a (localIndex P (D.reverse u v) v a) = atIdx ω a (localIndex P D v a)
    rw [localIndex_reverse_target_private P D hD u v he a (Finset.mem_sdiff.mp ha).2]

noncomputable def pairCoinCheck (P : MTProcess S ι) (D : HLS.WitnessDAG ι) (u v : WNode ι) :
    Set (OrientationCoin × LogSpace S) :=
  coinChoice (pairBlockRead P D u v ⁻¹' forwardEvent (sourceBlockBad P u.1 v.1) (targetBlockBad P u.1 v.1))
    (pairBlockRead P D u v ⁻¹' oneOrderOnly (sourceBlockBad P u.1 v.1) (targetBlockBad P u.1 v.1))

theorem pairCoinCheck_of_tests (P : MTProcess S ι) (D : HLS.WitnessDAG ι)
    (hD : D.Valid (Shearer.dependencyGraph P.footprint)) (u v : WNode ι)
    (he : D.Edge u v) (hrev : Acyclic (reverseArc D.Edge u v)) (ω : LogSpace S)
    (c : OrientationCoin) (hu : ω ∈ tableEvent P D u) (hv : ω ∈ tableEvent P D v)
    (hflip : c = .flip → ω ∉ tableEvent P (D.reverse u v) u ∨
      ω ∉ tableEvent P (D.reverse u v) v) : (c, ω) ∈ pairCoinCheck P D u v := by
  have hu' := (tableEvent_source_iff_block P D u v ω).mp hu
  have hv' := (tableEvent_target_iff_block P D u v ω).mp hv
  cases c with
  | keep =>
    exact Or.inl ⟨Set.mem_singleton _, ⟨hu', hv'⟩⟩
  | flip =>
    have hf := hflip rfl
    have hf' : ((pairBlockRead P D u v ω).1.1, (pairBlockRead P D u v ω).2.2) ∉
        sourceBlockBad P u.1 v.1 ∨
      ((pairBlockRead P D u v ω).2.1, (pairBlockRead P D u v ω).1.2) ∉ targetBlockBad P u.1 v.1 :=
      hf.imp ((tableEvent_reverse_source_iff_block P D hD u v he hrev ω).not.mp)
        ((tableEvent_reverse_target_iff_block P D hD u v he hrev ω).not.mp)
    exact Or.inr ⟨Set.mem_singleton _, hu', hv', hf'⟩

/-- HLS Lemma 3.4's pair saving, on the actual table and an independent fair coin. -/
theorem measureReal_pairCoinCheck_le [Fintype V] (P : MTProcess S ι) (D : HLS.WitnessDAG ι)
    (hD : D.Valid (Shearer.dependencyGraph P.footprint)) (u v : WNode ι) (he : D.Edge u v)
    (hu : MeasurableSet (P.bad u.1)) (hv : MeasurableSet (P.bad v.1))
    (δ : ℝ) (hδ : 0 ≤ δ)
    (hInt : δ ≤ (Measure.pi (fun a => S.measure a)).real (P.bad u.1 ∩ P.bad v.1)) :
    (fairOrientation.prod (logMeasure S)).real (pairCoinCheck P D u v) ≤
      (Measure.pi (fun a => S.measure a)).real (P.bad u.1) *
        (Measure.pi (fun a => S.measure a)).real (P.bad v.1) - δ ^ 2 / 2 := by
  let A := sourceBlockBad P u.1 v.1
  let B := targetBlockBad P u.1 v.1
  let μ₄ := ((blockMeasure S (sourcePrivate P u.1 v.1)).prod
    (blockMeasure S (targetPrivate P u.1 v.1))).prod
    ((blockMeasure S (sharedVariables P u.1 v.1)).prod (blockMeasure S (sharedVariables P u.1 v.1)))
  have hA : MeasurableSet A := hu.preimage (measurable_joinBlocks _ _ _)
  have hB : MeasurableSet B := hv.preimage (measurable_joinBlocks _ _ _)
  have hF := measurableSet_forwardEvent hA hB
  have hO := measurableSet_oneOrderOnly hA hB
  have hread := measurable_pairBlockRead P D u v
  have hmap := pairBlockRead_map P D hD u v he
  have hforward : (logMeasure S).real (pairBlockRead P D u v ⁻¹' forwardEvent A B) =
      μ₄.real (forwardEvent A B) := by
    exact congrArg ENNReal.toReal
      ((Measure.map_apply hread hF).symm.trans (congrArg (fun μ => μ (forwardEvent A B)) hmap))
  have hopposite : (logMeasure S).real (pairBlockRead P D u v ⁻¹' oneOrderOnly A B) =
      μ₄.real (oneOrderOnly A B) := by
    exact congrArg ENNReal.toReal
      ((Measure.map_apply hread hO).symm.trans (congrArg (fun μ => μ (oneOrderOnly A B)) hmap))
  have hs := coin_process_block_saving P u.1 v.1 hu hv δ hδ hInt
  change (fairOrientation.prod (logMeasure S)).real
    (coinChoice (pairBlockRead P D u v ⁻¹' forwardEvent A B)
      (pairBlockRead P D u v ⁻¹' oneOrderOnly A B)) ≤ _
  rw [measureReal_coinChoice _ (hF.preimage hread) (hO.preimage hread), hforward, hopposite]
  have hs' : (fairOrientation.prod μ₄).real (coinChoice (forwardEvent A B) (oneOrderOnly A B)) ≤ _ := hs
  rw [measureReal_coinChoice μ₄ hF hO] at hs'
  exact hs'

end HLS.WitnessDAG

#check @HLS.WitnessDAG.measurable_pairBlockRead
#check @HLS.WitnessDAG.tableEvent_reverse_source_iff_block
#check @HLS.WitnessDAG.tableEvent_reverse_target_iff_block
#check @HLS.WitnessDAG.pairCoinCheck_of_tests
#check @HLS.WitnessDAG.measureReal_pairCoinCheck_le
