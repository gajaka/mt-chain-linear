/- Actual augmented-table pair checks: measurability, law, and saving. -/
module

public import PPGraph.HLS.Probability.CoinQueryLaw
public import PPGraph.HLS.Encoding.RelativeCoins
public import PPGraph.HLS.Probability.PairProbability
public import PPGraph.HLS.Bounds.AugmentedExistence

@[expose] public section

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option backward.isDefEq.respectTransparency false

open Classical MeasureTheory

namespace HLS.WitnessDAG

variable {V : Type} [DecidableEq V] {S : VarSpaces V}
  {ι : Type} [Fintype ι] [DecidableEq ι] [Nonempty ι]

noncomputable def augmentedPairRead (P : MTProcess S ι)
    (M : DependencyMatching (Shearer.dependencyGraph P.footprint))
    (D : HLS.WitnessDAG ι) (u v : WNode ι) (η : LogSpace (augmentedSpaces S)) :=
  (relativeCoin M u.1 (auxiliaryCoins η (M.pair u.1, D.cliqueRank (M.pair u.1) u)),
    pairBlockRead P D u v (originalTable η))

noncomputable def augmentedPairCheck (P : MTProcess S ι)
    (M : DependencyMatching (Shearer.dependencyGraph P.footprint))
    (D : HLS.WitnessDAG ι) (u v : WNode ι) : Set (LogSpace (augmentedSpaces (ι := ι) S)) :=
  augmentedPairRead P M D u v ⁻¹'
    coinChoice (forwardEvent (sourceBlockBad P u.1 v.1) (targetBlockBad P u.1 v.1))
      (oneOrderOnly (sourceBlockBad P u.1 v.1) (targetBlockBad P u.1 v.1))

theorem measurable_augmentedPairRead (P : MTProcess S ι)
    (M : DependencyMatching (Shearer.dependencyGraph P.footprint))
    (D : HLS.WitnessDAG ι) (u v : WNode ι) : Measurable (augmentedPairRead P M D u v) := by
  exact ((measurable_relativeCoin M u.1).comp (measurable_pi_apply _)).prodMk
    ((measurable_pairBlockRead P D u v).comp (measurable_originalTable S))

theorem map_augmentedPairRead (P : MTProcess S ι)
    (M : DependencyMatching (Shearer.dependencyGraph P.footprint))
    (D : HLS.WitnessDAG ι) (hD : D.Valid (Shearer.dependencyGraph P.footprint))
    (u v : WNode ι) (he : D.Edge u v) :
    (logMeasure (augmentedSpaces S)).map (augmentedPairRead P M D u v) =
      fairOrientation.prod (((blockMeasure S (sourcePrivate P u.1 v.1)).prod
        (blockMeasure S (targetPrivate P u.1 v.1))).prod
        ((blockMeasure S (sharedVariables P u.1 v.1)).prod (blockMeasure S (sharedVariables P u.1 v.1)))) := by
  have hinj := four_block_query_injective (sourcePrivate P u.1 v.1) (sharedVariables P u.1 v.1)
    (targetPrivate P u.1 v.1) (source_shared_disjoint P u.1 v.1)
    (shared_target_disjoint P u.1 v.1) (source_target_disjoint P u.1 v.1)
    (localIndex P D u) (localIndex P D v)
    (fun a ha => Nat.ne_of_lt (localIndex_lt_of_edge P D hD u v he a
      (Finset.mem_inter.mp ha).1 (Finset.mem_inter.mp ha).2))
  have hraw := map_coinAndFourRead (S := S) (M.pair u.1) (D.cliqueRank (M.pair u.1) u)
    (Subtype.val : ↥(sourcePrivate P u.1 v.1) → V)
    (Subtype.val : ↥(sharedVariables P u.1 v.1) → V)
    (Subtype.val : ↥(targetPrivate P u.1 v.1) → V)
    (fun a => localIndex P D u a.val) (fun a => localIndex P D u a.val)
    (fun a => localIndex P D v a.val) (fun a => localIndex P D v a.val) hinj
  let μ₄ := ((blockMeasure S (sourcePrivate P u.1 v.1)).prod
    (blockMeasure S (targetPrivate P u.1 v.1))).prod
    ((blockMeasure S (sharedVariables P u.1 v.1)).prod (blockMeasure S (sharedVariables P u.1 v.1)))
  have hcoin : MeasurePreserving (relativeCoin M u.1) fairOrientation fairOrientation :=
    ⟨measurable_relativeCoin M u.1, map_relativeCoin M u.1⟩
  have hprod := hcoin.prod (MeasurePreserving.id μ₄)
  have hmeasRaw : Measurable (fun η : LogSpace (augmentedSpaces (ι := ι) S) =>
      (auxiliaryCoins η (M.pair u.1, D.cliqueRank (M.pair u.1) u), pairBlockRead P D u v (originalTable η))) :=
    (measurable_pi_apply _).prodMk
    ((measurable_pairBlockRead P D u v).comp (measurable_originalTable S (ι := ι)))
  have hread : MeasurePreserving
      (fun η : LogSpace (augmentedSpaces (ι := ι) S) =>
        (auxiliaryCoins η (M.pair u.1, D.cliqueRank (M.pair u.1) u), pairBlockRead P D u v (originalTable η)))
      (logMeasure (augmentedSpaces S)) (fairOrientation.prod μ₄) := ⟨hmeasRaw, hraw⟩
  exact (hprod.comp hread).map_eq

theorem measurableSet_augmentedPairCheck (P : MTProcess S ι)
    (M : DependencyMatching (Shearer.dependencyGraph P.footprint))
    (D : HLS.WitnessDAG ι) (u v : WNode ι) (hbad : ∀ i, MeasurableSet (P.bad i)) :
    MeasurableSet (augmentedPairCheck P M D u v) := by
  have hA : MeasurableSet (sourceBlockBad P u.1 v.1) :=
    (hbad u.1).preimage (measurable_joinBlocks _ _ _)
  have hB : MeasurableSet (targetBlockBad P u.1 v.1) :=
    (hbad v.1).preimage (measurable_joinBlocks _ _ _)
  exact (measurableSet_coinChoice (measurableSet_forwardEvent hA hB)
    (measurableSet_oneOrderOnly hA hB)).preimage (measurable_augmentedPairRead P M D u v)

theorem measureReal_augmentedPairCheck_le [Fintype V] (P : MTProcess S ι)
    (M : DependencyMatching (Shearer.dependencyGraph P.footprint))
    (D : HLS.WitnessDAG ι) (hD : D.Valid (Shearer.dependencyGraph P.footprint))
    (u v : WNode ι) (he : D.Edge u v) (hbad : ∀ i, MeasurableSet (P.bad i))
    (δ : ℝ) (hδ : 0 ≤ δ)
    (hInt : δ ≤ (Measure.pi (fun a => S.measure a)).real (P.bad u.1 ∩ P.bad v.1)) :
    (logMeasure (augmentedSpaces S)).real (augmentedPairCheck P M D u v) ≤
      (Measure.pi (fun a => S.measure a)).real (P.bad u.1) *
        (Measure.pi (fun a => S.measure a)).real (P.bad v.1) - δ ^ 2 / 2 := by
  have hA : MeasurableSet (sourceBlockBad P u.1 v.1) :=
    (hbad u.1).preimage (measurable_joinBlocks _ _ _)
  have hB : MeasurableSet (targetBlockBad P u.1 v.1) :=
    (hbad v.1).preimage (measurable_joinBlocks _ _ _)
  have hmeas := measurableSet_coinChoice (measurableSet_forwardEvent hA hB)
    (measurableSet_oneOrderOnly hA hB)
  have heq := (Measure.map_apply (μ := logMeasure (augmentedSpaces S))
    (measurable_augmentedPairRead P M D u v) hmeas).symm.trans
    (congrArg (fun μ => μ (coinChoice
      (forwardEvent (sourceBlockBad P u.1 v.1) (targetBlockBad P u.1 v.1))
      (oneOrderOnly (sourceBlockBad P u.1 v.1) (targetBlockBad P u.1 v.1))))
      (map_augmentedPairRead P M D hD u v he))
  change (logMeasure (augmentedSpaces S)).real ((augmentedPairRead P M D u v) ⁻¹' _) ≤ _
  rw [measureReal_def, heq]
  exact coin_process_block_saving P u.1 v.1 (hbad _) (hbad _) δ hδ hInt

theorem augmentedCheck_implies_pairCheck (P : MTProcess S ι)
    (M : DependencyMatching (Shearer.dependencyGraph P.footprint))
    (D : HLS.WitnessDAG ι) (hD : D.Valid (Shearer.dependencyGraph P.footprint))
    (r u v : WNode ι) (η : LogSpace (augmentedSpaces S))
    (haug : AugmentedCheck P M (fun q => coinLabel M q.1 (auxiliaryCoins η q)) r D (originalTable η))
    (he : D.Edge u v) (hr : Acyclic (reverseArc D.Edge u v))
    (hm : M.mate u.1 = v.1) (hl : u.1 ≠ v.1) : η ∈ augmentedPairCheck P M D u v := by
  have hmate : M.mate u.1 ≠ u.1 := by intro h; exact hl (h.symm.trans hm)
  have htests := pairCoinCheck_of_tests P D hD u v he hr (originalTable η)
    (relativeCoin M u.1 (auxiliaryCoins η (M.pair u.1, D.cliqueRank (M.pair u.1) u)))
    (Set.mem_iInter₂.mp haug.1 u (hD.supported _ _ he).1)
    (Set.mem_iInter₂.mp haug.1 v (hD.supported _ _ he).2) (by
      intro hc
      have hlabel := (coinLabel_target_iff_relative_flip M u.1 hmate _).mpr hc
      rw [hm] at hlabel
      exact flipped_prefix_failure_localizes P D r u v (originalTable η) haug.1
        (haug.2 u v he hr hm hl hlabel))
  exact htests

end HLS.WitnessDAG

#check @HLS.WitnessDAG.measurable_augmentedPairRead
#check @HLS.WitnessDAG.map_augmentedPairRead
#check @HLS.WitnessDAG.measurableSet_augmentedPairCheck
#check @HLS.WitnessDAG.measureReal_augmentedPairCheck_le
#check @HLS.WitnessDAG.augmentedCheck_implies_pairCheck
