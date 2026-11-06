/- Product laws for assembling assignments on disjoint variable blocks. -/
module

public import PPGraph.HLS.Probability.QueryLaw

@[expose] public section

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option backward.isDefEq.respectTransparency false

open Classical MeasureTheory

namespace HLS

variable {V : Type} [DecidableEq V] {S : VarSpaces V}

abbrev BlockState (S : VarSpaces V) (F : Finset V) := ∀ a : F, S.space a.val

noncomputable def blockMeasure (S : VarSpaces V) (F : Finset V) : Measure (BlockState S F) :=
  Measure.pi (fun a : F => S.measure a.val)

instance (F : Finset V) : IsProbabilityMeasure (blockMeasure S F) := by
  have : ∀ a : F, IsProbabilityMeasure (S.measure a.val) := fun a => S.isProb a.val
  unfold blockMeasure
  infer_instance

noncomputable def joinBlocks (F H : Finset V) (hd : Disjoint F H)
    (xy : BlockState S F × BlockState S H) : MTState S := by
  haveI : ∀ a, IsProbabilityMeasure (S.measure a) := S.isProb
  exact extendDefault (fun a => S.measure a) (F ∪ H)
    (MeasurableEquiv.piFinsetUnion S.space hd xy)

theorem measurable_joinBlocks (F H : Finset V) (hd : Disjoint F H) :
    Measurable (joinBlocks (S := S) F H hd) := by
  have : ∀ a, IsProbabilityMeasure (S.measure a) := S.isProb
  exact (measurable_extendDefault (fun a => S.measure a) (F ∪ H)).comp
    (MeasurableEquiv.piFinsetUnion S.space hd).measurable

theorem joinBlocks_left (F H : Finset V) (hd : Disjoint F H)
    (xy : BlockState S F × BlockState S H) (a : V) (ha : a ∈ F) :
    joinBlocks F H hd xy a = xy.1 ⟨a, ha⟩ := by
  have : ∀ a, IsProbabilityMeasure (S.measure a) := S.isProb
  dsimp only [joinBlocks]
  have hU := Finset.mem_union_left H ha
  have h := congrFun (extendDefault_restrict (fun a => S.measure a) (F ∪ H)
    (MeasurableEquiv.piFinsetUnion S.space hd xy)) ⟨a, hU⟩
  simp only [Finset.restrict] at h
  rw [h]
  exact Equiv.piFinsetUnion_left S.space hd ha hU

theorem joinBlocks_right (F H : Finset V) (hd : Disjoint F H)
    (xy : BlockState S F × BlockState S H) (a : V) (ha : a ∈ H) :
    joinBlocks F H hd xy a = xy.2 ⟨a, ha⟩ := by
  have : ∀ a, IsProbabilityMeasure (S.measure a) := S.isProb
  dsimp only [joinBlocks]
  have hU := Finset.mem_union_right F ha
  have h := congrFun (extendDefault_restrict (fun a => S.measure a) (F ∪ H)
    (MeasurableEquiv.piFinsetUnion S.space hd xy)) ⟨a, hU⟩
  simp only [Finset.restrict] at h
  rw [h]
  exact Equiv.piFinsetUnion_right S.space hd ha hU

theorem measure_joinBlocks_preimage [Fintype V] (F H : Finset V) (hd : Disjoint F H)
    (A : Set (MTState S)) (hA : MeasurableSet A)
    (hdep : ∀ σ τ : MTState S, (∀ a ∈ F ∪ H, σ a = τ a) → (σ ∈ A ↔ τ ∈ A)) :
    ((blockMeasure S F).prod (blockMeasure S H)) (joinBlocks F H hd ⁻¹' A) =
      Measure.pi (fun a => S.measure a) A := by
  have : ∀ a, IsProbabilityMeasure (S.measure a) := S.isProb
  have hmp := measurePreserving_piFinsetUnion hd (fun a => S.measure a)
  have hExt : MeasurableSet (extendDefault (fun a => S.measure a) (F ∪ H) ⁻¹' A) :=
    hA.preimage (measurable_extendDefault (fun a => S.measure a) _)
  calc
    _ = (blockMeasure S (F ∪ H))
        (extendDefault (fun a => S.measure a) (F ∪ H) ⁻¹' A) := by
      calc
        _ = (((blockMeasure S F).prod (blockMeasure S H)).map
            (MeasurableEquiv.piFinsetUnion S.space hd))
              (extendDefault (fun a => S.measure a) (F ∪ H) ⁻¹' A) :=
          (Measure.map_apply hmp.measurable hExt).symm
        _ = _ := congrArg (fun μ => μ (extendDefault (fun a => S.measure a) (F ∪ H) ⁻¹' A))
          hmp.map_eq
    _ = Measure.infinitePi (fun a => S.measure a) A :=
      (infinitePi_eq_pi_of_dependsOn (fun a => S.measure a) hdep hA).symm
    _ = _ := by rw [Measure.infinitePi_eq_pi]

noncomputable def joinThree (F H Z : Finset V) (hFZ : Disjoint F Z) (hUZ : Disjoint (F ∪ Z) H)
    (xyz : (BlockState S F × BlockState S Z) × BlockState S H) : MTState S :=
  joinBlocks (F ∪ Z) H hUZ (MeasurableEquiv.piFinsetUnion S.space hFZ xyz.1, xyz.2)

theorem measurable_joinThree (F H Z : Finset V) (hFZ : Disjoint F Z)
    (hUZ : Disjoint (F ∪ Z) H) : Measurable (joinThree (S := S) F H Z hFZ hUZ) :=
  (measurable_joinBlocks (F ∪ Z) H hUZ).comp
    (((MeasurableEquiv.piFinsetUnion S.space hFZ).measurable.comp measurable_fst).prodMk
      measurable_snd)

theorem joinThree_left (F H Z : Finset V) (hFZ : Disjoint F Z)
    (hUZ : Disjoint (F ∪ Z) H) (xyz : (BlockState S F × BlockState S Z) × BlockState S H)
    (a : V) (ha : a ∈ F) : joinThree F H Z hFZ hUZ xyz a = xyz.1.1 ⟨a, ha⟩ := by
  rw [joinThree, joinBlocks_left _ _ _ _ a (Finset.mem_union_left Z ha)]
  exact Equiv.piFinsetUnion_left S.space hFZ ha (Finset.mem_union_left Z ha)

theorem joinThree_middle (F H Z : Finset V) (hFZ : Disjoint F Z)
    (hUZ : Disjoint (F ∪ Z) H) (xyz : (BlockState S F × BlockState S Z) × BlockState S H)
    (a : V) (ha : a ∈ H) : joinThree F H Z hFZ hUZ xyz a = xyz.2 ⟨a, ha⟩ := by
  exact joinBlocks_right _ _ _ _ a ha

theorem joinThree_right (F H Z : Finset V) (hFZ : Disjoint F Z)
    (hUZ : Disjoint (F ∪ Z) H) (xyz : (BlockState S F × BlockState S Z) × BlockState S H)
    (a : V) (ha : a ∈ Z) : joinThree F H Z hFZ hUZ xyz a = xyz.1.2 ⟨a, ha⟩ := by
  rw [joinThree, joinBlocks_left _ _ _ _ a (Finset.mem_union_right F ha)]
  exact Equiv.piFinsetUnion_right S.space hFZ ha (Finset.mem_union_right F ha)

theorem measure_joinThree_preimage [Fintype V] (F H Z : Finset V) (hFZ : Disjoint F Z)
    (hUZ : Disjoint (F ∪ Z) H) (A : Set (MTState S)) (hA : MeasurableSet A)
    (hdep : ∀ σ τ : MTState S, (∀ a ∈ (F ∪ Z) ∪ H, σ a = τ a) → (σ ∈ A ↔ τ ∈ A)) :
    (((blockMeasure S F).prod (blockMeasure S Z)).prod (blockMeasure S H))
      (joinThree F H Z hFZ hUZ ⁻¹' A) = Measure.pi (fun a => S.measure a) A := by
  have : ∀ a, IsProbabilityMeasure (S.measure a) := S.isProb
  have hmp := (measurePreserving_piFinsetUnion hFZ (fun a => S.measure a)).prod
    (MeasurePreserving.id (blockMeasure S H))
  have hMeas := hA.preimage (measurable_joinBlocks (F ∪ Z) H hUZ)
  calc
    _ = ((blockMeasure S (F ∪ Z)).prod (blockMeasure S H))
        (joinBlocks (F ∪ Z) H hUZ ⁻¹' A) := by
      calc
        _ = ((((blockMeasure S F).prod (blockMeasure S Z)).prod (blockMeasure S H)).map
            (Prod.map (MeasurableEquiv.piFinsetUnion S.space hFZ) id))
              (joinBlocks (F ∪ Z) H hUZ ⁻¹' A) :=
          (Measure.map_apply hmp.measurable hMeas).symm
        _ = _ := congrArg (fun μ => μ (joinBlocks (F ∪ Z) H hUZ ⁻¹' A)) hmp.map_eq
    _ = _ := measure_joinBlocks_preimage (F ∪ Z) H hUZ A hA hdep

end HLS

#check @HLS.measurable_joinBlocks
#check @HLS.joinBlocks_left
#check @HLS.joinBlocks_right
#check @HLS.measure_joinBlocks_preimage
#check @HLS.measurable_joinThree
#check @HLS.joinThree_left
#check @HLS.joinThree_middle
#check @HLS.joinThree_right
#check @HLS.measure_joinThree_preimage
