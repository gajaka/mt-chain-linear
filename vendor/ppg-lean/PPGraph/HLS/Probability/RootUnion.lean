/- Ordinal occurrence unions, orientation augmentation, and unique-root counting. -/
module

public import PPGraph.HLS.Bounds.OrdinalOccurrence
public import PPGraph.HLS.Probability.UnitChecks

@[expose] public section

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option backward.isDefEq.respectTransparency false

open Classical MeasureTheory
open scoped ENNReal

namespace HLS.WitnessDAG

variable {V : Type} [DecidableEq V] {S : VarSpaces V}
  {ι : Type} [Fintype ι] [DecidableEq ι] [Nonempty ι]

abbrev RootFamily (G : SimpleGraph ι) (α : ι) (r : ℕ) :=
  {D : HLS.WitnessDAG ι // RootedCanonical G (α, r) D}

noncomputable def rootUnion (P : MTProcess S ι) (α : ι) (r : ℕ) : Set (LogSpace S) :=
  ⋃ D : RootFamily (Shearer.dependencyGraph P.footprint) α r, tableCheck P D.val

theorem measurableSet_rootUnion (P : MTProcess S ι)
    (hbad : ∀ i, MeasurableSet (P.bad i)) (α : ι) (r : ℕ) :
    MeasurableSet (rootUnion P α r) :=
  MeasurableSet.iUnion (fun D => measurableSet_tableCheck P D.val hbad)

theorem ordinalOccurrence_subset_rootUnion (P : MTProcess S ι) (α : ι) (r : ℕ) :
    ordinalOccurrence P α r ⊆ rootUnion P α r := by
  rintro ω ⟨t, ht, hr⟩
  have hroot : realRoot P ω t = (α, r) := Prod.ext ht.2 hr
  have hD : RootedCanonical (Shearer.dependencyGraph P.footprint) (α, r) (realDAG P ω t) := by
    refine ⟨realDAG_valid P ω t, realDAG_canonical P ω t, ?_, ?_⟩
    · simpa only [hroot] using realRoot_mem P ω t
    · intro u hu
      simpa only [hroot] using realDAG_reach_root P ω t u hu
  exact Set.mem_iUnion.mpr ⟨⟨realDAG P ω t, hD⟩, realDAG_tableCheck_of_running P ω t ht.1⟩

theorem rootUnion_preimage_subset_unitCheck_union (P : MTProcess S ι)
    (M : DependencyMatching (Shearer.dependencyGraph P.footprint)) (α : ι) (r : ℕ) :
    (originalTable (S := S) (ι := ι)) ⁻¹' rootUnion P α r ⊆
      ⋃ D : RootFamily (Shearer.dependencyGraph P.footprint) α r, unitCheck P M D.val := by
  intro η hη
  obtain ⟨D, hD⟩ := Set.mem_iUnion.mp hη
  obtain ⟨E, hE, _, haug⟩ := exists_augmented_same_root P M
    (fun q => coinLabel M q.1 (auxiliaryCoins η q)) (α, r) D.val D.property (originalTable η) hD
  exact Set.mem_iUnion.mpr ⟨⟨E, hE⟩, augmentedCheck_implies_unitCheck P M E hE.1 (α, r) η haug⟩

theorem measure_rootUnion_le_tsum_unitCheck (P : MTProcess S ι)
    (hbad : ∀ i, MeasurableSet (P.bad i))
    (M : DependencyMatching (Shearer.dependencyGraph P.footprint)) (α : ι) (r : ℕ) :
    logMeasure S (rootUnion P α r) ≤
      ∑' D : RootFamily (Shearer.dependencyGraph P.footprint) α r,
        logMeasure (augmentedSpaces S) (unitCheck P M D.val) := by
  calc
    _ = logMeasure (augmentedSpaces (ι := ι) S)
        ((originalTable (S := S) (ι := ι)) ⁻¹' rootUnion P α r) := by
      rw [← map_originalTable (ι := ι) S,
        Measure.map_apply (measurable_originalTable S) (measurableSet_rootUnion P hbad α r)]
    _ ≤ logMeasure (augmentedSpaces S)
        (⋃ D : RootFamily (Shearer.dependencyGraph P.footprint) α r, unitCheck P M D.val) :=
      measure_mono (rootUnion_preimage_subset_unitCheck_union P M α r)
    _ ≤ _ := measure_iUnion_le _

noncomputable def rootedFamilyMap (G : SimpleGraph ι) (α : ι)
    (F : Σ r : ℕ, RootFamily G α r) : ProperFamily G Finset.univ α :=
  ⟨F.2.val, F.2.property.1, F.2.property.2.1, (fun _ _ => Finset.mem_univ _),
    (α, F.1), F.2.property.2.2.1, rfl, F.2.property.2.2.2⟩

theorem rootedFamilyMap_injective (G : SimpleGraph ι) (α : ι) :
    Function.Injective (rootedFamilyMap G α) := by
  rintro ⟨r, ⟨D, hD⟩⟩ ⟨s, ⟨E, hE⟩⟩ h
  have hDE : D = E := congrArg Subtype.val h
  subst E
  have hSink := proper_root_sink G D hE.1 (α, s) hE.2.2.1 hE.2.2.2
  have hroot := sink_eq_root D (α, r) (α, s) hD.2.2.2 hSink
  have hsr : s = r := congrArg Prod.snd hroot
  subst s
  rfl

theorem tsum_rootFamily_weight_le (G : SimpleGraph ι) (α : ι) (w : HLS.WitnessDAG ι → ℝ≥0∞) :
    (∑' r : ℕ, ∑' D : RootFamily G α r, w D.val) ≤
      ∑' D : ProperFamily G Finset.univ α, w D.val := by
  rw [← ENNReal.tsum_sigma]
  exact ENNReal.tsum_comp_le_tsum_of_injective (rootedFamilyMap_injective G α) (fun D => w D.val)

end HLS.WitnessDAG

#check @HLS.WitnessDAG.measurableSet_rootUnion
#check @HLS.WitnessDAG.ordinalOccurrence_subset_rootUnion
#check @HLS.WitnessDAG.rootUnion_preimage_subset_unitCheck_union
#check @HLS.WitnessDAG.measure_rootUnion_le_tsum_unitCheck
#check @HLS.WitnessDAG.rootedFamilyMap_injective
#check @HLS.WitnessDAG.tsum_rootFamily_weight_le
