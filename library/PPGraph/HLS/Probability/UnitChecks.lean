/- Independent single-node and selected-pair units of an augmented DAG check. -/
module

public import PPGraph.HLS.Probability.AugmentedDependence

@[expose] public section

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option backward.isDefEq.respectTransparency false

open Classical MeasureTheory

namespace HLS.WitnessDAG

variable {V : Type} [DecidableEq V] {S : VarSpaces V}
  {ι : Type} [Fintype ι] [DecidableEq ι] [Nonempty ι]

abbrev CheckUnit (ι : Type) := WNode ι ⊕ (WNode ι × WNode ι)

noncomputable def checkUnits (P : MTProcess S ι)
    (M : DependencyMatching (Shearer.dependencyGraph P.footprint)) (D : HLS.WitnessDAG ι) :
    Finset (CheckUnit ι) :=
  (D.nodes \ arcNodes (selectedArcs M D)).image Sum.inl ∪ (selectedArcs M D).image Sum.inr

noncomputable def unitCoordinates (P : MTProcess S ι)
    (M : DependencyMatching (Shearer.dependencyGraph P.footprint)) (D : HLS.WitnessDAG ι) :
    CheckUnit ι → Finset (ℕ × (V ⊕ Finset ι)) :=
  Sum.elim (dataCoordinates P D) (pairCoordinates P M D)

noncomputable def unitEvent (P : MTProcess S ι)
    (M : DependencyMatching (Shearer.dependencyGraph P.footprint)) (D : HLS.WitnessDAG ι) :
    CheckUnit ι → Set (LogSpace (augmentedSpaces (ι := ι) S)) :=
  Sum.elim (fun u => originalTable ⁻¹' tableEvent P D u)
    (fun e => augmentedPairCheck P M D e.1 e.2)

noncomputable def unitCheck (P : MTProcess S ι)
    (M : DependencyMatching (Shearer.dependencyGraph P.footprint)) (D : HLS.WitnessDAG ι) :
    Set (LogSpace (augmentedSpaces (ι := ι) S)) := ⋂ U ∈ checkUnits P M D, unitEvent P M D U

theorem mem_checkUnits_single (P : MTProcess S ι)
    (M : DependencyMatching (Shearer.dependencyGraph P.footprint)) (D : HLS.WitnessDAG ι) (u : WNode ι) :
    Sum.inl u ∈ checkUnits P M D ↔ u ∈ D.nodes ∧ u ∉ arcNodes (selectedArcs M D) := by
  simp [checkUnits]

theorem mem_checkUnits_pair (P : MTProcess S ι)
    (M : DependencyMatching (Shearer.dependencyGraph P.footprint)) (D : HLS.WitnessDAG ι)
    (e : WNode ι × WNode ι) : Sum.inr e ∈ checkUnits P M D ↔ e ∈ selectedArcs M D := by
  simp [checkUnits]

theorem unitCoordinates_pairwiseDisjoint (P : MTProcess S ι)
    (M : DependencyMatching (Shearer.dependencyGraph P.footprint)) (D : HLS.WitnessDAG ι)
    (hD : D.Valid (Shearer.dependencyGraph P.footprint)) :
    (↑(checkUnits P M D) : Set (CheckUnit ι)).PairwiseDisjoint (unitCoordinates P M D) := by
  intro a ha b hb hne
  cases a with
  | inl u =>
    obtain ⟨hu, hnot⟩ := (mem_checkUnits_single P M D u).mp ha
    cases b with
    | inl v =>
      obtain ⟨hv, _⟩ := (mem_checkUnits_single P M D v).mp hb
      exact dataCoordinates_disjoint P D hD u v hu hv (fun h => hne (congrArg Sum.inl h))
    | inr e =>
      exact unselected_dataCoordinates_disjoint_pair P M D hD u hu hnot e ((mem_checkUnits_pair P M D e).mp hb)
  | inr e =>
    have he := (mem_checkUnits_pair P M D e).mp ha
    cases b with
    | inl v =>
      obtain ⟨hv, hnot⟩ := (mem_checkUnits_single P M D v).mp hb
      exact (unselected_dataCoordinates_disjoint_pair P M D hD v hv hnot e he).symm
    | inr f =>
      exact selected_pairCoordinates_disjoint P M D hD e f he ((mem_checkUnits_pair P M D f).mp hb)
        (fun h => hne (congrArg Sum.inr h))

theorem measurableSet_unitEvent (P : MTProcess S ι)
    (M : DependencyMatching (Shearer.dependencyGraph P.footprint)) (D : HLS.WitnessDAG ι)
    (hbad : ∀ i, MeasurableSet (P.bad i)) (U : CheckUnit ι) : MeasurableSet (unitEvent P M D U) := by
  cases U with
  | inl u => exact (measurableSet_tableEvent P D hbad u).preimage (measurable_originalTable S)
  | inr e => exact measurableSet_augmentedPairCheck P M D e.1 e.2 hbad

theorem unitEvent_depends_on_unitCoordinates (P : MTProcess S ι)
    (M : DependencyMatching (Shearer.dependencyGraph P.footprint)) (D : HLS.WitnessDAG ι)
    (U : CheckUnit ι) (η η' : LogSpace (augmentedSpaces S))
    (h : ∀ q ∈ unitCoordinates P M D U, η q = η' q) :
    η ∈ unitEvent P M D U ↔ η' ∈ unitEvent P M D U := by
  cases U with
  | inl u => exact originalTable_event_depends_on_dataCoordinates P D u η η' h
  | inr e => exact augmentedPairCheck_depends_on_pairCoordinates P M D e η η' h

theorem measurableSet_unitCheck (P : MTProcess S ι)
    (M : DependencyMatching (Shearer.dependencyGraph P.footprint)) (D : HLS.WitnessDAG ι)
    (hbad : ∀ i, MeasurableSet (P.bad i)) : MeasurableSet (unitCheck P M D) :=
  Finset.measurableSet_biInter _ (fun U _ => measurableSet_unitEvent P M D hbad U)

theorem logMeasure_unitCheck_eq_prod (P : MTProcess S ι)
    (M : DependencyMatching (Shearer.dependencyGraph P.footprint)) (D : HLS.WitnessDAG ι)
    (hD : D.Valid (Shearer.dependencyGraph P.footprint)) (hbad : ∀ i, MeasurableSet (P.bad i)) :
    logMeasure (augmentedSpaces S) (unitCheck P M D) =
      ∏ U ∈ checkUnits P M D, logMeasure (augmentedSpaces S) (unitEvent P M D U) := by
  have : ∀ q, IsProbabilityMeasure (μCoin (augmentedSpaces (ι := ι) S) q) :=
    fun q => (augmentedSpaces S).isProb q.2
  exact infinitePi_iInter_eq_prod_of_dependsOn (μCoin (augmentedSpaces S)) (checkUnits P M D)
    (unitCoordinates P M D) (unitEvent P M D) (unitCoordinates_pairwiseDisjoint P M D hD)
    (fun U _ => unitEvent_depends_on_unitCoordinates P M D U)
    (fun U _ => measurableSet_unitEvent P M D hbad U)

theorem logMeasure_unitCheck_eq_split_prod (P : MTProcess S ι)
    (M : DependencyMatching (Shearer.dependencyGraph P.footprint)) (D : HLS.WitnessDAG ι)
    (hD : D.Valid (Shearer.dependencyGraph P.footprint)) (hbad : ∀ i, MeasurableSet (P.bad i)) :
    logMeasure (augmentedSpaces S) (unitCheck P M D) =
      (∏ u ∈ D.nodes \ arcNodes (selectedArcs M D),
        logMeasure (augmentedSpaces (ι := ι) S) ((originalTable (S := S) (ι := ι)) ⁻¹' tableEvent P D u)) *
      ∏ e ∈ selectedArcs M D, logMeasure (augmentedSpaces S) (augmentedPairCheck P M D e.1 e.2) := by
  rw [logMeasure_unitCheck_eq_prod P M D hD hbad]
  unfold checkUnits
  have hd : Disjoint ((D.nodes \ arcNodes (selectedArcs M D)).image (Sum.inl : WNode ι → CheckUnit ι))
      ((selectedArcs M D).image Sum.inr) := by
    apply Finset.disjoint_left.mpr
    intro U hU hU'
    obtain ⟨u, _, hu⟩ := Finset.mem_image.mp hU
    obtain ⟨e, _, he⟩ := Finset.mem_image.mp hU'
    cases hu.trans he.symm
  rw [Finset.prod_union hd, Finset.prod_image (fun _ _ _ _ h => Sum.inl.inj h),
    Finset.prod_image (fun _ _ _ _ h => Sum.inr.inj h)]
  rfl

theorem augmentedCheck_implies_unitCheck (P : MTProcess S ι)
    (M : DependencyMatching (Shearer.dependencyGraph P.footprint)) (D : HLS.WitnessDAG ι)
    (hD : D.Valid (Shearer.dependencyGraph P.footprint)) (r : WNode ι)
    (η : LogSpace (augmentedSpaces S))
    (haug : AugmentedCheck P M (fun q => coinLabel M q.1 (auxiliaryCoins η q)) r D (originalTable η)) :
    η ∈ unitCheck P M D := by
  apply Set.mem_iInter₂.mpr
  intro U hU
  cases U with
  | inl u =>
    exact Set.mem_iInter₂.mp haug.1 u ((mem_checkUnits_single P M D u).mp hU).1
  | inr e =>
    obtain ⟨he, hm, hl, hr⟩ := Finset.mem_filter.mp
      (selectedArcs_subset M D ((mem_checkUnits_pair P M D e).mp hU))
    exact augmentedCheck_implies_pairCheck P M D hD r e.1 e.2 η haug he hr hm hl

end HLS.WitnessDAG

#check @HLS.WitnessDAG.mem_checkUnits_single
#check @HLS.WitnessDAG.mem_checkUnits_pair
#check @HLS.WitnessDAG.unitCoordinates_pairwiseDisjoint
#check @HLS.WitnessDAG.measurableSet_unitEvent
#check @HLS.WitnessDAG.unitEvent_depends_on_unitCoordinates
#check @HLS.WitnessDAG.measurableSet_unitCheck
#check @HLS.WitnessDAG.logMeasure_unitCheck_eq_prod
#check @HLS.WitnessDAG.logMeasure_unitCheck_eq_split_prod
#check @HLS.WitnessDAG.augmentedCheck_implies_unitCheck
