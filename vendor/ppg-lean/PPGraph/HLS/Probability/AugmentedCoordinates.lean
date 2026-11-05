/- Disjoint data and auxiliary-coin coordinate blocks for HLS Lemma 3.4. -/
module

public import PPGraph.HLS.Probability.AugmentedSpace
public import PPGraph.HLS.DAG.MatchingSelection
public import PPGraph.HLS.Encoding.TableCheck

@[expose] public section

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option backward.isDefEq.respectTransparency false

open Classical

namespace HLS.WitnessDAG

variable {V : Type} [DecidableEq V] {S : VarSpaces V}
  {ι : Type} [Fintype ι] [DecidableEq ι]

noncomputable def dataCoordinates (P : MTProcess S ι) (D : HLS.WitnessDAG ι) (u : WNode ι) :
    Finset (ℕ × (V ⊕ Finset ι)) :=
  (tableCoordinates P D u).image (fun q => (q.1, Sum.inl q.2))

noncomputable def coinCoordinate {P : MTProcess S ι}
    (M : DependencyMatching (Shearer.dependencyGraph P.footprint))
    (D : HLS.WitnessDAG ι) (e : WNode ι × WNode ι) : ℕ × (V ⊕ Finset ι) :=
  (D.cliqueRank (M.pair e.1.1) e.1, Sum.inr (M.pair e.1.1))

noncomputable def pairCoordinates (P : MTProcess S ι)
    (M : DependencyMatching (Shearer.dependencyGraph P.footprint))
    (D : HLS.WitnessDAG ι) (e : WNode ι × WNode ι) : Finset (ℕ × (V ⊕ Finset ι)) :=
  (dataCoordinates P D e.1 ∪ dataCoordinates P D e.2) ∪ {coinCoordinate M D e}

theorem coinCoordinate_not_dataCoordinates (P : MTProcess S ι)
    (M : DependencyMatching (Shearer.dependencyGraph P.footprint))
    (D : HLS.WitnessDAG ι) (e : WNode ι × WNode ι) (u : WNode ι) :
    coinCoordinate M D e ∉ dataCoordinates P D u := by
  intro h
  obtain ⟨q, _, hq⟩ := Finset.mem_image.mp h
  have hs : Sum.inl q.2 = Sum.inr (α := V) (M.pair e.1.1) := congrArg Prod.snd hq
  cases hs

theorem dataCoordinates_disjoint (P : MTProcess S ι) (D : HLS.WitnessDAG ι)
    (hD : D.Valid (Shearer.dependencyGraph P.footprint)) (u v : WNode ι)
    (hu : u ∈ D.nodes) (hv : v ∈ D.nodes) (hne : u ≠ v) :
    Disjoint (dataCoordinates P D u) (dataCoordinates P D v) := by
  apply Finset.disjoint_left.mpr
  intro p hp hq
  obtain ⟨a, ha, hap⟩ := Finset.mem_image.mp hp
  obtain ⟨b, hb, hbp⟩ := Finset.mem_image.mp hq
  have hab : a = b := Prod.ext
    (congrArg (fun z : ℕ × (V ⊕ Finset ι) => z.1) (hap.trans hbp.symm))
    (Sum.inl.inj (congrArg (fun z : ℕ × (V ⊕ Finset ι) => z.2) (hap.trans hbp.symm)))
  exact Finset.disjoint_left.mp (tableCoordinates_disjoint P D hD u v hu hv hne) ha (hab.symm ▸ hb)

theorem selected_coinCoordinate_injective (P : MTProcess S ι)
    (M : DependencyMatching (Shearer.dependencyGraph P.footprint))
    (D : HLS.WitnessDAG ι) (hD : D.Valid (Shearer.dependencyGraph P.footprint)) :
    Set.InjOn (coinCoordinate (V := V) M D)
      (↑(selectedArcs M D) : Set (WNode ι × WNode ι)) := by
  intro e he f hf h
  have hpair : M.pair e.1.1 = M.pair f.1.1 :=
    Sum.inr.inj (congrArg (fun z : ℕ × (V ⊕ Finset ι) => z.2) h)
  have hrank : D.cliqueRank (M.pair e.1.1) e.1 = D.cliqueRank (M.pair f.1.1) f.1 :=
    congrArg (fun z : ℕ × (V ⊕ Finset ι) => z.1) h
  rw [← hpair] at hrank
  have heData := Finset.mem_filter.mp (selectedArcs_subset M D he)
  have hfData := Finset.mem_filter.mp (selectedArcs_subset M D hf)
  have hsource := eq_of_cliqueRank_eq _ D hD _ (M.pair_is_clique e.1.1) e.1 f.1
    (hD.supported _ _ heData.1).1 (hD.supported _ _ hfData.1).1
    (M.mem_pair_self e.1.1) (hpair.symm ▸ M.mem_pair_self f.1.1) hrank
  by_contra hne
  exact Finset.disjoint_left.mp (selectedArcs_endpoints_disjoint M D hD e he f hf hne)
    (by simp : e.1 ∈ ({e.1, e.2} : Finset (WNode ι)))
    (Finset.mem_insert.mpr (Or.inl hsource))

theorem selected_pairCoordinates_disjoint (P : MTProcess S ι)
    (M : DependencyMatching (Shearer.dependencyGraph P.footprint))
    (D : HLS.WitnessDAG ι) (hD : D.Valid (Shearer.dependencyGraph P.footprint))
    (e f : WNode ι × WNode ι) (he : e ∈ selectedArcs M D) (hf : f ∈ selectedArcs M D)
    (hne : e ≠ f) : Disjoint (pairCoordinates P M D e) (pairCoordinates P M D f) := by
  have hd := selectedArcs_endpoints_disjoint M D hD e he f hf hne
  have heData := Finset.mem_filter.mp (selectedArcs_subset M D he)
  have hfData := Finset.mem_filter.mp (selectedArcs_subset M D hf)
  have hdata : ∀ u ∈ ({e.1, e.2} : Finset (WNode ι)), ∀ v ∈ ({f.1, f.2} : Finset (WNode ι)),
      Disjoint (dataCoordinates P D u) (dataCoordinates P D v) := by
    intro u hu v hv
    have huD : u ∈ D.nodes := by
      simp only [Finset.mem_insert, Finset.mem_singleton] at hu
      rcases hu with rfl | rfl
      · exact (hD.supported _ _ heData.1).1
      · exact (hD.supported _ _ heData.1).2
    have hvD : v ∈ D.nodes := by
      simp only [Finset.mem_insert, Finset.mem_singleton] at hv
      rcases hv with rfl | rfl
      · exact (hD.supported _ _ hfData.1).1
      · exact (hD.supported _ _ hfData.1).2
    have huv : u ≠ v := by intro h; exact Finset.disjoint_left.mp hd hu (h.symm ▸ hv)
    exact dataCoordinates_disjoint P D hD u v huD hvD huv
  have hcoin : coinCoordinate (V := V) M D e ≠ coinCoordinate M D f :=
    fun h => hne (selected_coinCoordinate_injective P M D hD he hf h)
  apply Finset.disjoint_left.mpr
  intro q hqe hqf
  rcases Finset.mem_union.mp hqe with hqe | hqe
  · rcases Finset.mem_union.mp hqf with hqf | hqf
    · rcases Finset.mem_union.mp hqe with hqe | hqe <;>
        rcases Finset.mem_union.mp hqf with hqf | hqf
      all_goals exact Finset.disjoint_left.mp (hdata _ (by simp) _ (by simp)) hqe hqf
    · have hq : q = coinCoordinate M D f := Finset.mem_singleton.mp hqf
      subst q
      rcases Finset.mem_union.mp hqe with hqe | hqe
      · exact coinCoordinate_not_dataCoordinates P M D f e.1 hqe
      · exact coinCoordinate_not_dataCoordinates P M D f e.2 hqe
  · have hq : q = coinCoordinate M D e := Finset.mem_singleton.mp hqe
    subst q
    rcases Finset.mem_union.mp hqf with hqf | hqf
    · rcases Finset.mem_union.mp hqf with hqf | hqf
      · exact coinCoordinate_not_dataCoordinates P M D e f.1 hqf
      · exact coinCoordinate_not_dataCoordinates P M D e f.2 hqf
    · exact hcoin (Finset.mem_singleton.mp hqf)

theorem unselected_dataCoordinates_disjoint_pair (P : MTProcess S ι)
    (M : DependencyMatching (Shearer.dependencyGraph P.footprint))
    (D : HLS.WitnessDAG ι) (hD : D.Valid (Shearer.dependencyGraph P.footprint))
    (u : WNode ι) (hu : u ∈ D.nodes) (hnot : u ∉ arcNodes (selectedArcs M D))
    (e : WNode ι × WNode ι) (he : e ∈ selectedArcs M D) :
    Disjoint (dataCoordinates P D u) (pairCoordinates P M D e) := by
  have heData := Finset.mem_filter.mp (selectedArcs_subset M D he)
  have hne₁ : u ≠ e.1 := by
    intro h; exact hnot (Finset.mem_biUnion.mpr ⟨e, he, h ▸ (by simp)⟩)
  have hne₂ : u ≠ e.2 := by
    intro h; exact hnot (Finset.mem_biUnion.mpr ⟨e, he, h ▸ (by simp)⟩)
  apply Finset.disjoint_union_right.mpr
  refine ⟨Finset.disjoint_union_right.mpr ⟨
    dataCoordinates_disjoint P D hD u e.1 hu (hD.supported _ _ heData.1).1 hne₁,
    dataCoordinates_disjoint P D hD u e.2 hu (hD.supported _ _ heData.1).2 hne₂⟩, ?_⟩
  exact Finset.disjoint_singleton_right.mpr (coinCoordinate_not_dataCoordinates P M D e u)

end HLS.WitnessDAG

#check @HLS.WitnessDAG.coinCoordinate_not_dataCoordinates
#check @HLS.WitnessDAG.dataCoordinates_disjoint
#check @HLS.WitnessDAG.selected_coinCoordinate_injective
#check @HLS.WitnessDAG.selected_pairCoordinates_disjoint
#check @HLS.WitnessDAG.unselected_dataCoordinates_disjoint_pair
