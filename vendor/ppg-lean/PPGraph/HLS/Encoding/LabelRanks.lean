/-
  Canonical occurrence indices for any finite witness DAG. Equal-label
  nodes form an acyclic complete chain. Counting their predecessors gives
  precisely the initial segment of natural numbers, so renaming introduces
  neither missing indices nor duplicate nodes.
-/
module

public import PPGraph.HLS.Encoding.CanonicalEncoding
public import PPGraph.HLS.Encoding.TableCheck

@[expose] public section

set_option autoImplicit false
set_option linter.unusedSectionVars false

open Classical

namespace HLS.WitnessDAG

variable {ι : Type} [DecidableEq ι]

noncomputable def labelNodes (D : HLS.WitnessDAG ι) (i : ι) : Finset (WNode ι) :=
  D.nodes.filter (fun u => u.1 = i)

noncomputable def labelPrior (D : HLS.WitnessDAG ι) (u : WNode ι) : Finset (WNode ι) :=
  D.nodes.filter (fun w => w.1 = u.1 ∧ D.Edge w u)

noncomputable def labelRank (D : HLS.WitnessDAG ι) (u : WNode ι) : ℕ :=
  (D.labelPrior u).card

noncomputable def canonicalName (D : HLS.WitnessDAG ι) (u : WNode ι) : WNode ι :=
  (u.1, D.labelRank u)

theorem labelPrior_strict (G : SimpleGraph ι) (D : HLS.WitnessDAG ι)
    (hD : D.Valid G) (u v : WNode ι) (huv : D.Edge u v) (hlabel : u.1 = v.1) :
    D.labelPrior u ⊂ D.labelPrior v := by
  have hsub : D.labelPrior u ⊆ D.labelPrior v := by
    intro w hw
    obtain ⟨hw, hwlabel, hwu⟩ := Finset.mem_filter.mp hw
    have hwv := edge_of_transGen_dependent G D hD w v
      ((Relation.TransGen.single hwu).tail huv) (Or.inl (hwlabel.trans hlabel))
    exact Finset.mem_filter.mpr ⟨hw, hwlabel.trans hlabel, hwv⟩
  apply lt_of_le_of_ne hsub
  intro heq
  have huin : u ∈ D.labelPrior v :=
    Finset.mem_filter.mpr ⟨(hD.supported u v huv).1, hlabel, huv⟩
  have hself := (Finset.mem_filter.mp (heq.symm ▸ huin)).2.2
  exact hD.acyclic.irrefl _ u hself

theorem labelRank_lt_of_edge (G : SimpleGraph ι) (D : HLS.WitnessDAG ι)
    (hD : D.Valid G) (u v : WNode ι) (huv : D.Edge u v) (hlabel : u.1 = v.1) :
    D.labelRank u < D.labelRank v := Finset.card_lt_card (labelPrior_strict G D hD u v huv hlabel)

theorem eq_of_same_labelRank (G : SimpleGraph ι) (D : HLS.WitnessDAG ι)
    (hD : D.Valid G) (u v : WNode ι) (hu : u ∈ D.nodes) (hv : v ∈ D.nodes)
    (hlabel : u.1 = v.1) (hrank : D.labelRank u = D.labelRank v) : u = v := by
  by_contra huv
  rcases (hD.oriented u hu v hv huv).mpr (Or.inl hlabel) with h | h
  · have hlt := labelRank_lt_of_edge G D hD u v h hlabel
    omega
  · have hlt := labelRank_lt_of_edge G D hD v u h hlabel.symm
    omega

theorem canonicalName_injective (G : SimpleGraph ι) (D : HLS.WitnessDAG ι)
    (hD : D.Valid G) : Set.InjOn D.canonicalName (↑D.nodes : Set (WNode ι)) := by
  intro u hu v hv h
  change (u.1, D.labelRank u) = (v.1, D.labelRank v) at h
  obtain ⟨hlabel, hrank⟩ := Prod.mk.inj h
  exact eq_of_same_labelRank G D hD u v hu hv hlabel hrank

theorem labelRank_lt_card (G : SimpleGraph ι) (D : HLS.WitnessDAG ι)
    (hD : D.Valid G) (u : WNode ι) (hu : u ∈ D.nodes) :
    D.labelRank u < (D.labelNodes u.1).card := by
  have hsub : D.labelPrior u ⊆ D.labelNodes u.1 := by
    intro w hw
    obtain ⟨hw, hlabel, _⟩ := Finset.mem_filter.mp hw
    exact Finset.mem_filter.mpr ⟨hw, hlabel⟩
  apply Finset.card_lt_card (lt_of_le_of_ne hsub ?_)
  intro heq
  have huin : u ∈ D.labelNodes u.1 := Finset.mem_filter.mpr ⟨hu, rfl⟩
  have hself := (Finset.mem_filter.mp (heq.symm ▸ huin)).2.2
  exact hD.acyclic.irrefl _ u hself

theorem labelRank_image_eq_range (G : SimpleGraph ι) (D : HLS.WitnessDAG ι)
    (hD : D.Valid G) (i : ι) :
    (D.labelNodes i).image D.labelRank = Finset.range (D.labelNodes i).card := by
  have hinj : Set.InjOn D.labelRank (↑(D.labelNodes i) : Set (WNode ι)) := by
    intro u hu v hv h
    obtain ⟨hu, hui⟩ := Finset.mem_filter.mp hu
    obtain ⟨hv, hvi⟩ := Finset.mem_filter.mp hv
    exact eq_of_same_labelRank G D hD u v hu hv (hui.trans hvi.symm) h
  have hsub : (D.labelNodes i).image D.labelRank ⊆ Finset.range (D.labelNodes i).card := by
    intro n hn
    obtain ⟨u, hu, rfl⟩ := Finset.mem_image.mp hn
    obtain ⟨hu, hui⟩ := Finset.mem_filter.mp hu
    exact Finset.mem_range.mpr (by simpa only [hui] using labelRank_lt_card G D hD u hu)
  apply Finset.eq_of_subset_of_card_le hsub
  rw [Finset.card_range, Finset.card_image_of_injOn hinj]

theorem exists_node_of_labelRank_lt (G : SimpleGraph ι) (D : HLS.WitnessDAG ι)
    (hD : D.Valid G) (i : ι) (n : ℕ) (hn : n < (D.labelNodes i).card) :
    ∃ u ∈ D.nodes, u.1 = i ∧ D.labelRank u = n := by
  have hmem : n ∈ (D.labelNodes i).image D.labelRank := by
    rw [labelRank_image_eq_range G D hD i]
    exact Finset.mem_range.mpr hn
  obtain ⟨u, hu, hun⟩ := Finset.mem_image.mp hmem
  obtain ⟨hu, hui⟩ := Finset.mem_filter.mp hu
  exact ⟨u, hu, hui, hun⟩

theorem labelPrior_eq_earlierLabelNodes (G : SimpleGraph ι) (D : HLS.WitnessDAG ι)
    (hD : D.Valid G) (hcanon : D.Canonical) (u : WNode ι) (hu : u ∈ D.nodes) :
    D.labelPrior u = D.earlierLabelNodes u.1 u.2 := by
  ext w
  simp only [labelPrior, earlierLabelNodes, Finset.mem_filter]
  constructor
  · rintro ⟨hw, hwlabel, hwu⟩
    have hheight := height_lt_of_edge G D hD w u hwu
    have hw' : (u.1, w.2) ∈ D.nodes := (Prod.ext hwlabel rfl : w = (u.1, w.2)) ▸ hw
    have hindex : w.2 < u.2 :=
      (same_label_height_iff_index G D hD hcanon u.1 w.2 u.2 hw' hu).mp
        (by convert hheight using 1; exact congrArg (height G D hD) (Prod.ext hwlabel.symm rfl))
    exact ⟨hw, hwlabel, hindex⟩
  · rintro ⟨hw, hwlabel, hindex⟩
    have hw' : (u.1, w.2) ∈ D.nodes := (Prod.ext hwlabel rfl : w = (u.1, w.2)) ▸ hw
    have hedge := hcanon.2 u.1 w.2 u.2 hw' hu hindex
    exact ⟨hw, hwlabel, by convert hedge using 1; exact Prod.ext hwlabel rfl⟩

theorem labelRank_eq_index_of_canonical (G : SimpleGraph ι) (D : HLS.WitnessDAG ι)
    (hD : D.Valid G) (hcanon : D.Canonical) (u : WNode ι) (hu : u ∈ D.nodes) :
    D.labelRank u = u.2 := by
  rw [labelRank, labelPrior_eq_earlierLabelNodes G D hD hcanon u hu]
  exact earlierLabelNodes_card D hcanon u.1 u.2 hu

theorem canonicalName_eq_of_canonical (G : SimpleGraph ι) (D : HLS.WitnessDAG ι)
    (hD : D.Valid G) (hcanon : D.Canonical) (u : WNode ι) (hu : u ∈ D.nodes) :
    D.canonicalName u = u := by
  rw [canonicalName, labelRank_eq_index_of_canonical G D hD hcanon u hu]

end HLS.WitnessDAG

#check @HLS.WitnessDAG.labelPrior_strict
#check @HLS.WitnessDAG.labelRank_lt_of_edge
#check @HLS.WitnessDAG.eq_of_same_labelRank
#check @HLS.WitnessDAG.canonicalName_injective
#check @HLS.WitnessDAG.labelRank_lt_card
#check @HLS.WitnessDAG.labelRank_image_eq_range
#check @HLS.WitnessDAG.exists_node_of_labelRank_lt
#check @HLS.WitnessDAG.labelPrior_eq_earlierLabelNodes
#check @HLS.WitnessDAG.labelRank_eq_index_of_canonical
#check @HLS.WitnessDAG.canonicalName_eq_of_canonical
