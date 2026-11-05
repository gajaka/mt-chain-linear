/-
  Disjoint matching-reversible arcs covering at least half the incident
  nodes of every label (He--Li--Sun Proposition 3.2). The two parity
  choices for each pair are compared by arc count.
-/
module

public import PPGraph.HLS.DAG.ParitySelection
public import PPGraph.HLS.DAG.PairKeys

@[expose] public section

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option backward.isDefEq.respectTransparency false

open Classical

namespace HLS.WitnessDAG

variable {ι : Type} [Fintype ι] [DecidableEq ι] {G : SimpleGraph ι}

noncomputable def matchingArcs (M : DependencyMatching G) (D : HLS.WitnessDAG ι) :
    Finset (WNode ι × WNode ι) := D.arcs.filter (fun e =>
      M.mate e.1.1 = e.2.1 ∧ e.1.1 ≠ e.2.1 ∧ Acyclic (reverseArc D.Edge e.1 e.2))

noncomputable def pairArcs (M : DependencyMatching G) (D : HLS.WitnessDAG ι) (i : ι) :
    Finset (WNode ι × WNode ι) :=
  (matchingArcs M D).filter (fun e => M.pair e.1.1 = M.pair i)

noncomputable def selectedPairArcs (M : DependencyMatching G) (D : HLS.WitnessDAG ι) (i : ι) :
    Finset (WNode ι × WNode ι) :=
  largerParity (pairArcs M D i) (D.cliqueRank (M.pair i))

noncomputable def selectedArcs (M : DependencyMatching G) (D : HLS.WitnessDAG ι) :
    Finset (WNode ι × WNode ι) := Finset.univ.biUnion (selectedPairArcs M D)

noncomputable def arcNodes (E : Finset (WNode ι × WNode ι)) : Finset (WNode ι) :=
  E.biUnion (fun e => {e.1, e.2})

theorem mem_pairArcs_data (M : DependencyMatching G) (D : HLS.WitnessDAG ι)
    (i : ι) (e : WNode ι × WNode ι) (he : e ∈ pairArcs M D i) :
    D.Edge e.1 e.2 ∧ M.mate e.1.1 = e.2.1 ∧ e.1.1 ≠ e.2.1 ∧
      Acyclic (reverseArc D.Edge e.1 e.2) ∧ M.pair e.1.1 = M.pair i := by
  obtain ⟨he, hkey⟩ := Finset.mem_filter.mp he
  obtain ⟨he, hm, hl, hrev⟩ := Finset.mem_filter.mp he
  exact ⟨he, hm, hl, hrev, hkey⟩

theorem pairArc_labels_mem (M : DependencyMatching G) (D : HLS.WitnessDAG ι)
    (i : ι) (e : WNode ι × WNode ι) (he : e ∈ pairArcs M D i) :
    e.1.1 ∈ M.pair i ∧ e.2.1 ∈ M.pair i := by
  obtain ⟨_, hm, _, _, hkey⟩ := mem_pairArcs_data M D i e he
  constructor
  · exact hkey ▸ M.mem_pair_self e.1.1
  · exact hkey ▸ hm ▸ M.mem_pair_mate e.1.1

theorem pairArcs_eq_of_pair_eq (M : DependencyMatching G) (D : HLS.WitnessDAG ι)
    (i j : ι) (h : M.pair i = M.pair j) : pairArcs M D i = pairArcs M D j := by
  simp only [pairArcs, h]

theorem selectedPairArcs_eq_of_pair_eq (M : DependencyMatching G) (D : HLS.WitnessDAG ι)
    (i j : ι) (h : M.pair i = M.pair j) : selectedPairArcs M D i = selectedPairArcs M D j := by
  simp only [selectedPairArcs, pairArcs, h]

theorem selectedPairArcs_subset (M : DependencyMatching G) (D : HLS.WitnessDAG ι) (i : ι) :
    selectedPairArcs M D i ⊆ pairArcs M D i := largerParity_subset _ _

theorem selectedPairArcs_half (M : DependencyMatching G) (D : HLS.WitnessDAG ι) (i : ι) :
    (pairArcs M D i).card ≤ 2 * (selectedPairArcs M D i).card := largerParity_half _ _

theorem selectedPairArcs_endpoints_disjoint (M : DependencyMatching G) (D : HLS.WitnessDAG ι)
    (hD : D.Valid G) (i : ι) (e : WNode ι × WNode ι)
    (he : e ∈ selectedPairArcs M D i) (f : WNode ι × WNode ι)
    (hf : f ∈ selectedPairArcs M D i) (hne : e ≠ f) :
    Disjoint ({e.1, e.2} : Finset (WNode ι)) {f.1, f.2} := by
  apply largerParity_endpoints_disjoint _ _ ?_ ?_ e he f hf hne
  · intro u hu v hv hrank
    obtain ⟨eu, heu, hu⟩ := Finset.mem_biUnion.mp hu
    obtain ⟨ev, hev, hv⟩ := Finset.mem_biUnion.mp hv
    have hue := mem_pairArcs_data M D i eu heu
    have hve := mem_pairArcs_data M D i ev hev
    have huJ := pairArc_labels_mem M D i eu heu
    have hvJ := pairArc_labels_mem M D i ev hev
    have huData : u ∈ D.nodes ∧ u.1 ∈ M.pair i := by
      simp only [Finset.mem_insert, Finset.mem_singleton] at hu
      rcases hu with rfl | rfl
      · exact ⟨(hD.supported _ _ hue.1).1, huJ.1⟩
      · exact ⟨(hD.supported _ _ hue.1).2, huJ.2⟩
    have hvData : v ∈ D.nodes ∧ v.1 ∈ M.pair i := by
      simp only [Finset.mem_insert, Finset.mem_singleton] at hv
      rcases hv with rfl | rfl
      · exact ⟨(hD.supported _ _ hve.1).1, hvJ.1⟩
      · exact ⟨(hD.supported _ _ hve.1).2, hvJ.2⟩
    exact eq_of_cliqueRank_eq G D hD _ (M.pair_is_clique i) u v
      huData.1 hvData.1 huData.2 hvData.2 hrank
  · intro e he
    obtain ⟨hedge, _, _, hrev, _⟩ := mem_pairArcs_data M D i e he
    obtain ⟨huJ, hvJ⟩ := pairArc_labels_mem M D i e he
    exact cliqueRank_reversible_consecutive G D hD _ (M.pair_is_clique i)
      _ _ hedge hrev huJ hvJ

theorem selectedArcs_subset (M : DependencyMatching G) (D : HLS.WitnessDAG ι) :
    selectedArcs M D ⊆ matchingArcs M D := by
  intro e he
  obtain ⟨i, _, hi⟩ := Finset.mem_biUnion.mp he
  exact (Finset.mem_filter.mp (selectedPairArcs_subset M D i hi)).1

theorem selectedArcs_endpoints_disjoint (M : DependencyMatching G) (D : HLS.WitnessDAG ι)
    (hD : D.Valid G) (e : WNode ι × WNode ι) (he : e ∈ selectedArcs M D)
    (f : WNode ι × WNode ι) (hf : f ∈ selectedArcs M D) (hne : e ≠ f) :
    Disjoint ({e.1, e.2} : Finset (WNode ι)) {f.1, f.2} := by
  obtain ⟨i, _, hei⟩ := Finset.mem_biUnion.mp he
  obtain ⟨j, _, hfj⟩ := Finset.mem_biUnion.mp hf
  by_cases hkey : M.pair i = M.pair j
  · have hfj' := (selectedPairArcs_eq_of_pair_eq M D i j hkey).symm ▸ hfj
    exact selectedPairArcs_endpoints_disjoint M D hD i e hei f hfj' hne
  · apply Finset.disjoint_left.mpr
    intro w hwe hwf
    have hi := pairArc_labels_mem M D i e (selectedPairArcs_subset M D i hei)
    have hj := pairArc_labels_mem M D j f (selectedPairArcs_subset M D j hfj)
    have hwi : w.1 ∈ M.pair i := by
      simp only [Finset.mem_insert, Finset.mem_singleton] at hwe
      rcases hwe with rfl | rfl <;> tauto
    have hwj : w.1 ∈ M.pair j := by
      simp only [Finset.mem_insert, Finset.mem_singleton] at hwf
      rcases hwf with rfl | rfl <;> tauto
    exact Finset.disjoint_left.mp (M.pair_disjoint_of_ne i j hkey) hwi hwj

def labelEndpoint (i : ι) (e : WNode ι × WNode ι) : WNode ι :=
  if e.1.1 = i then e.1 else e.2

theorem labelEndpoint_mem (i : ι) (e : WNode ι × WNode ι) :
    labelEndpoint i e ∈ ({e.1, e.2} : Finset (WNode ι)) := by
  unfold labelEndpoint
  split_ifs <;> simp

theorem labelEndpoint_label (M : DependencyMatching G) (D : HLS.WitnessDAG ι)
    (i : ι) (e : WNode ι × WNode ι) (he : e ∈ pairArcs M D i) :
    (labelEndpoint i e).1 = i := by
  obtain ⟨_, hm, _, _, _⟩ := mem_pairArcs_data M D i e he
  have huJ := (pairArc_labels_mem M D i e he).1
  simp only [DependencyMatching.pair, Finset.mem_insert, Finset.mem_singleton] at huJ
  unfold labelEndpoint
  split_ifs with hi
  · exact hi
  · have hus : e.1.1 = M.mate i := huJ.resolve_left hi
    rw [← hm, hus, M.involutive i]

theorem selected_labelEndpoint_injective (M : DependencyMatching G) (D : HLS.WitnessDAG ι)
    (hD : D.Valid G) (i : ι) :
    Set.InjOn (labelEndpoint i) (↑(selectedPairArcs M D i) : Set (WNode ι × WNode ι)) := by
  intro e he f hf h
  by_contra hne
  have hd := selectedPairArcs_endpoints_disjoint M D hD i e he f hf hne
  exact Finset.disjoint_left.mp hd (labelEndpoint_mem i e) (h.symm ▸ labelEndpoint_mem i f)

theorem incident_labelNodes_subset_image (M : DependencyMatching G) (D : HLS.WitnessDAG ι)
    (i : ι) :
    (arcNodes (matchingArcs M D)).filter (fun u => u.1 = i) ⊆
      (pairArcs M D i).image (labelEndpoint i) := by
  intro u hu
  obtain ⟨hu, hulabel⟩ := Finset.mem_filter.mp hu
  obtain ⟨e, he, hue⟩ := Finset.mem_biUnion.mp hu
  obtain ⟨hearc, hm, hl, hrev⟩ := Finset.mem_filter.mp he
  simp only [Finset.mem_insert, Finset.mem_singleton] at hue
  rcases hue with hue | hue
  · subst u
    have hepair : e ∈ pairArcs M D i := Finset.mem_filter.mpr
      ⟨Finset.mem_filter.mpr ⟨hearc, hm, hl, hrev⟩, congrArg M.pair hulabel⟩
    exact Finset.mem_image.mpr ⟨e, hepair, by simp [labelEndpoint, hulabel]⟩
  · subst u
    have hkey : M.pair e.1.1 = M.pair i := by
      calc
        M.pair e.1.1 = M.pair (M.mate e.1.1) := (M.pair_mate _).symm
        _ = M.pair i := congrArg M.pair (hm.trans hulabel)
    have hepair : e ∈ pairArcs M D i := Finset.mem_filter.mpr
      ⟨Finset.mem_filter.mpr ⟨hearc, hm, hl, hrev⟩, hkey⟩
    have hsource : e.1.1 ≠ i := by intro h; exact hl (h.trans hulabel.symm)
    exact Finset.mem_image.mpr ⟨e, hepair, by simp [labelEndpoint, hsource]⟩

theorem selected_endpoint_image_subset (M : DependencyMatching G) (D : HLS.WitnessDAG ι)
    (i : ι) :
    (selectedPairArcs M D i).image (labelEndpoint i) ⊆
      (arcNodes (selectedArcs M D)).filter (fun u => u.1 = i) := by
  intro u hu
  obtain ⟨e, he, heu⟩ := Finset.mem_image.mp hu
  subst u
  have heglobal : e ∈ selectedArcs M D :=
    Finset.mem_biUnion.mpr ⟨i, Finset.mem_univ i, he⟩
  exact Finset.mem_filter.mpr
    ⟨Finset.mem_biUnion.mpr ⟨e, heglobal, labelEndpoint_mem i e⟩,
      labelEndpoint_label M D i e (selectedPairArcs_subset M D i he)⟩

/-- Proposition 3.2: each label retains at least half its participating nodes. -/
theorem selectedArcs_half_incident_nodes (M : DependencyMatching G) (D : HLS.WitnessDAG ι)
    (hD : D.Valid G) (i : ι) :
    ((arcNodes (matchingArcs M D)).filter (fun u => u.1 = i)).card ≤
      2 * ((arcNodes (selectedArcs M D)).filter (fun u => u.1 = i)).card := by
  have horiginal : ((arcNodes (matchingArcs M D)).filter (fun u => u.1 = i)).card ≤
      (pairArcs M D i).card :=
    (Finset.card_le_card (incident_labelNodes_subset_image M D i)).trans (Finset.card_image_le)
  have hselected : (selectedPairArcs M D i).card ≤
      ((arcNodes (selectedArcs M D)).filter (fun u => u.1 = i)).card := by
    calc
      _ = ((selectedPairArcs M D i).image (labelEndpoint i)).card :=
        (Finset.card_image_of_injOn (selected_labelEndpoint_injective M D hD i)).symm
      _ ≤ _ := Finset.card_le_card (selected_endpoint_image_subset M D i)
  exact horiginal.trans ((selectedPairArcs_half M D i).trans (Nat.mul_le_mul_left 2 hselected))

end HLS.WitnessDAG

#check @HLS.WitnessDAG.mem_pairArcs_data
#check @HLS.WitnessDAG.pairArc_labels_mem
#check @HLS.WitnessDAG.pairArcs_eq_of_pair_eq
#check @HLS.WitnessDAG.selectedPairArcs_eq_of_pair_eq
#check @HLS.WitnessDAG.selectedPairArcs_subset
#check @HLS.WitnessDAG.selectedPairArcs_half
#check @HLS.WitnessDAG.selectedPairArcs_endpoints_disjoint
#check @HLS.WitnessDAG.selectedArcs_subset
#check @HLS.WitnessDAG.selectedArcs_endpoints_disjoint
#check @HLS.WitnessDAG.labelEndpoint_mem
#check @HLS.WitnessDAG.labelEndpoint_label
#check @HLS.WitnessDAG.selected_labelEndpoint_injective
#check @HLS.WitnessDAG.incident_labelNodes_subset_image
#check @HLS.WitnessDAG.selected_endpoint_image_subset
#check @HLS.WitnessDAG.selectedArcs_half_incident_nodes
