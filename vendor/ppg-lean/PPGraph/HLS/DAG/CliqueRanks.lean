/-
  Predecessor ranks in a clique of labels. For a matching pair this is
  the auxiliary-table index lambda in He--Li--Sun, Section 3.1.
-/
module

public import PPGraph.HLS.Encoding.Normalization
public import PPGraph.HLS.DAG.Matching

@[expose] public section

set_option autoImplicit false
set_option linter.unusedSectionVars false

open Classical

namespace HLS.WitnessDAG

variable {ι : Type} [DecidableEq ι]

def LabelClique (G : SimpleGraph ι) (J : Finset ι) : Prop :=
  ∀ i ∈ J, ∀ j ∈ J, i = j ∨ G.Adj i j

noncomputable def cliquePrior (D : HLS.WitnessDAG ι) (J : Finset ι) (u : WNode ι) :
    Finset (WNode ι) := D.nodes.filter (fun w => w.1 ∈ J ∧ D.Edge w u)

noncomputable def cliqueRank (D : HLS.WitnessDAG ι) (J : Finset ι) (u : WNode ι) : ℕ :=
  (D.cliquePrior J u).card

theorem cliquePrior_subset_of_edge (G : SimpleGraph ι) (D : HLS.WitnessDAG ι)
    (hD : D.Valid G) (J : Finset ι) (hJ : LabelClique G J) (u v : WNode ι)
    (he : D.Edge u v) (hv : v.1 ∈ J) : D.cliquePrior J u ⊆ D.cliquePrior J v := by
  intro w hw
  obtain ⟨hw, hwJ, hwu⟩ := Finset.mem_filter.mp hw
  exact Finset.mem_filter.mpr ⟨hw, hwJ, edge_of_transGen_dependent G D hD w v
    ((Relation.TransGen.single hwu).tail he) (hJ _ hwJ _ hv)⟩

theorem cliqueRank_lt_of_edge (G : SimpleGraph ι) (D : HLS.WitnessDAG ι)
    (hD : D.Valid G) (J : Finset ι) (hJ : LabelClique G J) (u v : WNode ι)
    (he : D.Edge u v) (hu : u.1 ∈ J) (hv : v.1 ∈ J) :
    D.cliqueRank J u < D.cliqueRank J v := by
  apply Finset.card_lt_card
  apply lt_of_le_of_ne (cliquePrior_subset_of_edge G D hD J hJ u v he hv)
  intro heq
  have huin : u ∈ D.cliquePrior J v :=
    Finset.mem_filter.mpr ⟨(hD.supported _ _ he).1, hu, he⟩
  exact hD.acyclic.irrefl _ u (Finset.mem_filter.mp (heq.symm ▸ huin)).2.2

theorem cliqueRank_lt_card (G : SimpleGraph ι) (D : HLS.WitnessDAG ι)
    (hD : D.Valid G) (J : Finset ι) (u : WNode ι) (hu : u ∈ D.nodes) :
    D.cliqueRank J u < D.nodes.card := by
  apply Finset.card_lt_card
  apply lt_of_le_of_ne (Finset.filter_subset _ _)
  intro heq
  have hself := (Finset.mem_filter.mp (heq.symm ▸ hu)).2.2
  exact hD.acyclic.irrefl _ u hself

theorem eq_of_cliqueRank_eq (G : SimpleGraph ι) (D : HLS.WitnessDAG ι)
    (hD : D.Valid G) (J : Finset ι) (hJ : LabelClique G J) (u v : WNode ι)
    (hu : u ∈ D.nodes) (hv : v ∈ D.nodes) (huJ : u.1 ∈ J) (hvJ : v.1 ∈ J)
    (h : D.cliqueRank J u = D.cliqueRank J v) : u = v := by
  by_contra hne
  rcases (hD.oriented u hu v hv hne).mpr (hJ _ huJ _ hvJ) with he | he
  · have hlt := cliqueRank_lt_of_edge G D hD J hJ u v he huJ hvJ
    omega
  · have hlt := cliqueRank_lt_of_edge G D hD J hJ v u he hvJ huJ
    omega

theorem cliquePrior_reversible_eq_insert (G : SimpleGraph ι) (D : HLS.WitnessDAG ι)
    (hD : D.Valid G) (J : Finset ι) (hJ : LabelClique G J) (u v : WNode ι)
    (he : D.Edge u v) (hrev : Acyclic (reverseArc D.Edge u v))
    (hu : u.1 ∈ J) (hv : v.1 ∈ J) :
    D.cliquePrior J v = insert u (D.cliquePrior J u) := by
  have hno := (reversible_iff_no_alternate_path D.Edge u v hD.acyclic he).mp hrev
  ext w
  constructor
  · intro hw
    obtain ⟨hw, hwJ, hwv⟩ := Finset.mem_filter.mp hw
    by_cases hwu : w = u
    · exact Finset.mem_insert.mpr (Or.inl hwu)
    rcases (hD.oriented w hw u (hD.supported _ _ he).1 hwu).mpr (hJ _ hwJ _ hu) with h | h
    · exact Finset.mem_insert_of_mem (Finset.mem_filter.mpr ⟨hw, hwJ, h⟩)
    · have hwne : w ≠ v := edge_ne G D hD w v hwv
      have h₁ : eraseArc D.Edge u v u w := ⟨h, by simpa using hwne⟩
      have h₂ : eraseArc D.Edge u v w v := ⟨hwv, by simpa using hwu⟩
      exact False.elim (hno ((Relation.TransGen.single h₁).tail h₂))
  · intro hw
    rcases Finset.mem_insert.mp hw with hwu | hw
    · subst w
      exact Finset.mem_filter.mpr ⟨(hD.supported _ _ he).1, hu, he⟩
    · exact cliquePrior_subset_of_edge G D hD J hJ u v he hv hw

theorem cliqueRank_reversible_consecutive (G : SimpleGraph ι) (D : HLS.WitnessDAG ι)
    (hD : D.Valid G) (J : Finset ι) (hJ : LabelClique G J) (u v : WNode ι)
    (he : D.Edge u v) (hrev : Acyclic (reverseArc D.Edge u v))
    (hu : u.1 ∈ J) (hv : v.1 ∈ J) : D.cliqueRank J v = D.cliqueRank J u + 1 := by
  have hnot : u ∉ D.cliquePrior J u := fun h =>
    hD.acyclic.irrefl _ u (Finset.mem_filter.mp h).2.2
  rw [cliqueRank, cliquePrior_reversible_eq_insert G D hD J hJ u v he hrev hu hv,
    Finset.card_insert_of_notMem hnot]
  rfl

theorem cliquePrior_reverse_other (D : HLS.WitnessDAG ι) (J : Finset ι)
    (u v w : WNode ι) (hwu : w ≠ u) (hwv : w ≠ v) :
    (D.reverse u v).cliquePrior J w = D.cliquePrior J w := by
  ext z
  simp only [cliquePrior, Finset.mem_filter, reverse_edge_iff, reverseArc, addArc, eraseArc]
  simp [reverse, hwu, hwv]

theorem cliquePrior_reverse_source (G : SimpleGraph ι) (D : HLS.WitnessDAG ι)
    (hD : D.Valid G) (J : Finset ι) (u v : WNode ι) (he : D.Edge u v) (hvJ : v.1 ∈ J) :
    (D.reverse u v).cliquePrior J u = insert v (D.cliquePrior J u) := by
  have hne := edge_ne G D hD u v he
  have hv := (hD.supported _ _ he).2
  ext z
  simp only [cliquePrior, Finset.mem_filter, Finset.mem_insert, reverse_edge_iff,
    reverseArc, addArc, eraseArc]
  simp only [reverse]
  constructor
  · rintro ⟨hz, hzJ, (⟨h, _⟩ | ⟨rfl, _⟩)⟩
    · exact Or.inr ⟨hz, hzJ, h⟩
    · exact Or.inl rfl
  · rintro (rfl | ⟨hz, hzJ, h⟩)
    · exact ⟨hv, hvJ, Or.inr ⟨rfl, trivial⟩⟩
    · exact ⟨hz, hzJ, Or.inl ⟨h, by simp [hne]⟩⟩

theorem cliquePrior_reverse_target (G : SimpleGraph ι) (D : HLS.WitnessDAG ι)
    (hD : D.Valid G) (J : Finset ι) (u v : WNode ι) (he : D.Edge u v) :
    (D.reverse u v).cliquePrior J v = (D.cliquePrior J v).erase u := by
  have hne := edge_ne G D hD u v he
  ext z
  simp only [cliquePrior, Finset.mem_filter, Finset.mem_erase, reverse_edge_iff,
    reverseArc, addArc, eraseArc]
  simp only [reverse, Ne.symm hne, and_false, or_false, and_true]
  tauto

theorem cliqueRank_reverse_source (G : SimpleGraph ι) (D : HLS.WitnessDAG ι)
    (hD : D.Valid G) (J : Finset ι) (hJ : LabelClique G J) (u v : WNode ι)
    (he : D.Edge u v) (hrev : Acyclic (reverseArc D.Edge u v))
    (hu : u.1 ∈ J) (hv : v.1 ∈ J) :
    (D.reverse u v).cliqueRank J u = D.cliqueRank J v := by
  have hnot : v ∉ D.cliquePrior J u := fun h =>
    hD.acyclic.asymm _ u v he (Finset.mem_filter.mp h).2.2
  rw [cliqueRank, cliquePrior_reverse_source G D hD J u v he hv,
    Finset.card_insert_of_notMem hnot]
  exact (cliqueRank_reversible_consecutive G D hD J hJ u v he hrev hu hv).symm

theorem cliqueRank_reverse_target (G : SimpleGraph ι) (D : HLS.WitnessDAG ι)
    (hD : D.Valid G) (J : Finset ι) (hJ : LabelClique G J) (u v : WNode ι)
    (he : D.Edge u v) (hrev : Acyclic (reverseArc D.Edge u v))
    (hu : u.1 ∈ J) (hv : v.1 ∈ J) :
    (D.reverse u v).cliqueRank J v = D.cliqueRank J u := by
  rw [cliqueRank, cliquePrior_reverse_target G D hD J u v he,
    cliquePrior_reversible_eq_insert G D hD J hJ u v he hrev hu hv]
  have hnot : u ∉ D.cliquePrior J u := fun h =>
    hD.acyclic.irrefl _ u (Finset.mem_filter.mp h).2.2
  rw [Finset.erase_insert hnot]
  rfl

theorem cliquePrior_prefix_eq (D : HLS.WitnessDAG ι) (J : Finset ι)
    (r u : WNode ι) (hur : D.Reach u r) :
    (D.ancestorPrefix r).cliquePrior J u = D.cliquePrior J u := by
  ext w
  simp only [cliquePrior, Finset.mem_filter, prefix_node_iff, prefix_edge_iff]
  constructor
  · rintro ⟨⟨hw, _⟩, hwJ, hwu, _⟩
    exact ⟨hw, hwJ, hwu⟩
  · rintro ⟨hw, hwJ, hwu⟩
    exact ⟨⟨hw, hur.head hwu⟩, hwJ, hwu, hur⟩

end HLS.WitnessDAG

#check @HLS.WitnessDAG.cliquePrior_subset_of_edge
#check @HLS.WitnessDAG.cliqueRank_lt_of_edge
#check @HLS.WitnessDAG.cliqueRank_lt_card
#check @HLS.WitnessDAG.eq_of_cliqueRank_eq
#check @HLS.WitnessDAG.cliquePrior_reversible_eq_insert
#check @HLS.WitnessDAG.cliqueRank_reversible_consecutive
#check @HLS.WitnessDAG.cliquePrior_reverse_other
#check @HLS.WitnessDAG.cliquePrior_reverse_source
#check @HLS.WitnessDAG.cliquePrior_reverse_target
#check @HLS.WitnessDAG.cliqueRank_reverse_source
#check @HLS.WitnessDAG.cliqueRank_reverse_target
#check @HLS.WitnessDAG.cliquePrior_prefix_eq
