/- The colored expanded graph determines the original canonical DAG. -/
module

public import PPGraph.HLS.Encoding.ColoredExpansion
public import PPGraph.HLS.Encoding.NodeIso

@[expose] public section

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option backward.isDefEq.respectTransparency false

open Classical

namespace HLS.WitnessDAG

variable {ι : Type} [Fintype ι] [DecidableEq ι] {G : SimpleGraph ι}

theorem original_name_exists_of_colored_eq (M : DependencyMatching G)
    (D E : HLS.WitnessDAG ι) (hD : D.Valid G) (hE : E.Valid G)
    (c d : WNode ι → ExpansionChoice) (hc : LegalExpansion M D c) (hd : LegalExpansion M E d)
    (heq : coloredExpansion M D hD c = coloredExpansion M E hE d)
    (u : WNode ι) (hu : u ∈ D.nodes) :
    ∃ v ∈ E.nodes, expansionName M E hE d (v, false) = expansionName M D hD c (u, false) := by
  have hn := congrArg Prod.fst heq
  have hx := expansionName_mem M D hD c (u, false) (expandedNode_original D c u hu)
  rw [hn] at hx
  obtain ⟨⟨v, b⟩, hv, hname⟩ := (coloredExpansion_node_iff M E hE d _).mp hx
  have hb : b = false := by
    have hnot : expansionName M D hD c (u, false) ∉ expansionExtras M D hD c := by
      rw [mem_expansionExtras_iff M D hD c _ (expandedNode_original D c u hu)]
      simp
    rw [expansionExtras_eq_of_colored_eq M D E hD hE c d hc hd heq, ← hname,
      mem_expansionExtras_iff M E hE d (v, b) hv] at hnot
    cases h : b <;> simp_all
  subst b
  exact ⟨v, expandedNode_origin E d (v, false) hv, hname⟩

noncomputable def originalIsoMap (M : DependencyMatching G)
    (D E : HLS.WitnessDAG ι) (hD : D.Valid G) (hE : E.Valid G)
    (c d : WNode ι → ExpansionChoice) (u : WNode ι) : WNode ι :=
  if h : ∃ v ∈ E.nodes,
    expansionName M E hE d (v, false) = expansionName M D hD c (u, false)
  then h.choose else u

theorem originalIsoMap_spec (M : DependencyMatching G)
    (D E : HLS.WitnessDAG ι) (hD : D.Valid G) (hE : E.Valid G)
    (c d : WNode ι → ExpansionChoice) (hc : LegalExpansion M D c) (hd : LegalExpansion M E d)
    (heq : coloredExpansion M D hD c = coloredExpansion M E hE d)
    (u : WNode ι) (hu : u ∈ D.nodes) :
    originalIsoMap M D E hD hE c d u ∈ E.nodes ∧
    expansionName M E hE d (originalIsoMap M D E hD hE c d u, false) =
      expansionName M D hD c (u, false) := by
  have h := original_name_exists_of_colored_eq M D E hD hE c d hc hd heq u hu
  simp only [originalIsoMap, dite_eq_left h]
  exact h.choose_spec

noncomputable def originalIso_of_colored_eq (M : DependencyMatching G)
    (D E : HLS.WitnessDAG ι) (hD : D.Valid G) (hE : E.Valid G)
    (c d : WNode ι → ExpansionChoice) (hc : LegalExpansion M D c) (hd : LegalExpansion M E d)
    (heq : coloredExpansion M D hD c = coloredExpansion M E hE d) : NodeIso D E := by
  let f := originalIsoMap M D E hD hE c d
  have hspec := originalIsoMap_spec M D E hD hE c d hc hd heq
  have hinj : Set.InjOn f (↑D.nodes : Set (WNode ι)) := by
    intro u hu v hv he
    have hnames := (hspec u hu).2.symm.trans ((congrArg
      (fun z => expansionName M E hE d (z, false)) he).trans (hspec v hv).2)
    have hpair := expansionName_injective M D hD c
      (expandedNode_original D c u hu) (expandedNode_original D c v hv) hnames
    exact congrArg (fun z : ExpandedVertex ι => z.1) hpair
  refine ⟨f, hinj, ?_, ?_, ?_⟩
  · ext v
    constructor
    · intro hv
      obtain ⟨u, hu, rfl⟩ := Finset.mem_image.mp hv
      exact (hspec u hu).1
    · intro hv
      obtain ⟨u, hu, hname⟩ := original_name_exists_of_colored_eq M E D hE hD d c hd hc heq.symm v hv
      have hpair := expansionName_injective M E hE d
        (expandedNode_original E d (f u) (hspec u hu).1) (expandedNode_original E d v hv)
        ((hspec u hu).2.trans hname)
      exact Finset.mem_image.mpr ⟨u, hu, congrArg (fun z : ExpandedVertex ι => z.1) hpair⟩
  · intro u hu
    have hl := congrArg (fun z : WNode ι => z.1) (hspec u hu).2
    exact hl
  · intro u hu v hv
    have hn := congrArg Prod.fst heq
    have hmapu := (hspec u hu).2
    have hmapv := (hspec v hv).2
    rw [← rawExpansion_original_edge_iff M E hE d (f u) (f v) (hspec u hu).1 (hspec v hv).1,
      ← expansionName_edge_iff M E hE d _ _
        (expandedNode_original E d (f u) (hspec u hu).1)
        (expandedNode_original E d (f v) (hspec v hv).1),
      hmapu, hmapv, ← hn,
      expansionName_edge_iff M D hD c _ _ (expandedNode_original D c u hu) (expandedNode_original D c v hv),
      rawExpansion_original_edge_iff M D hD c u v hu hv]

theorem original_eq_of_colored_eq (M : DependencyMatching G)
    (D E : HLS.WitnessDAG ι) (hD : D.Valid G) (hE : E.Valid G)
    (hcanonD : D.Canonical) (hcanonE : E.Canonical)
    (c d : WNode ι → ExpansionChoice) (hc : LegalExpansion M D c) (hd : LegalExpansion M E d)
    (heq : coloredExpansion M D hD c = coloredExpansion M E hE d) : D = E :=
  (originalIso_of_colored_eq M D E hD hE c d hc hd heq).eq_of_canonical G hD hE hcanonD hcanonE

theorem original_names_eq_of_colored_eq (M : DependencyMatching G)
    (D E : HLS.WitnessDAG ι) (hD : D.Valid G) (hE : E.Valid G)
    (hcanonD : D.Canonical) (hcanonE : E.Canonical)
    (c d : WNode ι → ExpansionChoice) (hc : LegalExpansion M D c) (hd : LegalExpansion M E d)
    (heq : coloredExpansion M D hD c = coloredExpansion M E hE d)
    (u : WNode ι) (hu : u ∈ D.nodes) :
    expansionName M D hD c (u, false) = expansionName M E hE d (u, false) := by
  have hm := (originalIso_of_colored_eq M D E hD hE c d hc hd heq).map_eq_of_canonical
    G hD hE hcanonD hcanonE u hu
  have hs := (originalIsoMap_spec M D E hD hE c d hc hd heq u hu).2
  change originalIsoMap M D E hD hE c d u = u at hm
  rw [hm] at hs
  exact hs.symm

end HLS.WitnessDAG

#check @HLS.WitnessDAG.original_name_exists_of_colored_eq
#check @HLS.WitnessDAG.originalIsoMap_spec
#check @HLS.WitnessDAG.original_eq_of_colored_eq
#check @HLS.WitnessDAG.original_names_eq_of_colored_eq
