/- Recover each of the four local choices from the colored expanded DAG. -/
module

public import PPGraph.HLS.Encoding.OriginalIso
public import PPGraph.HLS.DAG.MatchingArcUniqueness

@[expose] public section

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option backward.isDefEq.respectTransparency false

open Classical

namespace HLS.WitnessDAG

variable {ι : Type} [Fintype ι] [DecidableEq ι] {G : SimpleGraph ι}

theorem expansion_extra_predecessor (M : DependencyMatching G) (D : HLS.WitnessDAG ι)
    (hD : D.Valid G) (choice : WNode ι → ExpansionChoice) (u : WNode ι) (hu : u ∈ D.nodes)
    (w : WNode ι) (hw : w ∈ expansionExtras M D hD choice)
    (he : (coloredExpansion M D hD choice).1.Edge w (expansionName M D hD choice (u, false)))
    (hr : Acyclic (reverseArc (coloredExpansion M D hD choice).1.Edge
      w (expansionName M D hD choice (u, false))))
    (hm : M.mate w.1 = u.1) :
    needsExtra (choice u) = true ∧ w = expansionName M D hD choice (u, true) := by
  obtain ⟨⟨v, b⟩, hv, hvw⟩ := Finset.mem_image.mp hw
  obtain ⟨hv, hb⟩ := Finset.mem_filter.mp hv
  change b = true at hb
  subst b
  have hv' := expandedNode_origin D choice (v, true) hv
  have hc := expandedNode_extra_choice D choice v hv
  have hep := (expansionName_edge_iff M D hD choice (v, true) (v, false) hv
    (expandedNode_original D choice v hv')).mpr (rawExpansion_extra_edge M D hD choice v hv' hc)
  have hrp := (normalize_reversible_iff G _ (rawExpansion_valid M D hD choice) _ _
    (rawExpansion_extra_edge M D hD choice v hv' hc)).mpr
      (rawExpansion_extra_reversible M D hD choice v hv' hc)
  have hm' : M.mate (expansionName M D hD choice (v, true)).1 =
      (expansionName M D hD choice (v, false)).1 := M.involutive v.1
  have he' := hvw.symm ▸ he
  have hr' := hvw.symm ▸ hr
  have hmuv : M.mate (expansionName M D hD choice (v, true)).1 =
      (expansionName M D hD choice (u, false)).1 := by
    change M.mate (expansionName M D hD choice (v, true)).1 = u.1
    rw [hvw]
    exact hm
  have htargets := reversible_matching_target_unique M _
    (normalize_valid G _ (rawExpansion_valid M D hD choice)) _ _ _ he' hep hr' hrp hmuv hm'
  have huv := expansionName_injective M D hD choice
    (expandedNode_original D choice u hu) (expandedNode_original D choice v hv') htargets
  have huv' : u = v := congrArg (fun x : ExpandedVertex ι => x.1) huv
  subst v
  exact ⟨hc, hvw.symm⟩

def InsertedBefore (M : DependencyMatching G) (D : HLS.WitnessDAG ι)
    (extras : Finset (WNode ι)) (u : WNode ι) (condition : WNode ι → Prop) : Prop :=
  ∃ w ∈ extras, condition w ∧ D.Edge w u ∧ Acyclic (reverseArc D.Edge w u) ∧ M.mate w.1 = u.1

theorem needsExtra_iff_insertedBefore (M : DependencyMatching G) (D : HLS.WitnessDAG ι)
    (hD : D.Valid G) (choice : WNode ι → ExpansionChoice) (u : WNode ι) (hu : u ∈ D.nodes) :
    needsExtra (choice u) = true ↔ InsertedBefore M (coloredExpansion M D hD choice).1
      (expansionExtras M D hD choice) (expansionName M D hD choice (u, false)) (fun _ => True) := by
  constructor
  · intro hc
    have hx := expandedNode_extra D choice u hu hc
    have he := rawExpansion_extra_edge M D hD choice u hu hc
    refine ⟨expansionName M D hD choice (u, true),
      (mem_expansionExtras_iff M D hD choice _ hx).mpr rfl, trivial,
      (expansionName_edge_iff M D hD choice _ _ hx (expandedNode_original D choice u hu)).mpr he,
      (normalize_reversible_iff G _ (rawExpansion_valid M D hD choice) _ _ he).mpr
        (rawExpansion_extra_reversible M D hD choice u hu hc), M.involutive u.1⟩
  · rintro ⟨w, hw, _, he, hr, hm⟩
    exact (expansion_extra_predecessor M D hD choice u hu w hw he hr hm).1

theorem insertDown_iff_insertedBefore (M : DependencyMatching G) (D : HLS.WitnessDAG ι)
    (hD : D.Valid G) (choice : WNode ι → ExpansionChoice) (u : WNode ι) (hu : u ∈ D.nodes) :
    choice u = .insertDown ↔ InsertedBefore M (coloredExpansion M D hD choice).1
      (expansionExtras M D hD choice) (expansionName M D hD choice (u, false))
      (fun w => w ∈ (coloredExpansion M D hD choice).2) := by
  constructor
  · intro hc
    have hExtra : needsExtra (choice u) = true := by rw [hc]; rfl
    obtain ⟨w, hw, _, he, hr, hm⟩ := (needsExtra_iff_insertedBefore M D hD choice u hu).mp hExtra
    have hname := (expansion_extra_predecessor M D hD choice u hu w hw he hr hm).2
    refine ⟨w, hw, ?_, he, hr, hm⟩
    dsimp only
    rw [hname, mem_expansionDown_iff M D hD choice _ (expandedNode_extra D choice u hu hExtra)]
    exact hc
  · rintro ⟨w, hw, hd, he, hr, hm⟩
    obtain ⟨hc, hname⟩ := expansion_extra_predecessor M D hD choice u hu w hw he hr hm
    rw [hname, mem_expansionDown_iff M D hD choice _ (expandedNode_extra D choice u hu hc)] at hd
    exact hd

theorem choices_eq_of_colored_eq (M : DependencyMatching G)
    (D E : HLS.WitnessDAG ι) (hD : D.Valid G) (hE : E.Valid G)
    (hcanonD : D.Canonical) (hcanonE : E.Canonical)
    (c d : WNode ι → ExpansionChoice) (hc : LegalExpansion M D c) (hd : LegalExpansion M E d)
    (heq : coloredExpansion M D hD c = coloredExpansion M E hE d)
    (u : WNode ι) (hu : u ∈ D.nodes) : c u = d u := by
  have hDE := original_eq_of_colored_eq M D E hD hE hcanonD hcanonE c d hc hd heq
  subst E
  have hn := congrArg Prod.fst heq
  have hR := congrArg Prod.snd heq
  have hX := expansionExtras_eq_of_colored_eq M D D hD hE c d hc hd heq
  have hname := original_names_eq_of_colored_eq M D D hD hE hcanonD hcanonE c d hc hd heq u hu
  have hextra : needsExtra (c u) = true ↔ needsExtra (d u) = true := by
    rw [needsExtra_iff_insertedBefore M D hD c u hu, needsExtra_iff_insertedBefore M D hE d u hu,
      hn, hX, hname]
  have hdownextra : c u = .insertDown ↔ d u = .insertDown := by
    rw [insertDown_iff_insertedBefore M D hD c u hu, insertDown_iff_insertedBefore M D hE d u hu,
      hn, hX, hname, hR]
  have hdown : originalDown c u ↔ originalDown d u := by
    change expandedDown c (u, false) ↔ expandedDown d (u, false)
    rw [← mem_expansionDown_iff M D hD c (u, false) (expandedNode_original D c u hu),
      ← mem_expansionDown_iff M D hE d (u, false) (expandedNode_original D d u hu)]
    rw [hname, hR]
  cases hcu : c u <;> cases hdu : d u <;>
    simp_all [needsExtra, originalDown]

end HLS.WitnessDAG

#check @HLS.WitnessDAG.expansion_extra_predecessor
#check @HLS.WitnessDAG.needsExtra_iff_insertedBefore
#check @HLS.WitnessDAG.insertDown_iff_insertedBefore
#check @HLS.WitnessDAG.choices_eq_of_colored_eq
