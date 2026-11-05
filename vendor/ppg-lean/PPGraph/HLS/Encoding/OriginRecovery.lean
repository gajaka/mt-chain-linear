/-
  Intrinsic recovery of original and inserted vertices (HLS Appendix C).
  The original/extra partition is uniquely determined by the colored DAG:
  an extra vertex has a reversible matching arc into a down-colored
  original vertex. Uniqueness follows by induction toward the sink.
-/
module

public import PPGraph.HLS.Encoding.ExpansionReversibility
public import PPGraph.HLS.DAG.MatchingSelection

@[expose] public section

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option backward.isDefEq.respectTransparency false

open Classical

namespace HLS.WitnessDAG

variable {ι : Type} [Fintype ι] [DecidableEq ι] {G : SimpleGraph ι}

def OriginRule (M : DependencyMatching G) (D : HLS.WitnessDAG ι)
    (down extra : WNode ι → Prop) : Prop :=
  ∀ u ∈ D.nodes, extra u ↔ ∃ v ∈ D.nodes,
    ¬ extra v ∧ down v ∧ D.Edge u v ∧ Acyclic (reverseArc D.Edge u v) ∧
      M.mate u.1 = v.1 ∧ u.1 ≠ v.1

theorem originRule_unique (M : DependencyMatching G) (D : HLS.WitnessDAG ι)
    (hD : D.Valid G) (down e₁ e₂ : WNode ι → Prop)
    (h₁ : OriginRule M D down e₁) (h₂ : OriginRule M D down e₂) :
    ∀ u ∈ D.nodes, e₁ u ↔ e₂ u := by
  intro u
  induction u using (outgoing_wellFounded G D hD).induction with
  | h u ih =>
    intro hu
    rw [h₁ u hu, h₂ u hu]
    constructor
    · rintro ⟨v, hv, hnot, hd, he, hr, hm, hl⟩
      exact ⟨v, hv, (ih v he hv).not.mp hnot, hd, he, hr, hm, hl⟩
    · rintro ⟨v, hv, hnot, hd, he, hr, hm, hl⟩
      exact ⟨v, hv, (ih v he hv).not.mpr hnot, hd, he, hr, hm, hl⟩

def originalDown (choice : WNode ι → ExpansionChoice) (u : WNode ι) : Prop :=
  choice u ≠ .up

def expandedDown (choice : WNode ι → ExpansionChoice) (x : ExpandedVertex ι) : Prop :=
  if x.2 then choice x.1 = .insertDown else originalDown choice x.1

def LegalExpansion (M : DependencyMatching G) (D : HLS.WitnessDAG ι)
    (choice : WNode ι → ExpansionChoice) : Prop :=
  (∀ u ∈ arcNodes (matchingArcs M D), choice u = .up) ∧
    (∀ u ∈ D.nodes, M.mate u.1 = u.1 → choice u = .up)

theorem expandedNode_extra_choice (D : HLS.WitnessDAG ι)
    (choice : WNode ι → ExpansionChoice) (u : WNode ι)
    (hu : (u, true) ∈ expandedNodes D choice) : needsExtra (choice u) = true := by
  rcases Finset.mem_union.mp hu with h | h
  · obtain ⟨w, _, hw⟩ := Finset.mem_image.mp h
    have hb : false = true := congrArg Prod.snd hw
    cases hb
  · obtain ⟨w, hw, hwu⟩ := Finset.mem_image.mp h
    have hwu' : w = u := congrArg Prod.fst hwu
    exact hwu' ▸ (Finset.mem_filter.mp hw).2

theorem needsExtra_implies_down (choice : WNode ι → ExpansionChoice) (u : WNode ι)
    (h : needsExtra (choice u) = true) : originalDown choice u := by
  intro hn
  rw [hn] at h
  cases h

theorem legal_original_down_not_reversible (M : DependencyMatching G)
    (D : HLS.WitnessDAG ι) (choice : WNode ι → ExpansionChoice)
    (hlegal : LegalExpansion M D choice) (u v : WNode ι)
    (he : D.Edge u v) (hm : M.mate u.1 = v.1) (hl : u.1 ≠ v.1)
    (hd : originalDown choice v) : ¬ Acyclic (reverseArc D.Edge u v) := by
  intro hr
  have hmem : v ∈ arcNodes (matchingArcs M D) :=
    Finset.mem_biUnion.mpr ⟨(u, v), Finset.mem_filter.mpr ⟨he, hm, hl, hr⟩, by simp⟩
  exact hd (hlegal.1 v hmem)

theorem rawExpansion_origin_rule_at (M : DependencyMatching G) (D : HLS.WitnessDAG ι)
    (hD : D.Valid G) (choice : WNode ι → ExpansionChoice)
    (hlegal : LegalExpansion M D choice) (x : ExpandedVertex ι)
    (hx : x ∈ expandedNodes D choice) :
    x.2 = true ↔ ∃ y ∈ expandedNodes D choice,
      y.2 = false ∧ expandedDown choice y ∧
      (rawExpansion M D hD choice).Edge (expansionEmbed M x) (expansionEmbed M y) ∧
      Acyclic (reverseArc (rawExpansion M D hD choice).Edge
        (expansionEmbed M x) (expansionEmbed M y)) ∧
      M.mate (expandedLabel M x) = expandedLabel M y ∧
        expandedLabel M x ≠ expandedLabel M y := by
  obtain ⟨u, b⟩ := x
  cases b with
  | true =>
    have hu := expandedNode_origin D choice (u, true) hx
    have hc := expandedNode_extra_choice D choice u hx
    have hd := needsExtra_implies_down choice u hc
    have hm : M.mate u.1 ≠ u.1 := by
      intro hm
      exact hd (hlegal.2 u hu hm)
    constructor
    · intro _
      refine ⟨(u, false), expandedNode_original D choice u hu, rfl, hd,
        rawExpansion_extra_edge M D hD choice u hu hc,
        rawExpansion_extra_reversible M D hD choice u hu hc, ?_, ?_⟩
      · simpa [expandedLabel] using M.involutive u.1
      · simpa [expandedLabel] using hm
    · intro _; rfl
  | false =>
    constructor
    · intro h; cases h
    · rintro ⟨⟨v, c⟩, hv, hc, hd, he, hr, hm, hl⟩
      change c = false at hc
      subst c
      have hu := expandedNode_origin D choice (u, false) hx
      have hv' := expandedNode_origin D choice (v, false) hv
      have he' := (rawExpansion_original_edge_iff M D hD choice u v hu hv').mp he
      have hm' : M.mate u.1 = v.1 := by simpa [expandedLabel] using hm
      have hl' : u.1 ≠ v.1 := by simpa [expandedLabel] using hl
      have hd' : originalDown choice v := hd
      exact False.elim ((original_nonreversible_persists M D hD choice u v he'
        (legal_original_down_not_reversible M D choice hlegal u v he' hm' hl' hd')) hr)

end HLS.WitnessDAG

#check @HLS.WitnessDAG.originRule_unique
#check @HLS.WitnessDAG.expandedNode_extra_choice
#check @HLS.WitnessDAG.needsExtra_implies_down
#check @HLS.WitnessDAG.legal_original_down_not_reversible
#check @HLS.WitnessDAG.rawExpansion_origin_rule_at
