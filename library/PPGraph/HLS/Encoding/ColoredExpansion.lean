/- Canonical colored expansion and intrinsic recovery of inserted vertices. -/
module

public import PPGraph.HLS.Encoding.OriginRecovery
public import PPGraph.HLS.Encoding.NormalizationReversal

@[expose] public section

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option backward.isDefEq.respectTransparency false

open Classical

namespace HLS.WitnessDAG

variable {ι : Type} [Fintype ι] [DecidableEq ι] {G : SimpleGraph ι}

noncomputable def expansionName (M : DependencyMatching G) (D : HLS.WitnessDAG ι)
    (hD : D.Valid G) (choice : WNode ι → ExpansionChoice) (x : ExpandedVertex ι) : WNode ι :=
  (rawExpansion M D hD choice).canonicalName (expansionEmbed M x)

noncomputable def coloredExpansion (M : DependencyMatching G) (D : HLS.WitnessDAG ι)
    (hD : D.Valid G) (choice : WNode ι → ExpansionChoice) : HLS.WitnessDAG ι × Finset (WNode ι) :=
  ((rawExpansion M D hD choice).normalize,
    ((expandedNodes D choice).filter (expandedDown choice)).image (expansionName M D hD choice))

noncomputable def expansionExtras (M : DependencyMatching G) (D : HLS.WitnessDAG ι)
    (hD : D.Valid G) (choice : WNode ι → ExpansionChoice) : Finset (WNode ι) :=
  ((expandedNodes D choice).filter (fun x => x.2 = true)).image (expansionName M D hD choice)

theorem expansionName_mem (M : DependencyMatching G) (D : HLS.WitnessDAG ι)
    (hD : D.Valid G) (choice : WNode ι → ExpansionChoice) (x : ExpandedVertex ι)
    (hx : x ∈ expandedNodes D choice) :
    expansionName M D hD choice x ∈ (coloredExpansion M D hD choice).1.nodes := by
  exact Finset.mem_image.mpr ⟨expansionEmbed M x,
    Finset.mem_image.mpr ⟨x, hx, rfl⟩, rfl⟩

theorem expansionName_injective (M : DependencyMatching G) (D : HLS.WitnessDAG ι)
    (hD : D.Valid G) (choice : WNode ι → ExpansionChoice) :
    Set.InjOn (expansionName M D hD choice) (↑(expandedNodes D choice) : Set (ExpandedVertex ι)) := by
  intro x hx y hy h
  apply expansionEmbed_injective M
  exact canonicalName_injective G _ (rawExpansion_valid M D hD choice)
    (Finset.mem_image.mpr ⟨x, hx, rfl⟩) (Finset.mem_image.mpr ⟨y, hy, rfl⟩) h

theorem coloredExpansion_node_iff (M : DependencyMatching G) (D : HLS.WitnessDAG ι)
    (hD : D.Valid G) (choice : WNode ι → ExpansionChoice) (w : WNode ι) :
    w ∈ (coloredExpansion M D hD choice).1.nodes ↔
      ∃ x ∈ expandedNodes D choice, expansionName M D hD choice x = w := by
  change w ∈ ((expandedNodes D choice).image (expansionEmbed M)).image
    (rawExpansion M D hD choice).canonicalName ↔ _
  rw [Finset.image_image]
  exact Finset.mem_image

theorem mem_expansionDown_iff (M : DependencyMatching G) (D : HLS.WitnessDAG ι)
    (hD : D.Valid G) (choice : WNode ι → ExpansionChoice) (x : ExpandedVertex ι)
    (hx : x ∈ expandedNodes D choice) :
    expansionName M D hD choice x ∈ (coloredExpansion M D hD choice).2 ↔ expandedDown choice x := by
  constructor
  · intro h
    obtain ⟨y, hy, heq⟩ := Finset.mem_image.mp h
    obtain ⟨hy, hd⟩ := Finset.mem_filter.mp hy
    exact expansionName_injective M D hD choice hy hx heq ▸ hd
  · intro h
    exact Finset.mem_image.mpr ⟨x, Finset.mem_filter.mpr ⟨hx, h⟩, rfl⟩

theorem mem_expansionExtras_iff (M : DependencyMatching G) (D : HLS.WitnessDAG ι)
    (hD : D.Valid G) (choice : WNode ι → ExpansionChoice) (x : ExpandedVertex ι)
    (hx : x ∈ expandedNodes D choice) :
    expansionName M D hD choice x ∈ expansionExtras M D hD choice ↔ x.2 = true := by
  constructor
  · intro h
    obtain ⟨y, hy, heq⟩ := Finset.mem_image.mp h
    obtain ⟨hy, hb⟩ := Finset.mem_filter.mp hy
    exact expansionName_injective M D hD choice hy hx heq ▸ hb
  · intro h
    exact Finset.mem_image.mpr ⟨x, Finset.mem_filter.mpr ⟨hx, h⟩, rfl⟩

theorem expansionName_edge_iff (M : DependencyMatching G) (D : HLS.WitnessDAG ι)
    (hD : D.Valid G) (choice : WNode ι → ExpansionChoice) (x y : ExpandedVertex ι)
    (hx : x ∈ expandedNodes D choice) (hy : y ∈ expandedNodes D choice) :
    (coloredExpansion M D hD choice).1.Edge (expansionName M D hD choice x)
      (expansionName M D hD choice y) ↔
    (rawExpansion M D hD choice).Edge (expansionEmbed M x) (expansionEmbed M y) :=
  normalize_edge_iff G _ (rawExpansion_valid M D hD choice) _ _
    (Finset.mem_image.mpr ⟨x, hx, rfl⟩) (Finset.mem_image.mpr ⟨y, hy, rfl⟩)

theorem coloredExpansion_originRule (M : DependencyMatching G) (D : HLS.WitnessDAG ι)
    (hD : D.Valid G) (choice : WNode ι → ExpansionChoice)
    (hlegal : LegalExpansion M D choice) :
    OriginRule M (coloredExpansion M D hD choice).1
      (fun w => w ∈ (coloredExpansion M D hD choice).2)
      (fun w => w ∈ expansionExtras M D hD choice) := by
  intro w hw
  obtain ⟨x, hx, rfl⟩ := (coloredExpansion_node_iff M D hD choice w).mp hw
  dsimp only
  rw [mem_expansionExtras_iff M D hD choice x hx, rawExpansion_origin_rule_at M D hD choice hlegal x hx]
  constructor
  · rintro ⟨y, hy, hb, hd, he, hr, hm, hl⟩
    refine ⟨expansionName M D hD choice y, expansionName_mem M D hD choice y hy, ?_,
      (mem_expansionDown_iff M D hD choice y hy).mpr hd,
      (expansionName_edge_iff M D hD choice x y hx hy).mpr he, ?_, hm, hl⟩
    · rw [mem_expansionExtras_iff M D hD choice y hy, hb]
      simp
    · exact (normalize_reversible_iff G _ (rawExpansion_valid M D hD choice) _ _ he).mpr hr
  · rintro ⟨w, hw, hn, hd, he, hr, hm, hl⟩
    obtain ⟨y, hy, rfl⟩ := (coloredExpansion_node_iff M D hD choice w).mp hw
    have hb : y.2 = false := by
      have hnot := (mem_expansionExtras_iff M D hD choice y hy).not.mp hn
      cases h : y.2 <;> simp_all
    have he' := (expansionName_edge_iff M D hD choice x y hx hy).mp he
    exact ⟨y, hy, hb, (mem_expansionDown_iff M D hD choice y hy).mp hd, he',
      (normalize_reversible_iff G _ (rawExpansion_valid M D hD choice) _ _ he').mp hr, hm, hl⟩

theorem expansionExtras_eq_of_colored_eq (M : DependencyMatching G)
    (D E : HLS.WitnessDAG ι) (hD : D.Valid G) (hE : E.Valid G)
    (c d : WNode ι → ExpansionChoice) (hc : LegalExpansion M D c) (hd : LegalExpansion M E d)
    (heq : coloredExpansion M D hD c = coloredExpansion M E hE d) :
    expansionExtras M D hD c = expansionExtras M E hE d := by
  have hn := congrArg Prod.fst heq
  have hr := congrArg Prod.snd heq
  have h₁ := coloredExpansion_originRule M D hD c hc
  have h₂ := coloredExpansion_originRule M E hE d hd
  rw [← hn, ← hr] at h₂
  have hsame := originRule_unique M _ (normalize_valid G _ (rawExpansion_valid M D hD c)) _ _ _ h₁ h₂
  ext w
  by_cases hw : w ∈ (coloredExpansion M D hD c).1.nodes
  · exact hsame w hw
  · have hleft : w ∉ expansionExtras M D hD c := by
      intro h
      obtain ⟨x, hx, rfl⟩ := Finset.mem_image.mp h
      exact hw (expansionName_mem M D hD c x (Finset.mem_filter.mp hx).1)
    have hright : w ∉ expansionExtras M E hE d := by
      intro h
      obtain ⟨x, hx, rfl⟩ := Finset.mem_image.mp h
      exact hw (hn.symm ▸ expansionName_mem M E hE d x (Finset.mem_filter.mp hx).1)
    simp only [hleft, hright]

end HLS.WitnessDAG

#check @HLS.WitnessDAG.expansionName_mem
#check @HLS.WitnessDAG.expansionName_injective
#check @HLS.WitnessDAG.coloredExpansion_node_iff
#check @HLS.WitnessDAG.mem_expansionDown_iff
#check @HLS.WitnessDAG.mem_expansionExtras_iff
#check @HLS.WitnessDAG.expansionName_edge_iff
#check @HLS.WitnessDAG.coloredExpansion_originRule
#check @HLS.WitnessDAG.expansionExtras_eq_of_colored_eq
