/- An injective map from legal four-choice expansions to colored proper DAGs. -/
module

public import PPGraph.HLS.Encoding.ChoiceRecovery
public import PPGraph.HLS.Bounds.DecoratedBudget

@[expose] public section

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option backward.isDefEq.respectTransparency false

open Classical

namespace HLS.WitnessDAG

variable {ι : Type} [Fintype ι] [DecidableEq ι] {G : SimpleGraph ι}

noncomputable def extendChoice (D : HLS.WitnessDAG ι)
    (c : ↥D.nodes → ExpansionChoice) (u : WNode ι) : ExpansionChoice :=
  if h : u ∈ D.nodes then c ⟨u, h⟩ else .up

theorem extendChoice_mem (D : HLS.WitnessDAG ι) (c : ↥D.nodes → ExpansionChoice)
    (u : WNode ι) (hu : u ∈ D.nodes) : extendChoice D c u = c ⟨u, hu⟩ := by
  simp only [extendChoice, dite_eq_left hu]

abbrev LegalChoices (M : DependencyMatching G) (D : HLS.WitnessDAG ι) :=
  {c : ↥D.nodes → ExpansionChoice // LegalExpansion M D (extendChoice D c)}

abbrev ExpansionFamily (M : DependencyMatching G) (α : ι) :=
  Σ D : ProperFamily G Finset.univ α, LegalChoices M D.val

theorem coloredExpansion_isProperCanonical (M : DependencyMatching G)
    (α : ι) (D : ProperFamily G Finset.univ α) (c : LegalChoices M D.val) :
    IsProperCanonical G Finset.univ α (coloredExpansion M D.val D.property.1 (extendChoice D.val c.val)).1 := by
  let choice := extendChoice D.val c.val
  refine ⟨normalize_valid G _ (rawExpansion_valid M D.val D.property.1 choice),
    normalize_canonical G _ (rawExpansion_valid M D.val D.property.1 choice),
    (fun _ _ => Finset.mem_univ _), ?_⟩
  obtain ⟨r, hr, hlabel, hroot⟩ := D.property.2.2.2
  refine ⟨expansionName M D.val D.property.1 choice (r, false),
    expansionName_mem M D.val D.property.1 choice (r, false) (expandedNode_original D.val choice r hr),
    hlabel, ?_⟩
  intro w hw
  obtain ⟨x, hx, rfl⟩ := (coloredExpansion_node_iff M D.val D.property.1 choice w).mp hw
  apply normalize_reach_forward
  exact rawExpansion_proper_root M D.val D.property.1 choice r hr hroot _
    (Finset.mem_image.mpr ⟨x, hx, rfl⟩)

theorem coloredExpansion_down_subset (M : DependencyMatching G) (D : HLS.WitnessDAG ι)
    (hD : D.Valid G) (choice : WNode ι → ExpansionChoice) :
    (coloredExpansion M D hD choice).2 ⊆ (coloredExpansion M D hD choice).1.nodes := by
  intro w hw
  obtain ⟨x, hx, rfl⟩ := Finset.mem_image.mp hw
  exact expansionName_mem M D hD choice x (Finset.mem_filter.mp hx).1

noncomputable def expansionFamilyMap (M : DependencyMatching G) (α : ι)
    (F : ExpansionFamily M α) : DecoratedFamily G Finset.univ α :=
  ⟨⟨(coloredExpansion M F.1.val F.1.property.1 (extendChoice F.1.val F.2.val)).1,
    coloredExpansion_isProperCanonical M α F.1 F.2⟩,
    ⟨(coloredExpansion M F.1.val F.1.property.1 (extendChoice F.1.val F.2.val)).2,
      Finset.mem_powerset.mpr (coloredExpansion_down_subset M F.1.val F.1.property.1 _)⟩⟩

theorem expansionFamilyMap_injective (M : DependencyMatching G) (α : ι) :
    Function.Injective (expansionFamilyMap M α) := by
  rintro ⟨⟨D, hD⟩, ⟨c, hc⟩⟩ ⟨⟨E, hE⟩, ⟨d, hd⟩⟩ heq
  have hn := congrArg (fun F : DecoratedFamily G Finset.univ α => F.1.val) heq
  have hr := congrArg (fun F : DecoratedFamily G Finset.univ α => F.2.val) heq
  have hcolored : coloredExpansion M D hD.1 (extendChoice D c) =
      coloredExpansion M E hE.1 (extendChoice E d) := Prod.ext hn hr
  have hDE := original_eq_of_colored_eq M D E hD.1 hE.1 hD.2.1 hE.2.1 _ _ hc hd hcolored
  subst E
  have hcd : c = d := by
    funext u
    have h := choices_eq_of_colored_eq M D D hD.1 hE.1 hD.2.1 hE.2.1 _ _ hc hd hcolored u.val u.property
    simpa only [extendChoice, dite_eq_left u.property] using h
  subst d
  rfl

end HLS.WitnessDAG

#check @HLS.WitnessDAG.extendChoice_mem
#check @HLS.WitnessDAG.coloredExpansion_isProperCanonical
#check @HLS.WitnessDAG.coloredExpansion_down_subset
#check @HLS.WitnessDAG.expansionFamilyMap_injective
