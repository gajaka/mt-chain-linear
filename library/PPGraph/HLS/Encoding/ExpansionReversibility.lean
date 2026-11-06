/- The reversible inserted arcs and persistence of original alternate paths. -/
module

public import PPGraph.HLS.DAG.ExpansionGraph
public import PPGraph.HLS.Encoding.OrderedReversal

@[expose] public section

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option backward.isDefEq.respectTransparency false

open Classical

namespace HLS.WitnessDAG

variable {ι : Type} [Fintype ι] [DecidableEq ι] {G : SimpleGraph ι}

theorem expanded_pair_no_middle (G : SimpleGraph ι) (D : HLS.WitnessDAG ι) (hD : D.Valid G)
    (u : WNode ι) (z : ExpandedVertex ι) :
    ¬ (expandedBefore G D hD (u, true) z ∧ expandedBefore G D hD z (u, false)) := by
  rintro ⟨h₁, h₂⟩
  rcases h₁ with h₁ | ⟨h₁, _, hzFalse⟩
  · rcases h₂ with h₂ | ⟨h₂, _, _⟩
    · exact topoBefore_asymm G D hD _ _ h₁ h₂
    · change z.1 = u at h₂
      change topoBefore G D hD u z.1 at h₁
      rw [h₂] at h₁
      exact topoBefore_irrefl G D hD u h₁
  · rcases h₂ with h₂ | ⟨_, hzTrue, _⟩
    · change u = z.1 at h₁
      change topoBefore G D hD z.1 u at h₂
      rw [← h₁] at h₂
      exact topoBefore_irrefl G D hD u h₂
    · exact Bool.noConfusion (hzFalse.symm.trans hzTrue)

theorem rawExpansion_extra_reversible (M : DependencyMatching G) (D : HLS.WitnessDAG ι)
    (hD : D.Valid G) (choice : WNode ι → ExpansionChoice) (u : WNode ι)
    (hu : u ∈ D.nodes) (hExtra : needsExtra (choice u) = true) :
    Acyclic (reverseArc (rawExpansion M D hD choice).Edge
      (expansionEmbed M (u, true)) (expansionEmbed M (u, false))) := by
  apply OrderedDAG.reversible_if_no_middle G _ _ _ _
    (fun _ _ _ _ h => expansionEmbed_injective M h)
    (fun x _ y _ z _ => expandedBefore_trans G D hD x y z)
    (rawExpansion_valid M D hD choice) _ _
    (expandedNode_extra D choice u hu hExtra) (expandedNode_original D choice u hu)
    (Or.inr ⟨rfl, rfl, rfl⟩)
  · change M.mate u.1 = u.1 ∨ G.Adj (M.mate u.1) u.1
    by_cases hm : M.mate u.1 = u.1
    · exact Or.inl hm
    · exact Or.inr (G.adj_symm (M.adjacent u.1 hm))
  · intro z _
    exact expanded_pair_no_middle G D hD u z

theorem originalExpansion_injective (M : DependencyMatching G) :
    Function.Injective (fun u : WNode ι => expansionEmbed M (u, false)) := by
  intro u v h
  have huv : (u, false) = (v, false) := expansionEmbed_injective M h
  exact congrArg (fun z : ExpandedVertex ι => z.1) huv

theorem original_alternate_path_lifts (M : DependencyMatching G) (D : HLS.WitnessDAG ι)
    (hD : D.Valid G) (choice : WNode ι → ExpansionChoice) (u v : WNode ι)
    (hpath : Relation.TransGen (eraseArc D.Edge u v) u v) :
    Relation.TransGen (eraseArc (rawExpansion M D hD choice).Edge
      (expansionEmbed M (u, false)) (expansionEmbed M (v, false)))
      (expansionEmbed M (u, false)) (expansionEmbed M (v, false)) := by
  apply Relation.TransGen.lift (fun w => expansionEmbed M (w, false)) ?_ _ _ hpath
  intro x y he
  refine ⟨rawExpansion_original_edge M D hD choice x y he.1, ?_⟩
  rintro ⟨hxu, hyv⟩
  exact he.2 ⟨originalExpansion_injective M hxu, originalExpansion_injective M hyv⟩

/-- An original non-reversible arc cannot become reversible after expansion. -/
theorem original_nonreversible_persists (M : DependencyMatching G) (D : HLS.WitnessDAG ι)
    (hD : D.Valid G) (choice : WNode ι → ExpansionChoice) (u v : WNode ι)
    (he : D.Edge u v) (hn : ¬ Acyclic (reverseArc D.Edge u v)) :
    ¬ Acyclic (reverseArc (rawExpansion M D hD choice).Edge
      (expansionEmbed M (u, false)) (expansionEmbed M (v, false))) := by
  have hpath : Relation.TransGen (eraseArc D.Edge u v) u v := by
    by_contra hno
    exact hn ((reversible_iff_no_alternate_path D.Edge u v hD.acyclic he).mpr hno)
  intro hrev
  have he' := rawExpansion_original_edge M D hD choice u v he
  have hno := (reversible_iff_no_alternate_path _ _ _
    (rawExpansion_valid M D hD choice).acyclic he').mp hrev
  exact hno (original_alternate_path_lifts M D hD choice u v hpath)

end HLS.WitnessDAG

#check @HLS.WitnessDAG.expanded_pair_no_middle
#check @HLS.WitnessDAG.rawExpansion_extra_reversible
#check @HLS.WitnessDAG.originalExpansion_injective
#check @HLS.WitnessDAG.original_alternate_path_lifts
#check @HLS.WitnessDAG.original_nonreversible_persists
