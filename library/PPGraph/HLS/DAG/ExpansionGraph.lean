/-
  The four-choice graph expansion is a proper witness DAG, and its
  induced graph on original vertices is exactly the original DAG.
  He--Li--Sun, Definition 3.11 and Appendix C, Lemma C.1.
-/
module

public import PPGraph.HLS.DAG.ExpansionVertices
public import PPGraph.HLS.Encoding.Normalization

@[expose] public section

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option backward.isDefEq.respectTransparency false

open Classical

namespace HLS.WitnessDAG

variable {ι : Type} [Fintype ι] [DecidableEq ι] {G : SimpleGraph ι}

noncomputable def rawExpansion (M : DependencyMatching G) (D : HLS.WitnessDAG ι)
    (hD : D.Valid G) (choice : WNode ι → ExpansionChoice) : HLS.WitnessDAG ι :=
  OrderedDAG.build G (expandedNodes D choice) (expandedLabel M) expandedTag
    (expandedBefore G D hD)

theorem rawExpansion_valid (M : DependencyMatching G) (D : HLS.WitnessDAG ι)
    (hD : D.Valid G) (choice : WNode ι → ExpansionChoice) :
    (rawExpansion M D hD choice).Valid G :=
  OrderedDAG.valid G _ _ _ _ (fun _ _ _ _ h => expansionEmbed_injective M h)
    (fun x _ => expandedBefore_irrefl G D hD x)
    (fun x _ y _ z _ => expandedBefore_trans G D hD x y z)
    (fun x hx y hy => expandedBefore_total G D hD choice x y hx hy)

theorem rawExpansion_original_mem (M : DependencyMatching G) (D : HLS.WitnessDAG ι)
    (hD : D.Valid G) (choice : WNode ι → ExpansionChoice) (u : WNode ι) (hu : u ∈ D.nodes) :
    expansionEmbed M (u, false) ∈ (rawExpansion M D hD choice).nodes :=
  (OrderedDAG.node_iff _ _ _ _ _ _).mpr ⟨(u, false), expandedNode_original D choice u hu, rfl⟩

theorem rawExpansion_original_edge_iff (M : DependencyMatching G) (D : HLS.WitnessDAG ι)
    (hD : D.Valid G) (choice : WNode ι → ExpansionChoice) (u v : WNode ι)
    (hu : u ∈ D.nodes) (hv : v ∈ D.nodes) :
    (rawExpansion M D hD choice).Edge (expansionEmbed M (u, false)) (expansionEmbed M (v, false)) ↔
      D.Edge u v := by
  unfold rawExpansion expansionEmbed
  rw [OrderedDAG.edge_embed G _ _ _ _ (fun _ _ _ _ h => expansionEmbed_injective M h)
    _ _ (expandedNode_original D choice u hu) (expandedNode_original D choice v hv)]
  simp only [expandedBefore, expandedLabel, Bool.false_eq_true, ite_false,
    and_false, false_and, or_false]
  constructor
  · rintro ⟨hbefore, hdep⟩
    exact edge_of_topoBefore_dependent G D hD u v hu hv hbefore hdep
  · intro he
    exact ⟨topoBefore_of_edge G D hD u v he, edge_dependent G D hD u v he⟩

theorem rawExpansion_original_edge (M : DependencyMatching G) (D : HLS.WitnessDAG ι)
    (hD : D.Valid G) (choice : WNode ι → ExpansionChoice) (u v : WNode ι) (he : D.Edge u v) :
    (rawExpansion M D hD choice).Edge (expansionEmbed M (u, false)) (expansionEmbed M (v, false)) :=
  (rawExpansion_original_edge_iff M D hD choice u v (hD.supported _ _ he).1
    (hD.supported _ _ he).2).mpr he

theorem rawExpansion_original_reach (M : DependencyMatching G) (D : HLS.WitnessDAG ι)
    (hD : D.Valid G) (choice : WNode ι → ExpansionChoice) (u v : WNode ι) (he : D.Reach u v) :
    (rawExpansion M D hD choice).Reach (expansionEmbed M (u, false)) (expansionEmbed M (v, false)) :=
  Relation.ReflTransGen.lift (fun u => expansionEmbed M (u, false))
    (fun u v he => rawExpansion_original_edge M D hD choice u v he) _ _ he

theorem rawExpansion_extra_edge (M : DependencyMatching G) (D : HLS.WitnessDAG ι)
    (hD : D.Valid G) (choice : WNode ι → ExpansionChoice) (u : WNode ι)
    (hu : u ∈ D.nodes) (hExtra : needsExtra (choice u) = true) :
    (rawExpansion M D hD choice).Edge (expansionEmbed M (u, true)) (expansionEmbed M (u, false)) := by
  apply (OrderedDAG.edge_embed G _ _ _ _ (fun _ _ _ _ h => expansionEmbed_injective M h)
    _ _ (expandedNode_extra D choice u hu hExtra) (expandedNode_original D choice u hu)).mpr
  refine ⟨Or.inr ⟨rfl, rfl, rfl⟩, ?_⟩
  change M.mate u.1 = u.1 ∨ G.Adj (M.mate u.1) u.1
  by_cases hm : M.mate u.1 = u.1
  · exact Or.inl hm
  · exact Or.inr (G.adj_symm (M.adjacent u.1 hm))

theorem rawExpansion_proper_root (M : DependencyMatching G) (D : HLS.WitnessDAG ι)
    (hD : D.Valid G) (choice : WNode ι → ExpansionChoice) (r : WNode ι)
    (_hr : r ∈ D.nodes) (hroot : ∀ u ∈ D.nodes, D.Reach u r) :
    ∀ x ∈ (rawExpansion M D hD choice).nodes,
      (rawExpansion M D hD choice).Reach x (expansionEmbed M (r, false)) := by
  intro x hx
  obtain ⟨y, hy, hyx⟩ := (OrderedDAG.node_iff _ _ _ _ _ x).mp hx
  rw [← hyx]
  have hyOrigin := expandedNode_origin D choice y hy
  have hpath := rawExpansion_original_reach M D hD choice y.1 r (hroot y.1 hyOrigin)
  rcases y with ⟨u, b⟩
  cases b with
  | false => exact hpath
  | true =>
    have hExtra : needsExtra (choice u) = true := by
      rcases Finset.mem_union.mp hy with h | h
      · obtain ⟨w, _, hw⟩ := Finset.mem_image.mp h
        have hb := congrArg Prod.snd hw
        cases hb
      · obtain ⟨w, hw, hwu⟩ := Finset.mem_image.mp h
        have hwu' : w = u := congrArg Prod.fst hwu
        exact hwu' ▸ (Finset.mem_filter.mp hw).2
    exact hpath.head (rawExpansion_extra_edge M D hD choice u hyOrigin hExtra)

theorem rawExpansion_proper (M : DependencyMatching G) (D : HLS.WitnessDAG ι)
    (hD : D.Valid G) (choice : WNode ι → ExpansionChoice) (hp : D.Proper) :
    (rawExpansion M D hD choice).Proper := by
  obtain ⟨r, hr, hroot⟩ := hp
  exact ⟨expansionEmbed M (r, false), rawExpansion_original_mem M D hD choice r hr,
    rawExpansion_proper_root M D hD choice r hr hroot⟩

end HLS.WitnessDAG

#check @HLS.WitnessDAG.rawExpansion_valid
#check @HLS.WitnessDAG.rawExpansion_original_mem
#check @HLS.WitnessDAG.rawExpansion_original_edge_iff
#check @HLS.WitnessDAG.rawExpansion_original_edge
#check @HLS.WitnessDAG.rawExpansion_original_reach
#check @HLS.WitnessDAG.rawExpansion_extra_edge
#check @HLS.WitnessDAG.rawExpansion_proper_root
#check @HLS.WitnessDAG.rawExpansion_proper
