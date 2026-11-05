/- Vertices and topological order of the HLS four-choice graph expansion. -/
module

public import PPGraph.HLS.Encoding.ExpansionDecoder
public import PPGraph.HLS.DAG.TopologicalOrder
public import PPGraph.HLS.DAG.OrderedDAG

@[expose] public section

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option backward.isDefEq.respectTransparency false

open Classical

namespace HLS.WitnessDAG

variable {ι : Type} [Fintype ι] [DecidableEq ι] {G : SimpleGraph ι}

abbrev ExpandedVertex (ι : Type) := WNode ι × Bool

def needsExtra : ExpansionChoice → Bool
  | .up | .down => false
  | .insertUp | .insertDown => true

def expandedLabel (M : DependencyMatching G) (x : ExpandedVertex ι) : ι :=
  if x.2 then M.mate x.1.1 else x.1.1

def expandedTag (x : ExpandedVertex ι) : ℕ := 2 * x.1.2 + if x.2 then 0 else 1

def expansionEmbed (M : DependencyMatching G) (x : ExpandedVertex ι) : WNode ι :=
  OrderedDAG.embed (expandedLabel M) expandedTag x

theorem expansionEmbed_injective (M : DependencyMatching G) :
    Function.Injective (expansionEmbed M) := by
  intro x y h
  obtain ⟨u, b⟩ := x
  obtain ⟨v, c⟩ := y
  have hl := congrArg Prod.fst h
  have ht := congrArg Prod.snd h
  cases b <;> cases c
  all_goals simp [expansionEmbed, OrderedDAG.embed, expandedLabel, expandedTag] at hl ht
  · have hlabel : u.1 = v.1 := hl
    have hindex : u.2 = v.2 := ht
    exact Prod.ext (Prod.ext hlabel hindex) rfl
  · change 2 * u.2 + 1 = 2 * v.2 at ht
    omega
  · change 2 * u.2 = 2 * v.2 + 1 at ht
    omega
  · have hlabel : u.1 = v.1 := M.involutive.injective hl
    have hindex : u.2 = v.2 := ht
    exact Prod.ext (Prod.ext hlabel hindex) rfl

noncomputable def expandedNodes (D : HLS.WitnessDAG ι) (choice : WNode ι → ExpansionChoice) :
    Finset (ExpandedVertex ι) :=
  D.nodes.image (fun u => (u, false)) ∪
    (D.nodes.filter (fun u => needsExtra (choice u))).image (fun u => (u, true))

theorem expandedNode_origin (D : HLS.WitnessDAG ι) (choice : WNode ι → ExpansionChoice)
    (x : ExpandedVertex ι) (hx : x ∈ expandedNodes D choice) : x.1 ∈ D.nodes := by
  rcases Finset.mem_union.mp hx with hx | hx
  · obtain ⟨u, hu, hux⟩ := Finset.mem_image.mp hx
    exact congrArg Prod.fst hux ▸ hu
  · obtain ⟨u, hu, hux⟩ := Finset.mem_image.mp hx
    exact congrArg Prod.fst hux ▸ (Finset.mem_filter.mp hu).1

theorem expandedNode_original (D : HLS.WitnessDAG ι) (choice : WNode ι → ExpansionChoice)
    (u : WNode ι) (hu : u ∈ D.nodes) : (u, false) ∈ expandedNodes D choice :=
  Finset.mem_union_left _ (Finset.mem_image.mpr ⟨u, hu, rfl⟩)

theorem expandedNode_extra (D : HLS.WitnessDAG ι) (choice : WNode ι → ExpansionChoice)
    (u : WNode ι) (hu : u ∈ D.nodes) (hc : needsExtra (choice u) = true) :
    (u, true) ∈ expandedNodes D choice :=
  Finset.mem_union_right _ (Finset.mem_image.mpr
    ⟨u, Finset.mem_filter.mpr ⟨hu, hc⟩, rfl⟩)

noncomputable def expandedBefore (G : SimpleGraph ι) (D : HLS.WitnessDAG ι) (hD : D.Valid G)
    (x y : ExpandedVertex ι) : Prop :=
  topoBefore G D hD x.1 y.1 ∨ (x.1 = y.1 ∧ x.2 = true ∧ y.2 = false)

theorem expandedBefore_irrefl (G : SimpleGraph ι) (D : HLS.WitnessDAG ι) (hD : D.Valid G)
    (x : ExpandedVertex ι) : ¬ expandedBefore G D hD x x := by
  simp only [expandedBefore, topoBefore_irrefl, false_or, true_and]
  intro h
  exact Bool.noConfusion (h.1.symm.trans h.2)

theorem expandedBefore_trans (G : SimpleGraph ι) (D : HLS.WitnessDAG ι) (hD : D.Valid G)
    (x y z : ExpandedVertex ι) (hxy : expandedBefore G D hD x y)
    (hyz : expandedBefore G D hD y z) : expandedBefore G D hD x z := by
  rcases hxy with hxy | ⟨hxy, hxt, hyf⟩
  · rcases hyz with hyz | ⟨hyz, _, _⟩
    · exact Or.inl (topoBefore_trans G D hD _ _ _ hxy hyz)
    · exact Or.inl (hyz ▸ hxy)
  · rcases hyz with hyz | ⟨_, hyt, _⟩
    · exact Or.inl (hxy.symm ▸ hyz)
    · exact False.elim (Bool.noConfusion (hyf.symm.trans hyt))

theorem expandedBefore_total (G : SimpleGraph ι) (D : HLS.WitnessDAG ι) (hD : D.Valid G)
    (choice : WNode ι → ExpansionChoice) (x y : ExpandedVertex ι)
    (hx : x ∈ expandedNodes D choice) (hy : y ∈ expandedNodes D choice) (hne : x ≠ y) :
    expandedBefore G D hD x y ∨ expandedBefore G D hD y x := by
  by_cases ho : x.1 = y.1
  · have hb : x.2 ≠ y.2 := fun h => hne (Prod.ext ho h)
    have hcases : (x.2 = true ∧ y.2 = false) ∨ (y.2 = true ∧ x.2 = false) := by
      cases hxb : x.2 <;> cases hyb : y.2 <;> simp_all
    rcases hcases with h | h
    · exact Or.inl (Or.inr ⟨ho, h⟩)
    · exact Or.inr (Or.inr ⟨ho.symm, h⟩)
  · rcases topoBefore_total G D hD x.1 y.1
      (expandedNode_origin D choice x hx) (expandedNode_origin D choice y hy) ho with h | h
    · exact Or.inl (Or.inl h)
    · exact Or.inr (Or.inl h)

end HLS.WitnessDAG

#check @HLS.WitnessDAG.expansionEmbed_injective
#check @HLS.WitnessDAG.expandedNode_origin
#check @HLS.WitnessDAG.expandedNode_original
#check @HLS.WitnessDAG.expandedNode_extra
#check @HLS.WitnessDAG.expandedBefore_irrefl
#check @HLS.WitnessDAG.expandedBefore_trans
#check @HLS.WitnessDAG.expandedBefore_total
