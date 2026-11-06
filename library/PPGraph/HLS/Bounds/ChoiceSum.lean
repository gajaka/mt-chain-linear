/- Finite product-of-sums over the legal local expansion choices. -/
module

public import PPGraph.HLS.Bounds.ExpansionWeight

@[expose] public section

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option backward.isDefEq.respectTransparency false

open Classical
open scoped ENNReal

namespace HLS.WitnessDAG

variable {ι : Type} [Fintype ι] [DecidableEq ι] {G : SimpleGraph ι}

noncomputable def forcedUp (M : DependencyMatching G) (D : HLS.WitnessDAG ι)
    (u : WNode ι) : Prop := u ∈ arcNodes (matchingArcs M D) ∨ M.mate u.1 = u.1

abbrev LocalChoice (M : DependencyMatching G) (D : HLS.WitnessDAG ι) (u : ↥D.nodes) :=
  {c : ExpansionChoice // forcedUp M D u.val → c = .up}

abbrev IndependentChoices (M : DependencyMatching G) (D : HLS.WitnessDAG ι) :=
  ∀ u : ↥D.nodes, LocalChoice M D u

noncomputable instance localChoiceFintype (M : DependencyMatching G) (D : HLS.WitnessDAG ι)
    (u : ↥D.nodes) : Fintype (LocalChoice M D u) := Fintype.ofFinite _

noncomputable def independentToLegal (M : DependencyMatching G) (D : HLS.WitnessDAG ι)
    (hD : D.Valid G) (c : IndependentChoices M D) : LegalChoices M D := by
  refine ⟨(fun u => (c u).val), ?_, ?_⟩
  · intro u hu
    have hmem : u ∈ D.nodes := by
      obtain ⟨e, he, hue⟩ := Finset.mem_biUnion.mp hu
      have hEdge := (Finset.mem_filter.mp he).1
      simp only [Finset.mem_insert, Finset.mem_singleton] at hue
      rcases hue with rfl | rfl
      · exact (hD.supported _ _ hEdge).1
      · exact (hD.supported _ _ hEdge).2
    rw [extendChoice_mem D _ u hmem]
    exact (c ⟨u, hmem⟩).property (Or.inl hu)
  · intro u hu hm
    rw [extendChoice_mem D _ u hu]
    exact (c ⟨u, hu⟩).property (Or.inr hm)

noncomputable def legalToIndependent (M : DependencyMatching G) (D : HLS.WitnessDAG ι)
    (c : LegalChoices M D) : IndependentChoices M D := by
  intro u
  refine ⟨c.val u, ?_⟩
  intro h
  rcases h with h | h
  · have hc := c.property.1 u.val h
    simpa only [extendChoice, dite_eq_left u.property] using hc
  · have hc := c.property.2 u.val u.property h
    simpa only [extendChoice, dite_eq_left u.property] using hc

noncomputable def independentChoicesEquiv (M : DependencyMatching G) (D : HLS.WitnessDAG ι)
    (hD : D.Valid G) : IndependentChoices M D ≃ LegalChoices M D where
  toFun := independentToLegal M D hD
  invFun := legalToIndependent M D
  left_inv c := by funext u; apply Subtype.ext; rfl
  right_inv c := by apply Subtype.ext; rfl

theorem sum_localChoice (M : DependencyMatching G) (D : HLS.WitnessDAG ι)
    (u : ↥D.nodes) (up down : ι → ℝ≥0∞) :
    (∑ c : LocalChoice M D u, choiceWeight M up down u.val.1 c.val) =
      if forcedUp M D u.val then up u.val.1 else
        up u.val.1 + down u.val.1 + down u.val.1 * up (M.mate u.val.1) +
          down u.val.1 * down (M.mate u.val.1) := by
  by_cases hf : forcedUp M D u.val
  · have heq : ∀ c : LocalChoice M D u, c.val = .up := fun c => c.property hf
    have : Unique (LocalChoice M D u) :=
      ⟨⟨⟨.up, fun _ => rfl⟩⟩, fun c => Subtype.ext (heq c)⟩
    rw [ite_eq_left hf, Fintype.sum_unique, heq default]
    rfl
  · let e : LocalChoice M D u ≃ ExpansionChoice :=
      { toFun := Subtype.val
        invFun := fun c => ⟨c, fun h => False.elim (hf h)⟩
        left_inv := fun _ => rfl
        right_inv := fun _ => rfl }
    rw [ite_eq_right hf]
    calc
      _ = ∑ c : ExpansionChoice, choiceWeight M up down u.val.1 c :=
        e.sum_comp (fun c => choiceWeight M up down u.val.1 c)
      _ = _ := by
        change (∑ c ∈ ({.up, .down, .insertUp, .insertDown} : Finset ExpansionChoice),
          choiceWeight M up down u.val.1 c) = _
        simp [choiceWeight, add_assoc]

noncomputable instance legalChoicesFintype (M : DependencyMatching G) (D : HLS.WitnessDAG ι) :
    Fintype (LegalChoices M D) := Fintype.ofFinite _

theorem tsum_legalChoiceWeight_eq (M : DependencyMatching G) (D : HLS.WitnessDAG ι)
    (hD : D.Valid G) (up down : ι → ℝ≥0∞) :
    (∑' c : LegalChoices M D, ∏ u : ↥D.nodes, choiceWeight M up down u.val.1 (c.val u)) =
      ∏ u : ↥D.nodes, if forcedUp M D u.val then up u.val.1 else
        up u.val.1 + down u.val.1 + down u.val.1 * up (M.mate u.val.1) +
          down u.val.1 * down (M.mate u.val.1) := by
  rw [tsum_fintype, ← (independentChoicesEquiv M D hD).sum_comp]
  change (∑ c : IndependentChoices M D, ∏ u : ↥D.nodes, choiceWeight M up down u.val.1 (c u).val) = _
  calc
    _ = ∏ u : ↥D.nodes, ∑ c : LocalChoice M D u, choiceWeight M up down u.val.1 c.val :=
      (Fintype.prod_sum (fun u (c : LocalChoice M D u) => choiceWeight M up down u.val.1 c.val)).symm
    _ = _ := Finset.prod_congr rfl (fun u _ => sum_localChoice M D u up down)

end HLS.WitnessDAG

#check @HLS.WitnessDAG.sum_localChoice
#check @HLS.WitnessDAG.tsum_legalChoiceWeight_eq
