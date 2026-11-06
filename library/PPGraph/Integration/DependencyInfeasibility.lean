/-
  Exact satisfiability, not merely LLL feasibility, decomposes over the existing
  BDD components for local obligations on a product state space.
  Component solutions are glued by their component identity, so independent
  choices within the same component cannot accidentally be mixed.
  A frame freezes every variable outside the entire selected obligation family.
  Arbitrary additional admissibility constraints need their own decomposition.
-/
module

public import PPGraph.Dependency.Partition
public import PPGraph.Decision.UnsatisfiableCore

@[expose] public section

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option backward.isDefEq.respectTransparency false

namespace RepairFeasibility

variable {C V α : Type} [DecidableEq C] [DecidableEq V]

def InFamilyFootprint (vars : CertVars C V) (B : Finset C) (v : V) : Prop :=
  ∃ c ∈ B, v ∈ vars c

noncomputable def variableOwner (vars : CertVars C V) (B : Finset C) (v : V) : Finset C := by
  classical
  exact if h : InFamilyFootprint vars B v then compOf vars B (Classical.choose h) else ∅

theorem variableOwner_eq_component (vars : CertVars C V) (B : Finset C)
    (c : C) (hc : c ∈ B) (v : V) (hv : v ∈ vars c) :
    variableOwner vars B v = compOf vars B c := by
  classical
  have h : InFamilyFootprint vars B v := ⟨c, hc, hv⟩
  have hd := Classical.choose_spec h
  have hs : SameComponent vars B c (Classical.choose h) :=
    Relation.EqvGen.rel _ _ ⟨hc, hd.1, ⟨v, Finset.mem_inter.mpr ⟨hv, hd.2⟩⟩⟩
  simp only [variableOwner, dite_eq_left h]
  exact (compOf_eq_of_sameComponent vars B c (Classical.choose h) hs).symm

noncomputable def componentSolution (sat : C → (V → α) → Prop)
    (base : V → α) (K : Finset C) : V → α := by
  classical
  exact if h : ∃ z, ∀ c ∈ K, sat c z then Classical.choose h else base

theorem componentSolution_spec (sat : C → (V → α) → Prop) (base : V → α)
    (K : Finset C) (h : Satisfiable (fun _ => True) sat K) :
    ∀ c ∈ K, sat c (componentSolution sat base K) := by
  classical
  have he : ∃ z, ∀ c ∈ K, sat c z := by
    obtain ⟨z, _, hz⟩ := h
    exact ⟨z, hz⟩
  simpa only [componentSolution, dite_eq_left he] using Classical.choose_spec he

noncomputable def assembleComponents (vars : CertVars C V) (B : Finset C)
    (sat : C → (V → α) → Prop) (base : V → α) (v : V) : α := by
  classical
  exact if InFamilyFootprint vars B v then
    componentSolution sat base (variableOwner vars B v) v else base v

theorem assemble_agrees_on_obligation (vars : CertVars C V) (B : Finset C)
    (sat : C → (V → α) → Prop) (base : V → α) (c : C) (hc : c ∈ B) :
    ∀ v ∈ vars c, assembleComponents vars B sat base v =
      componentSolution sat base (compOf vars B c) v := by
  classical
  intro v hv
  simp only [assembleComponents, ite_eq_left (show InFamilyFootprint vars B v from ⟨c, hc, hv⟩),
    variableOwner_eq_component vars B c hc v hv]

theorem assemble_satisfies (vars : CertVars C V) (B : Finset C)
    (sat : C → (V → α) → Prop) (hloc : Local vars sat) (base : V → α)
    (hparts : ∀ c ∈ B, Satisfiable (fun _ => True) sat (compOf vars B c)) :
    ∀ c ∈ B, sat c (assembleComponents vars B sat base) := by
  intro c hc
  apply (hloc c _ _ (assemble_agrees_on_obligation vars B sat base c hc)).mpr
  exact componentSolution_spec sat base _ (hparts c hc) c (mem_compOf_self vars B c hc)

def FrameAllowed (vars : CertVars C V) (B : Finset C) (base z : V → α) : Prop :=
  ∀ v, ¬ InFamilyFootprint vars B v → z v = base v

theorem assemble_preserves_frame (vars : CertVars C V) (B : Finset C)
    (sat : C → (V → α) → Prop) (base : V → α) :
    FrameAllowed vars B base (assembleComponents vars B sat base) := by
  classical
  intro v hv
  simp only [assembleComponents, ite_eq_right hv]

theorem frame_satisfiable_iff_components (vars : CertVars C V) (B : Finset C)
    (sat : C → (V → α) → Prop) (hloc : Local vars sat) (base : V → α) :
    Satisfiable (FrameAllowed vars B base) sat B ↔
      ∀ c ∈ B, Satisfiable (fun _ => True) sat (compOf vars B c) := by
  constructor
  · intro h c hc
    exact satisfiable_mono_allowed _ _ sat _ (fun _ _ => trivial)
      (satisfiable_mono_obligations _ sat (compOf_subset vars B c) h)
  · intro h
    exact ⟨assembleComponents vars B sat base,
      assemble_preserves_frame vars B sat base, assemble_satisfies vars B sat hloc base h⟩

theorem satisfiable_iff_components (vars : CertVars C V) (B : Finset C)
    (sat : C → (V → α) → Prop) (hloc : Local vars sat) (base : V → α) :
    Satisfiable (fun _ => True) sat B ↔
      ∀ c ∈ B, Satisfiable (fun _ => True) sat (compOf vars B c) := by
  constructor
  · intro h c _
    exact satisfiable_mono_obligations _ sat (compOf_subset vars B c) h
  · intro h
    exact satisfiable_mono_allowed _ _ sat B (fun _ _ => trivial)
      ((frame_satisfiable_iff_components vars B sat hloc base).mpr h)

theorem infeasible_iff_component_infeasible (vars : CertVars C V) (B : Finset C)
    (sat : C → (V → α) → Prop) (hloc : Local vars sat) (base : V → α) :
    Infeasible (fun _ => True) sat B ↔
      ∃ c ∈ B, Infeasible (fun _ => True) sat (compOf vars B c) := by
  classical
  simp only [Infeasible, satisfiable_iff_components vars B sat hloc base,
    not_forall, exists_prop]

theorem frame_infeasible_iff_component_infeasible (vars : CertVars C V) (B : Finset C)
    (sat : C → (V → α) → Prop) (hloc : Local vars sat) (base : V → α) :
    Infeasible (FrameAllowed vars B base) sat B ↔
      ∃ c ∈ B, Infeasible (fun _ => True) sat (compOf vars B c) := by
  classical
  simp only [Infeasible, frame_satisfiable_iff_components vars B sat hloc base,
    not_forall, exists_prop]

/-- An inclusion-minimal conflict cannot span independent BDD components. -/
theorem minimalCore_is_one_component (vars : CertVars C V) (K : Finset C)
    (sat : C → (V → α) → Prop) (hloc : Local vars sat) (base : V → α)
    (hK : MinimalCore (fun _ => True) sat K) :
    ∃ c ∈ K, compOf vars K c = K := by
  classical
  obtain ⟨c, hc, hbad⟩ := (infeasible_iff_component_infeasible vars K sat hloc base).mp hK.1
  refine ⟨c, hc, ?_⟩
  by_contra hn
  have hp : compOf vars K c ⊂ K :=
    Finset.ssubset_iff_subset_ne.mpr ⟨compOf_subset vars K c, hn⟩
  exact hbad (minimalCore_proper_subset_satisfiable (fun _ => True) sat hp hK)

end RepairFeasibility

#check @RepairFeasibility.variableOwner_eq_component
#check @RepairFeasibility.componentSolution_spec
#check @RepairFeasibility.assemble_agrees_on_obligation
#check @RepairFeasibility.assemble_satisfies
#check @RepairFeasibility.assemble_preserves_frame
#check @RepairFeasibility.frame_satisfiable_iff_components
#check @RepairFeasibility.satisfiable_iff_components
#check @RepairFeasibility.infeasible_iff_component_infeasible
#check @RepairFeasibility.frame_infeasible_iff_component_infeasible
#check @RepairFeasibility.minimalCore_is_one_component
