/-
  Locality of the Shearer runtime budget under BDD decomposition.

  For disconnected finite sets S and T and a root set J contained in S,
  the upper-indexed coefficient on S union T gains the factor q(T).
  The avoidance polynomial gains the same factor. When q(T) is nonzero,
  it cancels from the stable-sequence budget. Strict Shearer positivity
  supplies this nonvanishing condition for every BDD component cut.
-/
module

public import PPGraph.Shearer.Stable
public import PPGraph.Shearer.BDD

@[expose] public section

set_option autoImplicit false
set_option linter.unusedSectionVars false

open Classical

namespace Shearer

variable {ι : Type*} [DecidableEq ι]

/-- Removing the closed neighborhood of J from one component leaves the
other disconnected part intact. -/
theorem outside_union (G : SimpleGraph ι) (S T J : Finset ι)
    (hJS : J ⊆ S) (hdis : Disjoint S T)
    (hcross : ∀ a ∈ S, ∀ b ∈ T, ¬ G.Adj a b) :
    outside G (S ∪ T) J = outside G S J ∪ T := by
  ext b
  simp only [mem_outside, Finset.mem_union]
  constructor
  · rintro ⟨hbS | hbT, hbJ, hbadj⟩
    · exact Or.inl ⟨hbS, hbJ, hbadj⟩
    · exact Or.inr hbT
  · rintro (⟨hbS, hbJ, hbadj⟩ | hbT)
    · exact ⟨Or.inl hbS, hbJ, hbadj⟩
    · exact ⟨Or.inr hbT,
        (fun hbJ => Finset.disjoint_left.mp hdis (hJS hbJ) hbT),
        fun a ha => hcross a (hJS ha) b hbT⟩

/-- Upper-indexed coefficients factor across a disconnected split.
This includes non-independent J, for which both coefficients vanish. -/
theorem coefficient_union (G : SimpleGraph ι) (p : ι → ℝ)
    (S T J : Finset ι) (hJS : J ⊆ S) (hdis : Disjoint S T)
    (hcross : ∀ a ∈ S, ∀ b ∈ T, ¬ G.Adj a b) :
    coefficient G p (S ∪ T) J = coefficient G p S J * polynomial G p T := by
  by_cases hJ : Independent G J
  · rw [coefficient_factor G p (S ∪ T) J (hJS.trans Finset.subset_union_left) hJ,
      coefficient_factor G p S J hJS hJ, outside_union G S T J hJS hdis hcross,
      polynomial_union G p (outside G S J) T
        (hdis.mono_left (outside_subset G S J))
        (fun a ha b hb => hcross a (outside_subset G S J ha) b hb)]
    ring
  · rw [coefficient_eq_zero_of_not_independent G p (S ∪ T) J hJ,
      coefficient_eq_zero_of_not_independent G p S J hJ, zero_mul]

/-- A disconnected part cancels from the coefficient-to-polynomial ratio. -/
theorem stableBudget_union (G : SimpleGraph ι) (p : ι → ℝ)
    (S T J : Finset ι) (hJS : J ⊆ S) (hdis : Disjoint S T)
    (hcross : ∀ a ∈ S, ∀ b ∈ T, ¬ G.Adj a b)
    (hT : polynomial G p T ≠ 0) :
    stableBudget G p (S ∪ T) J = stableBudget G p S J := by
  unfold stableBudget
  rw [coefficient_union G p S T J hJS hdis hcross,
    polynomial_union G p S T hdis hcross]
  exact mul_div_mul_right _ _ hT

variable {C V : Type} [DecidableEq C] [DecidableEq V]

/-- The coefficient for roots in a BDD component factors by the polynomial
on the remaining components. -/
theorem coefficient_compOf (vars : CertVars C V) (p : C → ℝ)
    (B : Finset C) (c : C) (J : Finset C) (hJ : J ⊆ compOf vars B c) :
    coefficient (dependencyGraph vars) p B J =
      coefficient (dependencyGraph vars) p (compOf vars B c) J *
        polynomial (dependencyGraph vars) p (B \ compOf vars B c) := by
  have h := coefficient_union (dependencyGraph vars) p
    (compOf vars B c) (B \ compOf vars B c) J hJ
    (Finset.disjoint_left.mpr (fun _ ha hb => (Finset.mem_sdiff.mp hb).2 ha))
    (not_adj_compOf_sdiff vars B c)
  rwa [Finset.union_sdiff_of_subset (compOf_subset vars B c)] at h

/-- Under the strict criterion, the stable-sequence budget for roots in a
component equals the budget computed using that component alone. -/
theorem stableBudget_compOf (vars : CertVars C V) (p : C → ℝ)
    (B : Finset C) (c : C) (J : Finset C) (hJ : J ⊆ compOf vars B c)
    (hcriterion : StrictCriterion (dependencyGraph vars) p B) :
    stableBudget (dependencyGraph vars) p B J =
      stableBudget (dependencyGraph vars) p (compOf vars B c) J := by
  have h := stableBudget_union (dependencyGraph vars) p
    (compOf vars B c) (B \ compOf vars B c) J hJ
    (Finset.disjoint_left.mpr (fun _ ha hb => (Finset.mem_sdiff.mp hb).2 ha))
    (not_adj_compOf_sdiff vars B c)
    (ne_of_gt (hcriterion _ Finset.sdiff_subset))
  rwa [Finset.union_sdiff_of_subset (compOf_subset vars B c)] at h

theorem coefficient_singleton_compOf (vars : CertVars C V) (p : C → ℝ)
    (B : Finset C) (c α : C) (hα : α ∈ compOf vars B c) :
    coefficient (dependencyGraph vars) p B {α} =
      coefficient (dependencyGraph vars) p (compOf vars B c) {α} *
        polynomial (dependencyGraph vars) p (B \ compOf vars B c) :=
  coefficient_compOf vars p B c {α} (Finset.singleton_subset_iff.mpr hα)

theorem stableBudget_singleton_compOf (vars : CertVars C V) (p : C → ℝ)
    (B : Finset C) (c α : C) (hα : α ∈ compOf vars B c)
    (hcriterion : StrictCriterion (dependencyGraph vars) p B) :
    stableBudget (dependencyGraph vars) p B {α} =
      stableBudget (dependencyGraph vars) p (compOf vars B c) {α} :=
  stableBudget_compOf vars p B c {α} (Finset.singleton_subset_iff.mpr hα) hcriterion

/-- The event-wise runtime budget depends only on the event's own component. -/
theorem stableBudget_singleton_own_compOf (vars : CertVars C V) (p : C → ℝ)
    (B : Finset C) (α : C) (hα : α ∈ B)
    (hcriterion : StrictCriterion (dependencyGraph vars) p B) :
    stableBudget (dependencyGraph vars) p B {α} =
      stableBudget (dependencyGraph vars) p (compOf vars B α) {α} :=
  stableBudget_singleton_compOf vars p B α α (mem_compOf_self vars B α hα) hcriterion

end Shearer

#check @Shearer.outside_union
#check @Shearer.coefficient_union
#check @Shearer.stableBudget_union
#check @Shearer.coefficient_compOf
#check @Shearer.stableBudget_compOf
#check @Shearer.coefficient_singleton_compOf
#check @Shearer.stableBudget_singleton_compOf
#check @Shearer.stableBudget_singleton_own_compOf
