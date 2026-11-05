/-
  Shearer's signed independence polynomial factors over the existing
  blocking dependency components. Consequently, strict positivity on
  every subset can be checked separately in each BDD component.
-/
module

public import PPGraph.Shearer.Polynomial
public import PPGraph.Dependency.Decomposition

@[expose] public section

set_option autoImplicit false
set_option linter.unusedSectionVars false

open Classical Relation

namespace Shearer

variable {C V : Type} [DecidableEq C] [DecidableEq V]

/-- The simple graph obtained from the existing shared-variable relation. -/
def dependencyGraph (vars : CertVars C V) : SimpleGraph C :=
  SimpleGraph.fromRel (dependent vars)

@[simp]
theorem dependencyGraph_adj_iff (vars : CertVars C V) (a b : C) :
    (dependencyGraph vars).Adj a b ↔ a ≠ b ∧ dependent vars a b := by
  rw [dependencyGraph, SimpleGraph.fromRel_adj]
  constructor
  · rintro ⟨hne, hab | hba⟩
    · exact ⟨hne, hab⟩
    · exact ⟨hne, dependent_symm vars b a hba⟩
  · rintro ⟨hne, hab⟩
    exact ⟨hne, Or.inl hab⟩

/-- No dependency edge crosses from a BDD component to its complement in B. -/
theorem not_adj_compOf_sdiff (vars : CertVars C V) (B : Finset C) (c : C) :
    ∀ a ∈ compOf vars B c, ∀ b ∈ B \ compOf vars B c,
      ¬ (dependencyGraph vars).Adj a b := by
  intro a ha b hb hab
  obtain ⟨haB, hca⟩ := Finset.mem_filter.mp ha
  obtain ⟨hbB, hbnot⟩ := Finset.mem_sdiff.mp hb
  have hdep := (dependencyGraph_adj_iff vars a b).mp hab |>.2
  have habcomp := sameComponent_of_coupled vars B a b ⟨haB, hbB, hdep⟩
  exact hbnot (Finset.mem_filter.mpr ⟨hbB, EqvGen.trans _ _ _ hca habcomp⟩)

/-- The full polynomial is the product of a component polynomial and
the polynomial on all remaining components. -/
theorem polynomial_BDD_split (vars : CertVars C V) (p : C → ℝ)
    (B : Finset C) (c : C) :
    polynomial (dependencyGraph vars) p B =
      polynomial (dependencyGraph vars) p (compOf vars B c) *
        polynomial (dependencyGraph vars) p (B \ compOf vars B c) := by
  have h := polynomial_union (dependencyGraph vars) p (compOf vars B c)
    (B \ compOf vars B c)
    (Finset.disjoint_left.mpr (fun _ ha hb => (Finset.mem_sdiff.mp hb).2 ha))
    (not_adj_compOf_sdiff vars B c)
  rwa [Finset.union_sdiff_of_subset (compOf_subset vars B c)] at h

/-- Shearer's strict criterion is equivalent to checking every BDD component.
Each component check still includes all subsets of that component. -/
theorem strictCriterion_iff_components (vars : CertVars C V) (p : C → ℝ)
    (B : Finset C) :
    StrictCriterion (dependencyGraph vars) p B ↔
      ∀ c ∈ B, StrictCriterion (dependencyGraph vars) p (compOf vars B c) := by
  constructor
  · intro h c _
    exact StrictCriterion.mono (dependencyGraph vars) p h (compOf_subset vars B c)
  · intro hcomp T
    induction T using Finset.strongInductionOn with
    | _ T ih =>
      intro hTB
      by_cases hT : T = ∅
      · simp [hT]
      obtain ⟨c, hc⟩ := Finset.nonempty_iff_ne_empty.mpr hT
      have hcK := mem_compOf_self vars B c (hTB hc)
      have hsmall : T \ compOf vars B c ⊂ T := by
        apply Finset.ssubset_iff_subset_ne.mpr
        refine ⟨Finset.sdiff_subset, ?_⟩
        intro heq
        have hcsmall : c ∈ T \ compOf vars B c := heq.symm ▸ hc
        exact (Finset.mem_sdiff.mp hcsmall).2 hcK
      have hcross : ∀ a ∈ T ∩ compOf vars B c,
          ∀ b ∈ T \ compOf vars B c, ¬ (dependencyGraph vars).Adj a b := by
        intro a ha b hb
        exact not_adj_compOf_sdiff vars B c a (Finset.mem_inter.mp ha).2 b
          (Finset.mem_sdiff.mpr ⟨hTB (Finset.mem_sdiff.mp hb).1,
            (Finset.mem_sdiff.mp hb).2⟩)
      have hsplit : (T ∩ compOf vars B c) ∪ (T \ compOf vars B c) = T := by
        ext a
        simp only [Finset.mem_union, Finset.mem_inter, Finset.mem_sdiff]
        tauto
      have hpoly := polynomial_union (dependencyGraph vars) p
        (T ∩ compOf vars B c) (T \ compOf vars B c)
        (Finset.disjoint_left.mpr (fun _ ha hb =>
          (Finset.mem_sdiff.mp hb).2 (Finset.mem_inter.mp ha).2)) hcross
      rw [hsplit] at hpoly
      rw [hpoly]
      exact mul_pos (hcomp c (hTB hc) _ Finset.inter_subset_right)
        (ih _ hsmall (Finset.sdiff_subset.trans hTB))

end Shearer

#check @Shearer.dependencyGraph_adj_iff
#check @Shearer.not_adj_compOf_sdiff
#check @Shearer.polynomial_BDD_split
#check @Shearer.strictCriterion_iff_components
