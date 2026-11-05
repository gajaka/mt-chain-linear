/-
  PPGraphBDDPartition.lean

  The distinct finite BDD components partition the chosen event family B.
  This file uses the existing compOf relation directly, without importing
  the spectral connected-component machinery. Its sum identity applies to
  counts, expectations, and real budgets alike.
-/

module

public import PPGraph.Dependency.Decomposition

@[expose] public section

set_option autoImplicit false

open Classical

variable {C V : Type} [DecidableEq C] [DecidableEq V]

/-- Any member of a component indexes that same component. -/
theorem compOf_eq_of_mem_compOf (vars : CertVars C V) (B : Finset C)
    (c a : C) (ha : a ∈ compOf vars B c) :
    compOf vars B a = compOf vars B c :=
  (compOf_eq_of_sameComponent vars B c a (Finset.mem_filter.mp ha).2).symm

#check @compOf_eq_of_mem_compOf

/-- Taking each distinct component once covers exactly B. -/
theorem compOf_groups_biUnion (vars : CertVars C V) (B : Finset C) :
    (B.image (compOf vars B)).biUnion id = B := by
  ext a
  constructor
  · intro ha
    obtain ⟨K, hK, haK⟩ := Finset.mem_biUnion.mp ha
    obtain ⟨c, _, rfl⟩ := Finset.mem_image.mp hK
    exact compOf_subset vars B c haK
  · intro ha
    exact Finset.mem_biUnion.mpr ⟨compOf vars B a,
      Finset.mem_image_of_mem _ ha, mem_compOf_self vars B a ha⟩

#check @compOf_groups_biUnion

/-- Distinct component groups are disjoint, so their sums do not double-count. -/
theorem compOf_groups_pairwise_disjoint (vars : CertVars C V) (B : Finset C) :
    ∀ K ∈ B.image (compOf vars B), ∀ L ∈ B.image (compOf vars B),
      K ≠ L → Disjoint K L := by
  intro K hK L hL hne
  obtain ⟨c, _, rfl⟩ := Finset.mem_image.mp hK
  obtain ⟨d, _, rfl⟩ := Finset.mem_image.mp hL
  apply Finset.disjoint_left.mpr
  intro a hac had
  exact hne ((compOf_eq_of_mem_compOf vars B c a hac).symm.trans
    (compOf_eq_of_mem_compOf vars B d a had))

#check @compOf_groups_pairwise_disjoint

/-- Summing over distinct BDD components is exactly summing over B. -/
theorem sum_compOf_groups {M : Type*} [AddCommMonoid M]
    (vars : CertVars C V) (B : Finset C) (f : C → M) :
    (∑ K ∈ B.image (compOf vars B), ∑ a ∈ K, f a) = ∑ a ∈ B, f a := by
  calc
    (∑ K ∈ B.image (compOf vars B), ∑ a ∈ K, f a) =
        ∑ a ∈ (B.image (compOf vars B)).biUnion id, f a :=
      (Finset.sum_biUnion (f := f) (compOf_groups_pairwise_disjoint vars B)).symm
    _ = ∑ a ∈ B, f a := by rw [compOf_groups_biUnion vars B]

#check @sum_compOf_groups
