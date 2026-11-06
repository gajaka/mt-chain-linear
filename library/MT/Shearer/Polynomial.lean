/-
  The signed independence polynomial used in the strict interior of Shearer's
  criterion. The deletion identity is Claim 2 of Harvey--Vondrak,
  "Short proofs for generalizations of the Lovasz Local Lemma:
  Shearer's condition and cluster expansion",
  arXiv:1711.06797. This file contains finite algebra only.
-/
module

public import Mathlib.Combinatorics.SimpleGraph.Basic
public import Mathlib.Algebra.BigOperators.Group.Finset.Powerset
public import Mathlib.Algebra.BigOperators.Ring.Finset
public import Mathlib.Data.Finset.Basic
public import Mathlib.Basic.Real.Basic
public import Mathlib.Tactic.Ring
public import Mathlib.Tactic.Tauto

@[expose] public section

set_option autoImplicit false
set_option linter.unusedSectionVars false

open Classical

namespace Shearer

variable {ι : Type*} [DecidableEq ι]

/-- Every pair of labels in the set is nonadjacent. -/
def Independent (G : SimpleGraph ι) (T : Finset ι) : Prop :=
  ∀ a ∈ T, ∀ b ∈ T, ¬ G.Adj a b

noncomputable def polynomial (G : SimpleGraph ι) (p : ι → ℝ)
    (T : Finset ι) : ℝ :=
  ∑ I ∈ T.powerset.filter (Independent G), ∏ i ∈ I, (-p i)

/-- The vertices remaining after deleting a label and its neighbors. -/
noncomputable def remote (G : SimpleGraph ι) (T : Finset ι) (a : ι) : Finset ι :=
  T.filter (fun b => b ≠ a ∧ ¬ G.Adj a b)

/-- Strict positivity on every subset, rather than only on the whole set. -/
def StrictCriterion (G : SimpleGraph ι) (p : ι → ℝ) (B : Finset ι) : Prop :=
  ∀ T ⊆ B, 0 < polynomial G p T

@[simp]
theorem independent_empty (G : SimpleGraph ι) : Independent G ∅ := by
  simp [Independent]

theorem Independent.mono (G : SimpleGraph ι) {S T : Finset ι}
    (h : Independent G T) (hST : S ⊆ T) : Independent G S := by
  intro a ha b hb
  exact h a (hST ha) b (hST hb)

theorem independent_insert (G : SimpleGraph ι) (a : ι) (T : Finset ι) :
    Independent G (insert a T) ↔ Independent G T ∧ ∀ b ∈ T, ¬ G.Adj a b := by
  constructor
  · intro h
    exact ⟨Independent.mono G h (Finset.subset_insert _ _),
      fun b hb => h a (Finset.mem_insert_self _ _) b (Finset.mem_insert_of_mem hb)⟩
  · rintro ⟨hT, ha⟩ b hb c hc
    rcases Finset.mem_insert.mp hb with hba | hbT
    · subst b
      rcases Finset.mem_insert.mp hc with hca | hcT
      · subst c
        exact G.irrefl
      · exact ha c hcT
    · rcases Finset.mem_insert.mp hc with hca | hcT
      · subst c
        exact fun h => ha b hbT h.symm
      · exact hT b hbT c hcT

@[simp]
theorem polynomial_empty (G : SimpleGraph ι) (p : ι → ℝ) :
    polynomial G p ∅ = 1 := by
  simp [polynomial, Finset.filter_singleton, Independent]

theorem remote_subset_erase (G : SimpleGraph ι) (T : Finset ι) (a : ι) :
    remote G T a ⊆ T.erase a := by
  intro b hb
  obtain ⟨hbT, hba, _⟩ := Finset.mem_filter.mp hb
  exact Finset.mem_erase.mpr ⟨hba, hbT⟩

theorem remote_subset (G : SimpleGraph ι) (T : Finset ι) (a : ι) :
    remote G T a ⊆ T :=
  (remote_subset_erase G T a).trans (Finset.erase_subset _ _)

theorem independent_insert_filter (G : SimpleGraph ι) (T : Finset ι) (a : ι)
    (ha : a ∉ T) :
    T.powerset.filter (fun I => Independent G (insert a I)) =
      (remote G T a).powerset.filter (Independent G) := by
  ext I
  simp only [Finset.mem_filter, Finset.mem_powerset, independent_insert]
  constructor
  · rintro ⟨hIT, hI, hadj⟩
    refine ⟨?_, hI⟩
    intro b hb
    exact Finset.mem_filter.mpr ⟨hIT hb, (fun h => ha (h ▸ hIT hb)), hadj b hb⟩
  · rintro ⟨hIR, hI⟩
    refine ⟨hIR.trans (remote_subset G T a), hI, ?_⟩
    intro b hb
    exact (Finset.mem_filter.mp (hIR hb)).2.2

theorem polynomial_insert (G : SimpleGraph ι) (p : ι → ℝ)
    (T : Finset ι) (a : ι) (ha : a ∉ T) :
    polynomial G p (insert a T) =
      polynomial G p T - p a * polynomial G p (remote G T a) := by
  calc
    polynomial G p (insert a T) = polynomial G p T +
        ∑ I ∈ T.powerset.filter (fun I => Independent G (insert a I)),
          ∏ i ∈ insert a I, (-p i) := by
      simp only [polynomial, Finset.sum_filter]
      exact Finset.sum_powerset_insert ha _
    _ = polynomial G p T + (-p a) * polynomial G p (remote G T a) := by
      rw [independent_insert_filter G T a ha]
      congr 1
      unfold polynomial
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro I hI
      have hsub := Finset.mem_powerset.mp (Finset.mem_filter.mp hI).1
      exact Finset.prod_insert (fun hi => ha (remote_subset G T a (hsub hi)))
    _ = polynomial G p T - p a * polynomial G p (remote G T a) := by ring

@[simp]
theorem remote_erase (G : SimpleGraph ι) (T : Finset ι) (a : ι) :
    remote G (T.erase a) a = remote G T a := by
  ext b
  simp only [remote, Finset.mem_filter, Finset.mem_erase]
  tauto

/-- The signed independence polynomial satisfies deletion of the closed neighborhood. -/
theorem polynomial_delete (G : SimpleGraph ι) (p : ι → ℝ)
    (T : Finset ι) (a : ι) (ha : a ∈ T) :
    polynomial G p T = polynomial G p (T.erase a) -
      p a * polynomial G p (remote G T a) := by
  simpa only [Finset.insert_erase ha, remote_erase] using
    polynomial_insert G p (T.erase a) a (Finset.notMem_erase a T)

/-- With no edge between the two parts, deleting a closed neighborhood
in the first part leaves the second part intact. -/
theorem remote_union (G : SimpleGraph ι) (S T : Finset ι) (a : ι)
    (haT : a ∉ T) (hcross : ∀ b ∈ T, ¬ G.Adj a b) :
    remote G (S ∪ T) a = remote G S a ∪ T := by
  ext b
  simp only [remote, Finset.mem_filter, Finset.mem_union]
  constructor
  · rintro ⟨hbS | hbT, hba, hab⟩
    · exact Or.inl ⟨hbS, hba, hab⟩
    · exact Or.inr hbT
  · rintro (⟨hbS, hba, hab⟩ | hbT)
    · exact ⟨Or.inl hbS, hba, hab⟩
    · exact ⟨Or.inr hbT, (fun h => haT (h ▸ hbT)), hcross b hbT⟩

/-- The polynomial factors over disjoint sets with no edges between them. -/
theorem polynomial_union (G : SimpleGraph ι) (p : ι → ℝ)
    (S T : Finset ι) (hdis : Disjoint S T)
    (hcross : ∀ a ∈ S, ∀ b ∈ T, ¬ G.Adj a b) :
    polynomial G p (S ∪ T) = polynomial G p S * polynomial G p T := by
  induction S using Finset.strongInductionOn generalizing T with
  | _ S ih =>
    by_cases hS : S = ∅
    · simp [hS]
    obtain ⟨a, ha⟩ := Finset.nonempty_iff_ne_empty.mpr hS
    have haT : a ∉ T := fun hat => Finset.disjoint_left.mp hdis ha hat
    have herase : (S ∪ T).erase a = S.erase a ∪ T := by
      ext b
      simp only [Finset.mem_erase, Finset.mem_union]
      constructor
      · rintro ⟨hba, hbS | hbT⟩
        · exact Or.inl ⟨hba, hbS⟩
        · exact Or.inr hbT
      · rintro (⟨hba, hbS⟩ | hbT)
        · exact ⟨hba, Or.inl hbS⟩
        · exact ⟨(fun h => haT (h ▸ hbT)), Or.inr hbT⟩
    have hrec1 := ih (S.erase a) (Finset.erase_ssubset ha) T
      (hdis.mono_left (Finset.erase_subset _ _))
      (fun b hb c hc => hcross b (Finset.erase_subset _ _ hb) c hc)
    have hrec2 := ih (remote G S a)
      (lt_of_le_of_lt (remote_subset_erase G S a) (Finset.erase_ssubset ha)) T
      (hdis.mono_left (remote_subset G S a))
      (fun b hb c hc => hcross b (remote_subset G S a hb) c hc)
    rw [polynomial_delete G p (S ∪ T) a (Finset.mem_union_left T ha), herase,
      remote_union G S T a haT (hcross a ha), hrec1, hrec2,
      polynomial_delete G p S a ha]
    ring

/-- Strict positivity is inherited by a smaller finite set. -/
theorem StrictCriterion.mono (G : SimpleGraph ι) (p : ι → ℝ)
    {S T : Finset ι} (hT : StrictCriterion G p T) (hST : S ⊆ T) :
    StrictCriterion G p S := by
  intro U hUS
  exact hT U (hUS.trans hST)

/-- Independent components satisfy the strict criterion exactly when each
component does. This assertion requires positivity on every subset. -/
theorem strictCriterion_union_iff (G : SimpleGraph ι) (p : ι → ℝ)
    (S T : Finset ι) (hdis : Disjoint S T)
    (hcross : ∀ a ∈ S, ∀ b ∈ T, ¬ G.Adj a b) :
    StrictCriterion G p (S ∪ T) ↔ StrictCriterion G p S ∧ StrictCriterion G p T := by
  constructor
  · intro h
    exact ⟨StrictCriterion.mono G p h Finset.subset_union_left,
      StrictCriterion.mono G p h Finset.subset_union_right⟩
  · rintro ⟨hS, hT⟩ U hU
    have hsplit : U = (U ∩ S) ∪ (U ∩ T) := by
      ext a
      simp only [Finset.mem_union, Finset.mem_inter]
      constructor
      · intro ha
        rcases Finset.mem_union.mp (hU ha) with haS | haT
        · exact Or.inl ⟨ha, haS⟩
        · exact Or.inr ⟨ha, haT⟩
      · rintro (⟨ha, _⟩ | ⟨ha, _⟩) <;> exact ha
    have hpoly := polynomial_union G p (U ∩ S) (U ∩ T)
      (hdis.mono Finset.inter_subset_right Finset.inter_subset_right)
      (fun a ha b hb => hcross a (Finset.mem_inter.mp ha).2 b
        (Finset.mem_inter.mp hb).2)
    rw [hsplit, hpoly]
    exact mul_pos (hS _ Finset.inter_subset_right) (hT _ Finset.inter_subset_right)

end Shearer

#check @Shearer.independent_empty
#check @Shearer.Independent.mono
#check @Shearer.independent_insert
#check @Shearer.polynomial_empty
#check @Shearer.remote_subset_erase
#check @Shearer.remote_subset
#check @Shearer.independent_insert_filter
#check @Shearer.polynomial_insert
#check @Shearer.remote_erase
#check @Shearer.polynomial_delete

#check @Shearer.remote_union
#check @Shearer.polynomial_union
#check @Shearer.StrictCriterion.mono
#check @Shearer.strictCriterion_union_iff
