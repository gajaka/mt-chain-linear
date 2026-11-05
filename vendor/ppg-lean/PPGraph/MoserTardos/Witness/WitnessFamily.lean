/-
  PPGraphMoserTardosWitnessFamily.lean

  The unbounded canonical witness family is the increasing union of
  the finite enumerations wtreesUpTo. Its total ENNReal weight is the
  supremum of the finite-depth mtWeight values.

  Restricting the sum to this family is essential: summing over all
  rooted ordered WTree values would also count sibling permutations.
  The depth-uniform algebraic convergence bound therefore controls
  the full canonical-family sum without assuming convergence first.
-/

module

public import PPGraph.MoserTardos.Bounds.WeightSum
public import PPGraph.MoserTardos.Bounds.Convergence
public import Mathlib.Topology.Algebra.InfiniteSum.ENNReal
public import Mathlib.Basic.ENNReal.BigOperators

@[expose] public section

open Classical
open scoped NNReal ENNReal

variable {V : Type} [DecidableEq V] {S : VarSpaces V} {ι : Type}
    [Fintype ι] [DecidableEq ι]

/-- Canonical witnesses rooted at `α`, with no fixed depth bound. -/
def witnessFamily (P : MTProcess S ι) (α : ι) : Set (WTree ι) :=
  {U | ∃ D : ℕ, U ∈ wtreesUpTo P D α}

/-- The tree weight on the canonical family, extended by zero to all
    ordered witness trees. -/
noncomputable def witnessFamilyWeight (P : MTProcess S ι) (p : ι → ℝ≥0)
    (α : ι) (U : WTree ι) : ℝ≥0∞ :=
  (witnessFamily P α).indicator (fun T => (T.weight p : ℝ≥0∞)) U

omit [DecidableEq V] in
@[simp]
theorem witnessFamilyWeight_of_mem (P : MTProcess S ι) (p : ι → ℝ≥0)
    (α : ι) (U : WTree ι) (hU : U ∈ witnessFamily P α) :
    witnessFamilyWeight P p α U = (U.weight p : ℝ≥0∞) := by
  simp [witnessFamilyWeight, hU]

omit [DecidableEq V] in
@[simp]
theorem witnessFamilyWeight_of_not_mem (P : MTProcess S ι) (p : ι → ℝ≥0)
    (α : ι) (U : WTree ι) (hU : U ∉ witnessFamily P α) :
    witnessFamilyWeight P p α U = 0 := by
  simp [witnessFamilyWeight, hU]

/-- Every finite selection from the unbounded canonical family fits
    inside one finite-depth enumeration. -/
theorem exists_wtreesUpTo_superset (P : MTProcess S ι) (α : ι)
    (F : Finset (WTree ι)) (hF : ∀ U ∈ F, U ∈ witnessFamily P α) :
    ∃ D : ℕ, F ⊆ wtreesUpTo P D α := by
  classical
  revert hF
  induction F using Finset.induction_on with
  | empty =>
    intro _
    exact ⟨0, Finset.empty_subset _⟩
  | insert U F _hnot ih =>
    intro hF
    obtain ⟨d, hd⟩ := hF U (Finset.mem_insert_self U F)
    obtain ⟨D, hD⟩ := ih (fun T hT => hF T (Finset.mem_insert_of_mem hT))
    refine ⟨max d D, ?_⟩
    intro T hT
    rcases Finset.mem_insert.mp hT with hTU | hTF
    · subst T
      exact wtreesUpTo_mono_le P d (max d D) α (le_max_left _ _) hd
    · exact wtreesUpTo_mono_le P D (max d D) α (le_max_right _ _) (hD hTF)

/-- At finite depth, extending by zero does not alter the established
    tree-enumeration weight identity. -/
theorem sum_wtreesUpTo_witnessFamilyWeight (P : MTProcess S ι)
    (p : ι → ℝ≥0) (α : ι) (D : ℕ) :
    (∑ U ∈ wtreesUpTo P D α, witnessFamilyWeight P p α U) =
      (mtWeight P p D α : ℝ≥0∞) := by
  calc
    (∑ U ∈ wtreesUpTo P D α, witnessFamilyWeight P p α U) =
        ∑ U ∈ wtreesUpTo P D α, (U.weight p : ℝ≥0∞) := by
      apply Finset.sum_congr rfl
      intro U hU
      exact witnessFamilyWeight_of_mem P p α U ⟨D, hU⟩
    _ = (mtWeight P p D α : ℝ≥0∞) := by
      rw [← ENNReal.ofNNReal_finsetSum, sum_wtreesUpTo_weight P p D α]

/-- Summing over all depths means taking the supremum of the
    finite-depth sums, rather than selecting one fixed depth. -/
theorem tsum_witnessFamilyWeight_eq_iSup_mtWeight (P : MTProcess S ι)
    (p : ι → ℝ≥0) (α : ι) :
    (∑' U : WTree ι, witnessFamilyWeight P p α U) =
      ⨆ D : ℕ, (mtWeight P p D α : ℝ≥0∞) := by
  classical
  apply le_antisymm
  · rw [ENNReal.tsum_eq_iSup_sum]
    apply iSup_le
    intro F
    let G : Finset (WTree ι) := F.filter (fun U => U ∈ witnessFamily P α)
    have hG : ∀ U ∈ G, U ∈ witnessFamily P α := by
      intro U hU
      exact (Finset.mem_filter.mp hU).2
    obtain ⟨D, hD⟩ := exists_wtreesUpTo_superset P α G hG
    calc
      (∑ U ∈ F, witnessFamilyWeight P p α U) =
          ∑ U ∈ G, (U.weight p : ℝ≥0∞) := by
        simp only [G, witnessFamilyWeight, Set.indicator_apply, Finset.sum_filter]
      _ ≤ ∑ U ∈ wtreesUpTo P D α, (U.weight p : ℝ≥0∞) :=
        Finset.sum_le_sum_of_subset hD
      _ = (mtWeight P p D α : ℝ≥0∞) := by
        rw [← ENNReal.ofNNReal_finsetSum, sum_wtreesUpTo_weight P p D α]
      _ ≤ ⨆ d : ℕ, (mtWeight P p d α : ℝ≥0∞) :=
        le_iSup (fun d : ℕ => (mtWeight P p d α : ℝ≥0∞)) D
  · apply iSup_le
    intro D
    calc
      (mtWeight P p D α : ℝ≥0∞) =
          ∑ U ∈ wtreesUpTo P D α, witnessFamilyWeight P p α U :=
        (sum_wtreesUpTo_witnessFamilyWeight P p α D).symm
      _ ≤ ∑' U : WTree ι, witnessFamilyWeight P p α U :=
        ENNReal.sum_le_tsum (wtreesUpTo P D α)

/-- The algebraic MT budget bounds the entire canonical-family sum. -/
theorem tsum_witnessFamilyWeight_le (P : MTProcess S ι) (p x : ι → ℝ≥0)
    (h_dom : ∀ α, p α ≤ x α)
    (h_self : ∀ α, p α * ∏ β ∈ plusNeighbors P α, (1 + x β) ≤ x α)
    (α : ι) :
    (∑' U : WTree ι, witnessFamilyWeight P p α U) ≤ (x α : ℝ≥0∞) := by
  rw [tsum_witnessFamilyWeight_eq_iSup_mtWeight P p α]
  apply iSup_le
  intro D
  exact ENNReal.coe_le_coe.mpr (mtWeight_le P p x h_dom h_self D α)

-- -------------------------------------------------------------------
-- Verification
-- -------------------------------------------------------------------

#check @witnessFamily
#check @witnessFamilyWeight
#check @witnessFamilyWeight_of_mem
#check @witnessFamilyWeight_of_not_mem
#check @exists_wtreesUpTo_superset
#check @sum_wtreesUpTo_witnessFamilyWeight
#check @tsum_witnessFamilyWeight_eq_iSup_mtWeight
#check @tsum_witnessFamilyWeight_le
