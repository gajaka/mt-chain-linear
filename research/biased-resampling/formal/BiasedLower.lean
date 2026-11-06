module

public import AdaptiveWork
public import GenericLower

@[expose] public section

set_option autoImplicit false

namespace MTChainFormal.BiasedResampling

open scoped BigOperators ENNReal

noncomputable def defectCount {n : ℕ} (s : ChainState n) : ℝ :=
  (badIndices s).card

theorem defectCount_nonneg {n : ℕ} (s : ChainState n) : 0 ≤ defectCount s := by
  exact Nat.cast_nonneg _

theorem badIndices_of_good {n : ℕ} (s : ChainState n) (hg : firstFailure s = none) :
    badIndices s = ∅ := by
  apply Finset.eq_empty_iff_forall_notMem.mpr
  intro i hi
  have ht := (no_failure_iff s).mp hg i
  have hf := (mem_badIndices s i).mp hi
  simp [ht] at hf

theorem defectCount_le_active {n : ℕ} (s : ChainState n) :
    defectCount s ≤ (n : ℝ) * rawActiveCost s := by
  by_cases hg : firstFailure s = none
  · simp [defectCount, badIndices_of_good s hg, rawActiveCost, hg]
  · have h : (badIndices s).card ≤ n :=
      (Finset.card_le_univ _).trans_eq (Fintype.card_fin n)
    simpa [defectCount, rawActiveCost, hg] using (Nat.cast_le.mpr h :
      ((badIndices s).card : ℝ) ≤ (n : ℝ))

/-- Only the selected certificate and its two neighbours can be repaired
    by one original full-footprint update. -/
theorem replacement_count_drop {n : ℕ} (hn : 2 ≤ n)
    (s : ChainState n) (i : Fin n) (u : Draw) :
    (badIndices s).card ≤ (badIndices (replace s i u)).card + 3 := by
  classical
  let near : Finset (Fin n) := Finset.univ.filter
    (fun j => i.val ≤ j.val + 1 ∧ j.val ≤ i.val + 1)
  have hnear : (near.image Fin.val) ⊆ {i.val - 1, i.val, i.val + 1} := by
    intro k hk
    obtain ⟨j, hj, rfl⟩ := Finset.mem_image.mp hk
    have hj' := (Finset.mem_filter.mp hj).2
    simp only [Finset.mem_insert, Finset.mem_singleton]
    omega
  have hc : near.card ≤ 3 := by
    rw [← Finset.card_image_of_injective near Fin.val_injective]
    exact (Finset.card_le_card hnear).trans Finset.card_le_three
  have hs : badIndices s ⊆ badIndices (replace s i u) ∪ near := by
    intro j hj
    by_cases ht : j ∈ badIndices (replace s i u)
    · exact Finset.mem_union_left _ ht
    · apply Finset.mem_union_right
      apply Finset.mem_filter.mpr
      refine ⟨Finset.mem_univ j, ?_⟩
      have hnotfar : ¬ (j.val + 1 < i.val ∨ i.val + 1 < j.val) := by
        intro hfar
        apply ht
        rw [mem_badIndices, replace_pass_unchanged hn s i j u hfar]
        exact (mem_badIndices s j).mp hj
      omega
  exact (Finset.card_le_card hs).trans
    ((Finset.card_union_le _ _).trans (Nat.add_le_add_left hc _))

theorem static_defect_step {n : ℕ} (hn : 2 ≤ n) (s : ChainState n) (u : Draw) :
    defectCount s ≤ 3 * rawActiveCost s + defectCount (staticStep s u) := by
  cases hi : firstFailure s with
  | none => simp [staticStep, hi, rawActiveCost, defectCount, badIndices_of_good s hi]
  | some i =>
      have h := replacement_count_drop hn s i u
      have hr : ((badIndices s).card : ℝ) ≤
          ((badIndices (replace s i u)).card : ℝ) + 3 := by exact_mod_cast h
      simpa [staticStep, hi, rawActiveCost, defectCount, add_comm] using hr

theorem static_defect_expectation {n : ℕ} (hn : 2 ≤ n) (p : AdmissibleBias)
    (s : ChainState n) :
    defectCount s ≤ 3 * rawActiveCost s + expect (staticKernel p n) defectCount s := by
  have h := average_mono p.val (le_trans (by norm_num) p.property.1) p.property.2
    (static_defect_step hn s)
  rw [average_const, average_add, average_const] at h
  rw [expect_staticKernel]
  exact h

theorem static_supersolution {n : ℕ} (hn : 2 ≤ n) (p : AdmissibleBias)
    (s : ChainState n) :
    rawActiveCost s + expect (staticKernel p n) potential s ≤ potential s := by
  rw [expect_staticKernel]
  cases hi : firstFailure s with
  | none => simp [staticStep, hi, rawActiveCost, average_const]
  | some i =>
      simpa [staticStep, hi, rawActiveCost] using pointwise_drift hn p.val
        p.property.1 p.property.2 s i (selected_failed s i hi)

theorem static_initial_steps_ge_defects {n : ℕ} (hn : 2 ≤ n) (p : AdmissibleBias)
    (q : ℝ) (hq0 : 0 ≤ q) (hq1 : q ≤ 1) :
    ENNReal.ofReal ((∑ s : ChainState n, initialWeight q s * defectCount s) / 3) ≤
      initialTotalWork (staticKernel p n) (initialWeight q) rawActiveCost := by
  exact initial_steps_ge_count (staticKernel p n) (initialWeight q) rawActiveCost
    defectCount potential (initialWeight_nonneg q hq0 hq1) rawActiveCost_nonneg
    defectCount_nonneg potential_nonneg (static_supersolution hn p)
    (static_defect_expectation hn p) n defectCount_le_active

end MTChainFormal.BiasedResampling
