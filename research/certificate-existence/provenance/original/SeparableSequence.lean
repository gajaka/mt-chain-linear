import SeparableBase
import Mathlib.Analysis.Asymptotics.Basic

set_option autoImplicit false

namespace PotentialSeparation

open scoped BigOperators

theorem abs_contrast_le_oscillation (f : ThresholdCosts) (j : ℕ) :
    |contrast f j| ≤ oscillation f j := by
  have h0 : f j 0 ∈ Finset.univ.image (f j) := Finset.mem_image_of_mem _ (Finset.mem_univ _)
  have h2 : f j 2 ∈ Finset.univ.image (f j) := Finset.mem_image_of_mem _ (Finset.mem_univ _)
  have hmin0 := Finset.min'_le _ _ h0
  have hmin2 := Finset.min'_le _ _ h2
  have hmax0 := Finset.le_max' _ _ h0
  have hmax2 := Finset.le_max' _ _ h2
  unfold contrast oscillation
  exact abs_le.mpr ⟨by linarith, by linarith⟩

/-- A telescoped adjacent decrease. -/
theorem sequence_span (a : ℕ → ℝ) (K : ℝ) (r : ℕ) :
    (∀ j < r, K ≤ a j - a (j + 1)) → K * (r : ℝ) ≤ a 0 - a r := by
  induction r with
  | zero => intro _; simp
  | succ r ih =>
      intro h
      have hprev := ih (fun j hj => h j (by omega))
      have hlast := h r (by omega)
      push_cast
      nlinarith

/-- Pairing endpoints and deleting them proves the exact floor-square bound.
    The majorant b may be any bound on the absolute value of a. -/
theorem sequence_absolute_budget (m : ℕ) :
    ∀ (a b : ℕ → ℝ) (K : ℝ),
      (∀ j < m, |a j| ≤ b j) →
      (∀ j, j + 1 < m → K ≤ a j - a (j + 1)) →
      K * ((m ^ 2 / 4 : ℕ) : ℝ) ≤ ∑ j ∈ Finset.range m, b j := by
  induction m using Nat.strong_induction_on with
  | h m ih =>
      intro a b K hb hg
      by_cases hm : m < 2
      · interval_cases m
        · simp
        · have h := hb 0 (by omega)
          have ha := abs_nonneg (a 0)
          simp
          linarith
      · obtain ⟨k, rfl⟩ : ∃ k, m = k + 2 := ⟨m - 2, by omega⟩
        have hmid := ih k (by omega) (fun j => a (j + 1)) (fun j => b (j + 1)) K
          (by intro j hj; exact hb (j + 1) (by omega))
          (by intro j hj; exact hg (j + 1) (by omega))
        have hend := sequence_span a K (k + 1) (by
          intro j hj
          exact hg j (by omega))
        have hb0 := hb 0 (by omega)
        have hblast := hb (k + 1) (by omega)
        have hleft : a 0 ≤ b 0 := le_trans (le_abs_self _) hb0
        have hright : -a (k + 1) ≤ b (k + 1) :=
          le_trans (neg_le_abs _) hblast
        have hdiv : (k + 2) ^ 2 / 4 = k ^ 2 / 4 + k + 1 := by
          have heq : (k + 2) ^ 2 = k ^ 2 + 4 * (k + 1) := by ring
          omega
        have hsum : (∑ j ∈ Finset.range (k + 2), b j) =
            b 0 + (∑ j ∈ Finset.range k, b (j + 1)) + b (k + 1) := by
          rw [Finset.sum_range_succ, Finset.sum_range_succ']
          ring
        rw [hdiv, hsum]
        push_cast at hend
        push_cast
        nlinarith

theorem gradient_oscillation_lower {n : ℕ} (f : ThresholdCosts) (δ : ℝ)
    (hgrad : ∀ j, 1 ≤ j → j + 1 ≤ n - 2 →
      3 * δ ≤ contrast f j - contrast f (j + 1)) :
    3 * δ * (((n - 2) ^ 2 / 4 : ℕ) : ℝ) ≤
      ∑ j : Fin (n - 2), oscillation f (j.val + 1) := by
  have h := sequence_absolute_budget (n - 2)
    (fun j => contrast f (j + 1)) (fun j => oscillation f (j + 1)) (3 * δ)
    (by intro j _; exact abs_contrast_le_oscillation f (j + 1))
    (by intro j hj; exact hgrad (j + 1) (by omega) (by omega))
  rw [Fin.sum_univ_eq_sum_range (fun j => oscillation f (j + 1)) (n - 2)]
  exact h

/-- A coarse explicit quadratic lower envelope for the exact floor budget. -/
theorem floor_budget_quadratic_lower {n : ℕ} (hn : 8 ≤ n) :
    (n : ℝ) ^ 2 / 384 ≤ (((n - 2) ^ 2 / 4 : ℕ) : ℝ) / 12 := by
  let m := n - 2
  let q := m ^ 2 / 4
  have hm : 6 ≤ m := by dsimp [m]; omega
  have hnm : n = m + 2 := by dsimp [m]; omega
  have hquot : m ^ 2 ≤ 4 * q + 3 := by
    have hmod := Nat.mod_lt (m ^ 2) (by decide : 0 < 4)
    have hsum := Nat.mod_add_div (m ^ 2) 4
    dsimp [q]
    omega
  have hmreal : (6 : ℝ) ≤ m := by exact_mod_cast hm
  have hnmreal : (n : ℝ) = (m : ℝ) + 2 := by exact_mod_cast hnm
  have hquotreal : (m : ℝ) ^ 2 ≤ 4 * (q : ℝ) + 3 := by exact_mod_cast hquot
  change (n : ℝ) ^ 2 / 384 ≤ (q : ℝ) / 12
  nlinarith [sq_nonneg ((m : ℝ) - 6)]

theorem eventually_floor_budget_quadratic_lower :
    ∀ᶠ n : ℕ in Filter.atTop,
      (n : ℝ) ^ 2 / 384 ≤ (((n - 2) ^ 2 / 4 : ℕ) : ℝ) / 12 := by
  exact Filter.eventually_atTop.mpr ⟨8, fun n hn => floor_budget_quadratic_lower hn⟩

theorem quadratic_lower_isBigO (b : ℕ → ℝ)
    (hb : ∀ᶠ n : ℕ in Filter.atTop, (n : ℝ) ^ 2 / 384 ≤ b n) :
    Asymptotics.IsBigO Filter.atTop (fun n : ℕ => (n : ℝ) ^ 2) b := by
  refine Asymptotics.isBigO_iff.mpr ⟨384, ?_⟩
  filter_upwards [hb] with n hn
  have hnonneg : 0 ≤ b n := le_trans (by positivity) hn
  rw [Real.norm_of_nonneg (by positivity : (0 : ℝ) ≤ (n : ℝ) ^ 2),
    Real.norm_of_nonneg hnonneg]
  linarith

theorem quadratic_lower_not_linear (b : ℕ → ℝ)
    (hb : ∀ᶠ n : ℕ in Filter.atTop, (n : ℝ) ^ 2 / 384 ≤ b n) :
    ¬ Asymptotics.IsBigO Filter.atTop b (fun n : ℕ => (n : ℝ)) := by
  intro hbig
  obtain ⟨C, hC, hevent⟩ := Asymptotics.isBigO_iff'.mp hbig
  obtain ⟨N, hN⟩ := Filter.eventually_atTop.mp (hb.and hevent)
  obtain ⟨M, hM⟩ := exists_nat_gt (384 * C)
  let n := max N M
  have hnN : N ≤ n := le_max_left _ _
  have hnM : M ≤ n := le_max_right _ _
  have hlarge : 384 * C < (n : ℝ) := lt_of_lt_of_le hM (by exact_mod_cast hnM)
  have hnpos : (0 : ℝ) < n := by linarith
  obtain ⟨hlow, hupp⟩ := hN n hnN
  have hnonneg : 0 ≤ b n := le_trans (by positivity) hlow
  rw [Real.norm_of_nonneg hnonneg, Real.norm_of_nonneg (Nat.cast_nonneg n)] at hupp
  have hprod := mul_pos hnpos (sub_pos.mpr hlarge)
  nlinarith

end PotentialSeparation

#print axioms PotentialSeparation.gradient_oscillation_lower
#print axioms PotentialSeparation.floor_budget_quadratic_lower
#print axioms PotentialSeparation.quadratic_lower_not_linear
