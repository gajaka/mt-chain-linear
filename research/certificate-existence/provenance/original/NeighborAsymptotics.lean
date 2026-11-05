import NeighborBase
import Mathlib.Analysis.Asymptotics.Basic

set_option autoImplicit false

namespace NeighborSeparation

theorem floor_budget_quadratic_lower {n : ℕ} (hn : 10 ≤ n) :
    (n : ℝ) ^ 2 / 1248 ≤ (((n - 4) ^ 2 / 4 : ℕ) : ℝ) / 78 := by
  let m := n - 4
  let q := m ^ 2 / 4
  have hm : 6 ≤ m := by dsimp [m]; omega
  have hnm : n = m + 4 := by dsimp [m]; omega
  have hquot : m ^ 2 ≤ 4 * q + 3 := by
    have hmod := Nat.mod_lt (m ^ 2) (by decide : 0 < 4)
    have hsum := Nat.mod_add_div (m ^ 2) 4
    dsimp [q]
    omega
  have hmreal : (6 : ℝ) ≤ m := by exact_mod_cast hm
  have hnmreal : (n : ℝ) = (m : ℝ) + 4 := by exact_mod_cast hnm
  have hquotreal : (m : ℝ) ^ 2 ≤ 4 * (q : ℝ) + 3 := by exact_mod_cast hquot
  change (n : ℝ) ^ 2 / 1248 ≤ (q : ℝ) / 78
  nlinarith [sq_nonneg ((m : ℝ) - 6)]

theorem quadratic_lower_isBigO (b : ℕ → ℝ)
    (hb : ∀ᶠ n : ℕ in Filter.atTop, (n : ℝ) ^ 2 / 1248 ≤ b n) :
    Asymptotics.IsBigO Filter.atTop (fun n : ℕ => (n : ℝ) ^ 2) b := by
  refine Asymptotics.isBigO_iff.mpr ⟨1248, ?_⟩
  filter_upwards [hb] with n hn
  have hnonneg : 0 ≤ b n := le_trans (by positivity) hn
  rw [Real.norm_of_nonneg (by positivity : (0 : ℝ) ≤ (n : ℝ) ^ 2),
    Real.norm_of_nonneg hnonneg]
  linarith

theorem quadratic_lower_not_linear (b : ℕ → ℝ)
    (hb : ∀ᶠ n : ℕ in Filter.atTop, (n : ℝ) ^ 2 / 1248 ≤ b n) :
    ¬ Asymptotics.IsBigO Filter.atTop b (fun n : ℕ => (n : ℝ)) := by
  intro hbig
  obtain ⟨C, hC, hevent⟩ := Asymptotics.isBigO_iff'.mp hbig
  obtain ⟨N, hN⟩ := Filter.eventually_atTop.mp (hb.and hevent)
  obtain ⟨M, hM⟩ := exists_nat_gt (1248 * C)
  let n := max N M
  have hnN : N ≤ n := le_max_left _ _
  have hnM : M ≤ n := le_max_right _ _
  have hlarge : 1248 * C < (n : ℝ) := lt_of_lt_of_le hM (by exact_mod_cast hnM)
  have hnpos : (0 : ℝ) < n := by linarith
  obtain ⟨hlow, hupp⟩ := hN n hnN
  have hnonneg : 0 ≤ b n := le_trans (by positivity) hlow
  rw [Real.norm_of_nonneg hnonneg, Real.norm_of_nonneg (Nat.cast_nonneg n)] at hupp
  have hprod := mul_pos hnpos (sub_pos.mpr hlarge)
  nlinarith

end NeighborSeparation

#print axioms NeighborSeparation.floor_budget_quadratic_lower
#print axioms NeighborSeparation.quadratic_lower_not_linear
