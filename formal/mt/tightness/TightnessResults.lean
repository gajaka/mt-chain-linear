module

public import LinearPotential
public import LinearAsymptotics
public import LowerBound

@[expose] public section

set_option autoImplicit false

namespace MTChainFormal.Tightness

open scoped ENNReal

/-- Matching growth order for the original initialized operation count. -/
theorem linear_work_bounds {n : ℕ} (hn : 2 ≤ n) :
    ENNReal.ofReal ((n : ℝ) / 18) ≤ expectedSteps n ∧
      expectedSteps n ≤ ENNReal.ofReal (1054 * (n : ℝ)) :=
  ⟨expected_steps_ge_linear hn, expected_steps_le_linear hn⟩

/-- In particular no positive quadratic lower bound can hold eventually. -/
theorem no_positive_quadratic_lower_bound :
    ¬ ∃ c : ℝ, ∃ N : ℕ, 0 < c ∧ ∀ n : ℕ, N ≤ n →
      ENNReal.ofReal (c * (n : ℝ)^2) ≤ expectedSteps n := by
  rintro ⟨c, N, hc, hlower⟩
  obtain ⟨m, hm⟩ := exists_nat_gt (1054 / c)
  let n : ℕ := max 2 (max N m)
  have hn : 2 ≤ n := le_max_left _ _
  have hN : N ≤ n := le_trans (le_max_left _ _) (le_max_right _ _)
  have hmN : m ≤ n := le_trans (le_max_right _ _) (le_max_right _ _)
  have hnr : (0 : ℝ) < n := by exact_mod_cast (lt_of_lt_of_le (by omega : 0 < 2) hn)
  have hmn : (m : ℝ) ≤ n := by exact_mod_cast hmN
  have hlarge : 1054 < c * (n : ℝ) := by
    have he := (div_lt_iff₀ hc).mp (lt_of_lt_of_le hm hmn)
    nlinarith
  have hcomp := le_trans (hlower n hN) (expected_steps_le_linear hn)
  have hreal : c * (n : ℝ)^2 ≤ 1054 * (n : ℝ) := by
    exact (ENNReal.ofReal_le_ofReal_iff (by positivity)).mp hcomp
  nlinarith [mul_pos (sub_pos.mpr hlarge) hnr]

end MTChainFormal.Tightness
