import LinearPotential
import LowerBound
import Mathlib.Analysis.Asymptotics.SpecificAsymptotics

set_option autoImplicit false

namespace MTChainFormal.Tightness

open Filter Asymptotics

/-- The upper operation bound as a finite real expectation. -/
theorem expected_steps_toReal_le_linear {n : ℕ} (hn : 2 ≤ n) :
    (expectedSteps n).toReal ≤ 1054 * (n : ℝ) := by
  have h := ENNReal.toReal_mono ENNReal.ofReal_ne_top (expected_steps_le_linear hn)
  simpa only [ENNReal.toReal_ofReal (by positivity : (0 : ℝ) ≤ 1054 * (n : ℝ))] using h

/-- The counting lower bound as a finite real expectation. -/
theorem expected_steps_toReal_ge_linear {n : ℕ} (hn : 2 ≤ n) :
    (n : ℝ) / 18 ≤ (expectedSteps n).toReal :=
  (ENNReal.ofReal_le_iff_le_toReal (expected_steps_finite hn).ne).mp
    (expected_steps_ge_linear hn)

theorem expected_steps_isBigO_linear :
    IsBigO atTop (fun n : ℕ => (expectedSteps n).toReal) (fun n : ℕ => (n : ℝ)) := by
  apply IsBigO.of_bound 1054
  filter_upwards [eventually_ge_atTop 2] with n hn
  simpa only [Real.norm_eq_abs, abs_of_nonneg ENNReal.toReal_nonneg,
    abs_of_nonneg (show (0 : ℝ) ≤ (n : ℝ) from Nat.cast_nonneg n)] using
      expected_steps_toReal_le_linear hn

theorem linear_isBigO_expected_steps :
    IsBigO atTop (fun n : ℕ => (n : ℝ)) (fun n : ℕ => (expectedSteps n).toReal) := by
  apply IsBigO.of_bound 18
  filter_upwards [eventually_ge_atTop 2] with n hn
  have h := expected_steps_toReal_ge_linear hn
  simp only [Real.norm_eq_abs, abs_of_nonneg ENNReal.toReal_nonneg,
    abs_of_nonneg (show (0 : ℝ) ≤ (n : ℝ) from Nat.cast_nonneg n)]
  linarith

/-- Tight asymptotic order of the actual expected redraw count under the
    registered product initialization. This is not a running-time theorem. -/
theorem expected_steps_isTheta_linear :
    IsTheta atTop (fun n : ℕ => (expectedSteps n).toReal) (fun n : ℕ => (n : ℝ)) :=
  ⟨expected_steps_isBigO_linear, linear_isBigO_expected_steps⟩

theorem linear_isLittleO_quadratic :
    IsLittleO atTop (fun n : ℕ => (n : ℝ)) (fun n : ℕ => (n : ℝ)^2) := by
  have h := isLittleO_pow_pow_atTop_of_lt (𝕜 := ℝ) (p := 1) (q := 2) (by decide)
  simpa only [Function.comp_def, pow_one] using
    h.comp_tendsto (tendsto_natCast_atTop_atTop (R := ℝ))

/-- In particular a quadratic lower asymptotic bound is false. Mathlib
    expresses Omega(n^2) by this reverse Big-O relation. -/
theorem expected_steps_not_quadratic_lower :
    ¬ IsBigO atTop (fun n : ℕ => (n : ℝ)^2)
      (fun n : ℕ => (expectedSteps n).toReal) := by
  intro h
  have hnonzero : ∀ᶠ n : ℕ in atTop, (n : ℝ) ≠ 0 := by
    filter_upwards [eventually_ge_atTop 1] with n hn
    exact_mod_cast (show n ≠ 0 by omega)
  exact linear_isLittleO_quadratic.not_isBigO hnonzero.frequently
    (h.trans expected_steps_isBigO_linear)

theorem expected_steps_not_isTheta_quadratic :
    ¬ IsTheta atTop (fun n : ℕ => (expectedSteps n).toReal)
      (fun n : ℕ => (n : ℝ)^2) := by
  intro h
  exact expected_steps_not_quadratic_lower h.2

end MTChainFormal.Tightness
