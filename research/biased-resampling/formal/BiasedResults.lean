module

public import BiasedLower
public import Mathlib.Analysis.Asymptotics.SpecificAsymptotics

@[expose] public section

set_option autoImplicit false

namespace MTChainFormal.BiasedResampling

open scoped BigOperators ENNReal

/-- The initialization law is independent of subsequent adaptive decisions. -/
noncomputable def adaptiveInitialWork {n : ℕ} (policy : HistoryPolicy n)
    (q : ℝ) (m : ℕ) : ℝ :=
  ∑ s, initialWeight q s * adaptiveWork policy m [] s

noncomputable def adaptiveInitialTotalWork {n : ℕ} (policy : HistoryPolicy n)
    (q : ℝ) : ℝ≥0∞ :=
  ⨆ m : ℕ, ENNReal.ofReal (adaptiveInitialWork policy q m)

theorem adaptiveInitialTotalWork_le_budget {n : ℕ} (hn : 2 ≤ n)
    (policy : HistoryPolicy n) (q : ℝ) (hq0 : 0 ≤ q) (hq1 : q ≤ 1) :
    adaptiveInitialTotalWork policy q ≤
      ENNReal.ofReal (∑ s : ChainState n, initialWeight q s * potential s) := by
  apply iSup_le
  intro m
  apply ENNReal.ofReal_le_ofReal
  exact Finset.sum_le_sum (fun s _ =>
    mul_le_mul_of_nonneg_left (adaptiveWork_le_potential hn policy m [] s)
      (initialWeight_nonneg q hq0 hq1 s))

theorem adaptive_biased_initial_upper {n : ℕ} (hn : 2 ≤ n)
    (policy : HistoryPolicy n) :
    adaptiveInitialTotalWork policy (2 / 3) ≤ ENNReal.ofReal (3 * (n : ℝ) - 2) := by
  have h := adaptiveInitialTotalWork_le_budget hn policy (2 / 3)
    (by norm_num) (by norm_num)
  rwa [initial_static_potential_mean hn] at h

theorem adaptive_uniform_initial_upper {n : ℕ} (hn : 2 ≤ n)
    (policy : HistoryPolicy n) :
    adaptiveInitialTotalWork policy (1 / 3) ≤ ENNReal.ofReal (5 * (n : ℝ) - 4) := by
  have h := adaptiveInitialTotalWork_le_budget hn policy (1 / 3)
    (by norm_num) (by norm_num)
  rwa [initial_uniform_potential_mean hn] at h

theorem static_initial_total_eq {n : ℕ} (p : AdmissibleBias) (q : ℝ) :
    adaptiveInitialTotalWork (staticPolicy p : HistoryPolicy n) q =
      initialTotalWork (staticKernel p n) (initialWeight q) rawActiveCost := by
  simp only [adaptiveInitialTotalWork, adaptiveInitialWork, initialTotalWork,
    initialWork, staticWork_eq]

theorem static_biased_initial_upper {n : ℕ} (hn : 2 ≤ n) :
    initialTotalWork (staticKernel staticBias n) (initialWeight (2 / 3)) rawActiveCost ≤
      ENNReal.ofReal (3 * (n : ℝ) - 2) := by
  rw [← static_initial_total_eq]
  exact adaptive_biased_initial_upper hn _

theorem static_uniform_initial_upper {n : ℕ} (hn : 2 ≤ n) :
    initialTotalWork (staticKernel staticBias n) (initialWeight (1 / 3)) rawActiveCost ≤
      ENNReal.ofReal (5 * (n : ℝ) - 4) := by
  rw [← static_initial_total_eq]
  exact adaptive_uniform_initial_upper hn _

theorem static_biased_initial_lower_refined {n : ℕ} (hn : 2 ≤ n) :
    ENNReal.ofReal ((15 * (n : ℝ) - 16) / 144) ≤
      initialTotalWork (staticKernel staticBias n) (initialWeight (2 / 3)) rawActiveCost := by
  have h := static_initial_steps_ge_defects hn staticBias (2 / 3)
    (by norm_num) (by norm_num)
  simp only [defectCount] at h
  rw [initial_static_bad_moment hn] at h
  have he : ((15 * (n : ℝ) - 16) / 48) / 3 = (15 * (n : ℝ) - 16) / 144 := by ring
  rwa [he] at h

theorem static_biased_initial_lower {n : ℕ} (hn : 2 ≤ n) :
    ENNReal.ofReal ((n : ℝ) / 24) ≤
      initialTotalWork (staticKernel staticBias n) (initialWeight (2 / 3)) rawActiveCost := by
  apply le_trans (ENNReal.ofReal_le_ofReal ?_) (static_biased_initial_lower_refined hn)
  have hnr : (2 : ℝ) ≤ n := by exact_mod_cast hn
  linarith

/-- Matched linear upper and lower bounds for the fixed-law, initialized
    process. The separate adaptive theorem supplies an upper bound only. -/
theorem static_linear_work_bounds {n : ℕ} (hn : 2 ≤ n) :
    ENNReal.ofReal ((n : ℝ) / 24) ≤
        initialTotalWork (staticKernel staticBias n) (initialWeight (2 / 3)) rawActiveCost ∧
      initialTotalWork (staticKernel staticBias n) (initialWeight (2 / 3)) rawActiveCost ≤
        ENNReal.ofReal (3 * (n : ℝ) - 2) :=
  ⟨static_biased_initial_lower hn, static_biased_initial_upper hn⟩

theorem policy_space_nonempty (n : ℕ) : Nonempty (HistoryPolicy n) :=
  ⟨staticPolicy staticBias⟩

noncomputable def expectedSteps (n : ℕ) : ℝ≥0∞ :=
  initialTotalWork (staticKernel staticBias n) (initialWeight (2 / 3)) rawActiveCost

theorem expected_steps_finite {n : ℕ} (hn : 2 ≤ n) : expectedSteps n < ∞ :=
  lt_of_le_of_lt (static_biased_initial_upper hn) ENNReal.ofReal_lt_top

theorem expected_steps_toReal_lower {n : ℕ} (hn : 2 ≤ n) :
    (n : ℝ) / 24 ≤ (expectedSteps n).toReal :=
  (ENNReal.ofReal_le_iff_le_toReal (expected_steps_finite hn).ne).mp
    (static_biased_initial_lower hn)

theorem expected_steps_toReal_upper {n : ℕ} (hn : 2 ≤ n) :
    (expectedSteps n).toReal ≤ 3 * (n : ℝ) := by
  have hu : expectedSteps n ≤ ENNReal.ofReal (3 * (n : ℝ)) :=
    (static_biased_initial_upper hn).trans (ENNReal.ofReal_le_ofReal (by linarith))
  have h := ENNReal.toReal_mono ENNReal.ofReal_ne_top hu
  simpa only [ENNReal.toReal_ofReal (by positivity : (0 : ℝ) ≤ 3 * (n : ℝ))] using h

/-- Theta(n) counts actual redraws for the new fixed law and its separately
    specified product initialization. It is not an execution-time claim. -/
theorem expected_steps_isTheta_linear :
    Asymptotics.IsTheta Filter.atTop
      (fun n : ℕ => (expectedSteps n).toReal) (fun n : ℕ => (n : ℝ)) := by
  constructor
  · apply Asymptotics.IsBigO.of_bound 3
    filter_upwards [Filter.eventually_ge_atTop 2] with n hn
    simpa only [Real.norm_eq_abs, abs_of_nonneg ENNReal.toReal_nonneg,
      abs_of_nonneg (show (0 : ℝ) ≤ (n : ℝ) from Nat.cast_nonneg n)] using
      expected_steps_toReal_upper hn
  · apply Asymptotics.IsBigO.of_bound 24
    filter_upwards [Filter.eventually_ge_atTop 2] with n hn
    have h := expected_steps_toReal_lower hn
    simp only [Real.norm_eq_abs, abs_of_nonneg ENNReal.toReal_nonneg,
      abs_of_nonneg (show (0 : ℝ) ≤ (n : ℝ) from Nat.cast_nonneg n)]
    linarith

end MTChainFormal.BiasedResampling
