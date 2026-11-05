import RegularDrift
import PotentialTransport
import StoppedKernel
import HistoryFiltering

/-!
An all-length theorem about the actual registered finite chain. The only
hypothesis in its quantitative result is n >= 2. Filtering, the actual local
drift and the concrete initial law are proved, not external assumptions.
-/

set_option autoImplicit false

namespace MTChainFormal

open scoped BigOperators ENNReal
open Filter Filtering

/-- The proved one-step payment for every active observed prefix. -/
theorem observed_supersolution {n : ℕ} (hn : 2 ≤ n) :
    ∀ q : ObservedState n,
      activeCost observedActive q + expect (observedKernel n) observedPotential q ≤
        observedPotential q := by
  intro q
  cases q with
  | none =>
      simp [activeCost, observedActive, observedPotential, expect, observedKernel, observedWeight]
  | some q =>
      have hstep := completed_chain_potential_drift hn q.val q.property
      rw [← expect_observedPotential_eq_completed (actual_intertwining hn) q] at hstep
      change 1 + expect (observedKernel n) observedPotential (some q) ≤ chainPotential q.val.2
      linarith

/-- Expected number of redraws, excluding the common initial product draw.
    This is the extended sum of actual active-state survival probabilities. -/
noncomputable def expectedSteps (n : ℕ) : ℝ≥0∞ :=
  initialTotalWork (chainKernel n) initialLaw (activeCost killedActive)

/-- Every actual PASS-to-FAIL episode is counted, including repeated episodes
    for the same certificate. -/
noncomputable def expectedInvalidations (n : ℕ) : ℝ≥0∞ :=
  initialTotalWork (chainKernel n) initialLaw expectedHazardCost

/-- A general quadratic upper bound for the original independent product law. -/
theorem expected_steps_le_quadratic {n : ℕ} (hn : 2 ≤ n) :
    expectedSteps n ≤ ENNReal.ofReal (283 * (n : ℝ)^2) := by
  exact transported_initialTotalWork_le_uniform (observedKernel n) (chainKernel n)
    completionWeight (actual_intertwining hn) (activeCost observedActive)
    (activeCost killedActive) completion_active_cost initialObserved initialLaw
    (initialLaw_completion n) initialObserved_nonneg (initialObserved_sum n)
    observedPotential observedPotential_nonneg (observed_supersolution hn)
    (283 * (n : ℝ)^2) (observedPotential_le hn)

theorem expected_steps_finite {n : ℕ} (hn : 2 ≤ n) : expectedSteps n < ∞ :=
  lt_of_le_of_lt (expected_steps_le_quadratic hn) ENNReal.ofReal_lt_top

theorem finite_horizon_steps_le_quadratic {n : ℕ} (hn : 2 ≤ n) (m : ℕ) :
    initialWork (chainKernel n) initialLaw (activeCost killedActive) m ≤ 283 * (n : ℝ)^2 := by
  rw [← initialWork_transport (observedKernel n) (chainKernel n) completionWeight
    (actual_intertwining hn) (activeCost observedActive) (activeCost killedActive)
    completion_active_cost initialObserved initialLaw (initialLaw_completion n)]
  calc
    _ ≤ ∑ q, initialObserved q * observedPotential q :=
      initialWork_le_supersolution (observedKernel n) initialObserved (activeCost observedActive)
        observedPotential initialObserved_nonneg observedPotential_nonneg (observed_supersolution hn) m
    _ ≤ ∑ q, initialObserved q * (283 * (n : ℝ)^2) :=
      Finset.sum_le_sum fun q _ => mul_le_mul_of_nonneg_left (observedPotential_le hn q)
        (initialObserved_nonneg q)
    _ = _ := by rw [← Finset.sum_mul, initialObserved_sum n, one_mul]

theorem expected_invalidations_le_twice_steps {n : ℕ} (hn : 2 ≤ n) :
    expectedInvalidations n ≤ expectedSteps n * 2 :=
  initialTotalHazardWork_le_two_active hn

theorem expected_invalidations_le_quadratic {n : ℕ} (hn : 2 ≤ n) :
    expectedInvalidations n ≤ ENNReal.ofReal (566 * (n : ℝ)^2) := by
  calc
    _ ≤ expectedSteps n * 2 := expected_invalidations_le_twice_steps hn
    _ ≤ ENNReal.ofReal (283 * (n : ℝ)^2) * 2 :=
      mul_le_mul_of_nonneg_right (expected_steps_le_quadratic hn) (by positivity)
    _ = _ := by
      rw [show (2 : ℝ≥0∞) = ENNReal.ofReal (2 : ℝ) by norm_num,
        ← ENNReal.ofReal_mul' (by norm_num : (0 : ℝ) ≤ 2)]
      congr 1
      ring

theorem expected_invalidations_finite {n : ℕ} (hn : 2 ≤ n) :
    expectedInvalidations n < ∞ :=
  lt_of_le_of_lt (expected_invalidations_le_quadratic hn) ENNReal.ofReal_lt_top

/-- The original reviewed paper constants follow from the stronger potential. -/
theorem expected_steps_le_paper_bound {n : ℕ} (hn : 2 ≤ n) :
    expectedSteps n ≤ ENNReal.ofReal (6000 * (n : ℝ)^2) := by
  apply (expected_steps_le_quadratic hn).trans
  apply ENNReal.ofReal_le_ofReal
  nlinarith [sq_nonneg (n : ℝ)]

theorem expected_invalidations_le_paper_bound {n : ℕ} (hn : 2 ≤ n) :
    expectedInvalidations n ≤ ENNReal.ofReal (12000 * (n : ℝ)^2) := by
  apply (expected_invalidations_le_quadratic hn).trans
  apply ENNReal.ofReal_le_ofReal
  nlinarith [sq_nonneg (n : ℝ)]

/-- Survival mass of the actual initialized process tends to zero. This is
    stated using the finite transition weights, without assuming termination. -/
theorem initialized_survival_tendsto_zero {n : ℕ} (hn : 2 ≤ n) :
    Tendsto (fun t : ℕ => ENNReal.ofReal
      (initialRewardAt (chainKernel n) initialLaw (activeCost killedActive) t))
      atTop (nhds 0) :=
  initialRewardAt_tendsto_zero (chainKernel n) initialLaw (activeCost killedActive)
    initialLaw_nonneg (activeCost_nonneg killedActive) (expected_steps_finite hn)

theorem initialized_survival_iInf_eq_zero {n : ℕ} (hn : 2 ≤ n) :
    (⨅ t : ℕ, ENNReal.ofReal
      (initialRewardAt (chainKernel n) initialLaw (activeCost killedActive) t)) = 0 := by
  apply le_antisymm _ bot_le
  exact ge_of_tendsto' (initialized_survival_tendsto_zero hn)
    (fun t => iInf_le (fun m => ENNReal.ofReal
      (initialRewardAt (chainKernel n) initialLaw (activeCost killedActive) m)) t)

/-- Any excursion stopped upon a declared set of observed prefixes satisfies
    the same bound, including its extended infinite horizon. -/
theorem stopped_excursion_infinite_bound {n : ℕ} (hn : 2 ≤ n)
    (stop : ObservedState n → Bool) (q : ObservedState n) :
    totalWork (stoppedKernel (observedKernel n) stop)
      (stoppedCost stop (activeCost observedActive)) q ≤ ENNReal.ofReal (observedPotential q) :=
  stopped_infinite_work_le (observedKernel n) stop (activeCost observedActive)
    observedPotential observedPotential_nonneg (observed_supersolution hn) q

theorem stopped_excursion_finite_bound {n : ℕ} (hn : 2 ≤ n)
    (stop : ObservedState n → Bool) (q : ObservedState n) (m : ℕ) :
    work (stoppedKernel (observedKernel n) stop)
      (stoppedCost stop (activeCost observedActive)) m q ≤ observedPotential q :=
  stopped_work_le (observedKernel n) stop (activeCost observedActive)
    observedPotential observedPotential_nonneg (observed_supersolution hn) m q

end MTChainFormal
