module

public import KernelWork

@[expose] public section

set_option autoImplicit false

namespace MTChainFormal.BiasedResampling

open scoped BigOperators ENNReal
open Filter

section

variable {S : Type*} [Fintype S]

theorem reward_mono (K : FiniteKernel S) {f g : S → ℝ}
    (h : ∀ s, f s ≤ g s) (m : ℕ) (s : S) :
    rewardAt K f m s ≤ rewardAt K g m s := by
  induction m generalizing s with
  | zero => exact h s
  | succ m ih => exact expect_mono K ih s

theorem reward_const_mul (K : FiniteKernel S) (f : S → ℝ) (a : ℝ)
    (m : ℕ) (s : S) :
    rewardAt K (fun t => a * f t) m s = a * rewardAt K f m s := by
  induction m generalizing s with
  | zero => rfl
  | succ m ih =>
      simp only [rewardAt_succ, show rewardAt K (fun t => a * f t) m =
        (fun t => a * rewardAt K f m t) from funext ih]
      simpa [mul_comm] using expect_mul_const K (rewardAt K f m) a s

/-- A step removes at most three units of the count. This is independent
    of the resampling probabilities and of a particular chain instance. -/
theorem count_finite_horizon (K : FiniteKernel S) (c D : S → ℝ)
    (hstep : ∀ s, D s ≤ 3 * c s + expect K D s)
    (m : ℕ) (s : S) :
    D s ≤ 3 * work K c m s + rewardAt K D m s := by
  induction m generalizing s with
  | zero => simp
  | succ m ih =>
      have hm := expect_mono K ih s
      have hs := hstep s
      rw [expect_add] at hm
      have hmul : expect K (fun t => 3 * work K c m t) s =
          3 * expect K (work K c m) s := by
        simpa [mul_comm] using expect_mul_const K (work K c m) 3 s
      rw [hmul] at hm
      rw [work_succ, rewardAt_succ]
      linarith

/-- A lower bound from the initial count. Finiteness is discharged by
    an explicit supersolution rather than postulated as a premise. -/
theorem initial_steps_ge_count (K : FiniteKernel S) (μ c D V : S → ℝ)
    (hμ : ∀ s, 0 ≤ μ s) (hc : ∀ s, 0 ≤ c s)
    (hD : ∀ s, 0 ≤ D s) (hV : ∀ s, 0 ≤ V s)
    (hupper : ∀ s, c s + expect K V s ≤ V s)
    (hstep : ∀ s, D s ≤ 3 * c s + expect K D s)
    (cap : ℝ) (hbounded : ∀ s, D s ≤ cap * c s) :
    ENNReal.ofReal ((∑ s, μ s * D s) / 3) ≤ initialTotalWork K μ c := by
  have hfinite : initialTotalWork K μ c < ∞ :=
    lt_of_le_of_lt (initialTotalWork_le_supersolution K μ c V hμ hV hupper)
      ENNReal.ofReal_lt_top
  have hcnonneg (m : ℕ) : 0 ≤ initialRewardAt K μ c m := by
    exact Finset.sum_nonneg (fun s _ => mul_nonneg (hμ s)
      (rewardAt_nonneg K c hc m s))
  have hcLim : Tendsto (fun m => initialRewardAt K μ c m) atTop (nhds 0) := by
    have h := (ENNReal.tendsto_toReal ENNReal.zero_ne_top).comp
      (initialRewardAt_tendsto_zero K μ c hμ hc hfinite)
    simpa only [Function.comp_def, ENNReal.toReal_ofReal (hcnonneg _),
      ENNReal.toReal_zero] using h
  have hDnonneg (m : ℕ) : 0 ≤ initialRewardAt K μ D m := by
    exact Finset.sum_nonneg (fun s _ => mul_nonneg (hμ s)
      (rewardAt_nonneg K D hD m s))
  have hDcap (m : ℕ) : initialRewardAt K μ D m ≤
      cap * initialRewardAt K μ c m := by
    unfold initialRewardAt
    rw [Finset.mul_sum]
    apply Finset.sum_le_sum
    intro s _
    have h := reward_mono K hbounded m s
    rw [reward_const_mul] at h
    nlinarith [hμ s]
  have hDLim : Tendsto (fun m => initialRewardAt K μ D m) atTop (nhds 0) :=
    squeeze_zero hDnonneg hDcap (by simpa using hcLim.const_mul cap)
  have hwork (m : ℕ) : initialWork K μ c m ≤ (initialTotalWork K μ c).toReal := by
    apply (ENNReal.ofReal_le_iff_le_toReal hfinite.ne).mp
    exact le_iSup (fun k => ENNReal.ofReal (initialWork K μ c k)) m
  have htel (m : ℕ) : (∑ s, μ s * D s) ≤
      3 * initialWork K μ c m + initialRewardAt K μ D m := by
    unfold initialWork initialRewardAt
    rw [Finset.mul_sum, ← Finset.sum_add_distrib]
    apply Finset.sum_le_sum
    intro s _
    have h := mul_le_mul_of_nonneg_left (count_finite_horizon K c D hstep m s) (hμ s)
    nlinarith
  have hcount : (∑ s, μ s * D s) ≤ 3 * (initialTotalWork K μ c).toReal := by
    have hlim := hDLim.const_add (3 * (initialTotalWork K μ c).toReal)
    apply ge_of_tendsto' (by simpa using hlim)
    intro m
    have h := htel m
    have hw := hwork m
    linarith
  apply ENNReal.ofReal_le_of_le_toReal
  linarith

end

end MTChainFormal.BiasedResampling
