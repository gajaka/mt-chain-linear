import FinalQuadratic
import RefreshDensity
import InitialBadMoment

/-!
A linear lower bound for the same initialized least-failed chain.
The proof uses an initial first moment and the fact that one update can
repair at most three currently failed bridges. No quadratic lower bound
is assumed or inferred from finite numerical data.
-/

set_option autoImplicit false

namespace MTChainFormal.Tightness

open scoped BigOperators ENNReal
open Filter Filtering RefreshDensity

noncomputable def badCount {n : ℕ} : KilledState n → ℝ
  | none => 0
  | some a => (badIndices a.val).card

theorem badCount_nonneg {n : ℕ} (s : KilledState n) : 0 ≤ badCount s := by
  cases s <;> simp [badCount]

theorem badCount_kill {n : ℕ} (s : ChainState n) :
    badCount (kill s) = (badIndices s).card := by
  classical
  by_cases h : (badIndices s).Nonempty
  · simp [kill, h, badCount]
  · have he : badIndices s = ∅ := Finset.not_nonempty_iff_eq_empty.mp h
    simp [kill, badCount, he]

theorem badCount_le_active {n : ℕ} (s : KilledState n) :
    badCount s ≤ (n : ℝ) * activeCost killedActive s := by
  cases s with
  | none => simp [badCount, activeCost, killedActive]
  | some a =>
      have h : (badIndices a.val).card ≤ n := by
        exact (Finset.card_le_univ _).trans_eq (Fintype.card_fin n)
      simpa [badCount, activeCost, killedActive] using (Nat.cast_le.mpr h :
        ((badIndices a.val).card : ℝ) ≤ n)

theorem replacement_bad_count_decrease_le_three {n : ℕ} (hn : 2 ≤ n)
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
    exact (Finset.card_le_card hnear).trans (Finset.card_le_three)
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

theorem badCount_step {n : ℕ} (hn : 2 ≤ n) (s : KilledState n) (u : Draw) :
    badCount s ≤ 3 * activeCost killedActive s + badCount (killedStep s u) := by
  cases s with
  | none => simp [badCount, activeCost, killedActive, killedStep]
  | some a =>
      have h := replacement_bad_count_decrease_le_three hn a.val (activeSelected a) u
      have hr : ((badIndices a.val).card : ℝ) ≤
          ((badIndices (replace a.val (activeSelected a) u)).card : ℝ) + 3 := by
        exact_mod_cast h
      rw [killedStep_some, badCount_kill]
      simpa [badCount, activeCost, killedActive, add_comm] using hr

theorem badCount_one_step {n : ℕ} (hn : 2 ≤ n) (s : KilledState n) :
    badCount s ≤ 3 * activeCost killedActive s + expect (chainKernel n) badCount s := by
  have h := drawAverage_mono (badCount_step hn s)
  rw [drawAverage_const] at h
  rw [expect_chainKernel]
  calc
    _ ≤ drawAverage (fun u => 3 * activeCost killedActive s + badCount (killedStep s u)) := h
    _ = _ := by
      simp only [drawAverage, mul_add, Finset.sum_add_distrib]
      rw [show (∑ _u : Draw, (1 / 36 : ℝ) * (3 * activeCost killedActive s)) =
        3 * activeCost killedActive s from drawAverage_const _]

theorem badCount_finite_horizon {n : ℕ} (hn : 2 ≤ n) (m : ℕ) (s : KilledState n) :
    badCount s ≤ 3 * work (chainKernel n) (activeCost killedActive) m s +
      rewardAt (chainKernel n) badCount m s := by
  induction m generalizing s with
  | zero => simp
  | succ m ih =>
      have hm := expect_mono (chainKernel n) ih s
      have hs := badCount_one_step hn s
      rw [expect_add] at hm
      have hmul : expect (chainKernel n)
          (fun t => 3 * work (chainKernel n) (activeCost killedActive) m t) s =
          3 * expect (chainKernel n) (work (chainKernel n) (activeCost killedActive) m) s := by
        simpa [mul_comm] using expect_mul_const (chainKernel n)
          (work (chainKernel n) (activeCost killedActive) m) 3 s
      rw [hmul] at hm
      rw [work_succ, rewardAt_succ]
      linarith

theorem rewardAt_mono {S : Type*} [Fintype S] (K : FiniteKernel S)
    {f g : S → ℝ} (h : ∀ s, f s ≤ g s) (m : ℕ) (s : S) :
    rewardAt K f m s ≤ rewardAt K g m s := by
  induction m generalizing s with
  | zero => exact h s
  | succ m ih => exact expect_mono K ih s

theorem rewardAt_mul {S : Type*} [Fintype S] (K : FiniteKernel S)
    (f : S → ℝ) (a : ℝ) (m : ℕ) (s : S) :
    rewardAt K (fun t => a * f t) m s = a * rewardAt K f m s := by
  induction m generalizing s with
  | zero => rfl
  | succ m ih =>
      simp only [rewardAt_succ, show rewardAt K (fun t => a * f t) m =
        (fun t => a * rewardAt K f m t) from funext ih]
      simpa [mul_comm] using expect_mul_const K (rewardAt K f m) a s

theorem badCount_reward_le {n : ℕ} (m : ℕ) :
    initialRewardAt (chainKernel n) initialLaw badCount m ≤
      (n : ℝ) * initialRewardAt (chainKernel n) initialLaw (activeCost killedActive) m := by
  unfold initialRewardAt
  rw [Finset.mul_sum]
  apply Finset.sum_le_sum
  intro s _
  have h := rewardAt_mono (chainKernel n) badCount_le_active m s
  rw [rewardAt_mul] at h
  nlinarith [initialLaw_nonneg s]

theorem initial_badCount_reward_nonneg {n : ℕ} (m : ℕ) :
    0 ≤ initialRewardAt (chainKernel n) initialLaw badCount m := by
  exact Finset.sum_nonneg (fun s _ => mul_nonneg (initialLaw_nonneg s)
    (rewardAt_nonneg (chainKernel n) badCount badCount_nonneg m s))

theorem initial_survival_real_tendsto_zero {n : ℕ} (hn : 2 ≤ n) :
    Tendsto (fun m => initialRewardAt (chainKernel n) initialLaw
      (activeCost killedActive) m) atTop (nhds 0) := by
  have h := (ENNReal.tendsto_toReal ENNReal.zero_ne_top).comp
    (initialized_survival_tendsto_zero hn)
  have hnonneg (m : ℕ) : 0 ≤ initialRewardAt (chainKernel n) initialLaw
      (activeCost killedActive) m := by
    exact Finset.sum_nonneg (fun s _ => mul_nonneg (initialLaw_nonneg s)
      (rewardAt_nonneg (chainKernel n) _ (activeCost_nonneg _) m s))
  simpa only [Function.comp_def, ENNReal.toReal_ofReal (hnonneg _),
    ENNReal.toReal_zero] using h

theorem badCount_reward_tendsto_zero {n : ℕ} (hn : 2 ≤ n) :
    Tendsto (fun m => initialRewardAt (chainKernel n) initialLaw badCount m)
      atTop (nhds 0) := by
  exact squeeze_zero initial_badCount_reward_nonneg badCount_reward_le
    (by simpa using (initial_survival_real_tendsto_zero hn).const_mul (n : ℝ))

noncomputable def initialBadCount (n : ℕ) : ℝ :=
  ∑ s : KilledState n, initialLaw s * badCount s

theorem initial_badCount_finite_horizon {n : ℕ} (hn : 2 ≤ n) (m : ℕ) :
    initialBadCount n ≤ 3 * initialWork (chainKernel n) initialLaw
      (activeCost killedActive) m + initialRewardAt (chainKernel n) initialLaw badCount m := by
  unfold initialBadCount initialWork initialRewardAt
  rw [Finset.mul_sum, ← Finset.sum_add_distrib]
  apply Finset.sum_le_sum
  intro s _
  have h := mul_le_mul_of_nonneg_left (badCount_finite_horizon hn m s) (initialLaw_nonneg s)
  nlinarith

theorem initialWork_le_expectedSteps_toReal {n : ℕ} (hn : 2 ≤ n) (m : ℕ) :
    initialWork (chainKernel n) initialLaw (activeCost killedActive) m ≤
      (expectedSteps n).toReal := by
  apply (ENNReal.ofReal_le_iff_le_toReal (expected_steps_finite hn).ne).mp
  exact le_iSup (fun k => ENNReal.ofReal
    (initialWork (chainKernel n) initialLaw (activeCost killedActive) k)) m

theorem initialBadCount_le_three_expectedSteps {n : ℕ} (hn : 2 ≤ n) :
    initialBadCount n ≤ 3 * (expectedSteps n).toReal := by
  have hlim := (badCount_reward_tendsto_zero hn).const_add (3 * (expectedSteps n).toReal)
  apply ge_of_tendsto' (by simpa using hlim)
  intro m
  have h := initial_badCount_finite_horizon hn m
  have hm := initialWork_le_expectedSteps_toReal hn m
  linarith

theorem expected_steps_ge_initial_bad {n : ℕ} (hn : 2 ≤ n) :
    ENNReal.ofReal (initialBadCount n / 3) ≤ expectedSteps n := by
  apply ENNReal.ofReal_le_of_le_toReal
  have h := initialBadCount_le_three_expectedSteps hn
  linarith

theorem initialBadCount_eq {n : ℕ} (hn : 2 ≤ n) :
    initialBadCount n = (5 * (n : ℝ) - 6) / 12 := by
  unfold initialBadCount
  rw [initialLaw_expect]
  simp only [badCount_kill]
  exact initial_bad_moment hn

theorem expected_steps_ge_linear_refined {n : ℕ} (hn : 2 ≤ n) :
    ENNReal.ofReal ((5 * (n : ℝ) - 6) / 36) ≤ expectedSteps n := by
  have h := expected_steps_ge_initial_bad hn
  rw [initialBadCount_eq hn] at h
  convert h using 1
  congr 1
  ring

theorem expected_steps_ge_linear {n : ℕ} (hn : 2 ≤ n) :
    ENNReal.ofReal ((n : ℝ) / 18) ≤ expectedSteps n := by
  apply le_trans (ENNReal.ofReal_le_ofReal ?_) (expected_steps_ge_linear_refined hn)
  have hnr : (2 : ℝ) ≤ n := by exact_mod_cast hn
  linarith

end MTChainFormal.Tightness
