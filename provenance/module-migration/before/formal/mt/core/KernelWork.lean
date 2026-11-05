import Mathlib.Data.Fintype.BigOperators
import Mathlib.Topology.Algebra.InfiniteSum.ENNReal
import Mathlib.Topology.Algebra.InfiniteSum.Real
import Mathlib.Tactic

set_option autoImplicit false

namespace MTChainFormal

open scoped BigOperators ENNReal
open Filter

/-- A finite stochastic kernel, represented by its nonnegative real weights. -/
structure FiniteKernel (S : Type*) [Fintype S] where
  weight : S → S → ℝ
  nonneg : ∀ s u, 0 ≤ weight s u
  sum_eq_one : ∀ s, ∑ u, weight s u = 1

variable {S : Type*} [Fintype S]

/-- The one-step expectation is the actual finite weighted sum. -/
noncomputable def expect (K : FiniteKernel S) (f : S → ℝ) (s : S) : ℝ :=
  ∑ u, K.weight s u * f u

@[simp] theorem expect_zero (K : FiniteKernel S) (s : S) :
    expect K (fun _ => 0) s = 0 := by
  simp [expect]

theorem expect_nonneg (K : FiniteKernel S) (f : S → ℝ)
    (hf : ∀ u, 0 ≤ f u) (s : S) : 0 ≤ expect K f s := by
  exact Finset.sum_nonneg (fun u _ => mul_nonneg (K.nonneg s u) (hf u))

theorem expect_mono (K : FiniteKernel S) {f g : S → ℝ}
    (hfg : ∀ u, f u ≤ g u) (s : S) : expect K f s ≤ expect K g s := by
  exact Finset.sum_le_sum (fun u _ => mul_le_mul_of_nonneg_left (hfg u) (K.nonneg s u))

theorem expect_add (K : FiniteKernel S) (f g : S → ℝ) (s : S) :
    expect K (fun u => f u + g u) s = expect K f s + expect K g s := by
  simp [expect, mul_add, Finset.sum_add_distrib]

theorem expect_mul_const (K : FiniteKernel S) (f : S → ℝ) (a : ℝ) (s : S) :
    expect K (fun u => f u * a) s = expect K f s * a := by
  simp [expect, mul_assoc, Finset.sum_mul]

theorem expect_const (K : FiniteKernel S) (a : ℝ) (s : S) :
    expect K (fun _ => a) s = a := by
  simp [expect, ← Finset.sum_mul, K.sum_eq_one]

/-- Expected reward earned precisely at time t, obtained by kernel iteration. -/
noncomputable def rewardAt (K : FiniteKernel S) (c : S → ℝ) : ℕ → S → ℝ
  | 0 => c
  | t + 1 => fun s => expect K (rewardAt K c t) s

/-- Expected cumulative reward over the first m operations, before transition m. -/
noncomputable def work (K : FiniteKernel S) (c : S → ℝ) : ℕ → S → ℝ
  | 0 => fun _ => 0
  | m + 1 => fun s => c s + expect K (work K c m) s

@[simp] theorem rewardAt_zero (K : FiniteKernel S) (c : S → ℝ) (s : S) :
    rewardAt K c 0 s = c s := rfl

@[simp] theorem rewardAt_succ (K : FiniteKernel S) (c : S → ℝ) (t : ℕ) (s : S) :
    rewardAt K c (t + 1) s = expect K (rewardAt K c t) s := rfl

@[simp] theorem work_zero (K : FiniteKernel S) (c : S → ℝ) (s : S) :
    work K c 0 s = 0 := rfl

@[simp] theorem work_succ (K : FiniteKernel S) (c : S → ℝ) (m : ℕ) (s : S) :
    work K c (m + 1) s = c s + expect K (work K c m) s := rfl

theorem rewardAt_nonneg (K : FiniteKernel S) (c : S → ℝ)
    (hc : ∀ s, 0 ≤ c s) (t : ℕ) (s : S) : 0 ≤ rewardAt K c t s := by
  induction t generalizing s with
  | zero => exact hc s
  | succ t ih => exact expect_nonneg K _ ih s

theorem work_nonneg (K : FiniteKernel S) (c : S → ℝ)
    (hc : ∀ s, 0 ≤ c s) (m : ℕ) (s : S) : 0 ≤ work K c m s := by
  induction m generalizing s with
  | zero => exact le_rfl
  | succ m ih => exact add_nonneg (hc s) (expect_nonneg K _ ih s)

theorem work_cost_mono (K : FiniteKernel S) {c d : S → ℝ}
    (hcd : ∀ s, c s ≤ d s) (m : ℕ) (s : S) : work K c m s ≤ work K d m s := by
  induction m generalizing s with
  | zero => exact le_rfl
  | succ m ih => exact add_le_add (hcd s) (expect_mono K ih s)

theorem work_mul_const (K : FiniteKernel S) (c : S → ℝ) (a : ℝ)
    (m : ℕ) (s : S) : work K (fun u => c u * a) m s = work K c m s * a := by
  induction m generalizing s with
  | zero => simp
  | succ m ih =>
      have hfun : work K (fun u => c u * a) m = fun u => work K c m u * a := funext ih
      rw [work_succ, work_succ, hfun, expect_mul_const, add_mul]

theorem work_le_supersolution (K : FiniteKernel S) (c V : S → ℝ)
    (hV : ∀ s, 0 ≤ V s)
    (hstep : ∀ s, c s + expect K V s ≤ V s) (m : ℕ) (s : S) :
    work K c m s ≤ V s := by
  induction m generalizing s with
  | zero => exact hV s
  | succ m ih =>
      exact le_trans (add_le_add (le_refl (c s)) (expect_mono K ih s)) (hstep s)

theorem work_succ_eq_add_rewardAt (K : FiniteKernel S) (c : S → ℝ)
    (m : ℕ) (s : S) : work K c (m + 1) s = work K c m s + rewardAt K c m s := by
  induction m generalizing s with
  | zero => simp [work, expect]
  | succ m ih =>
      change c s + expect K (work K c (m + 1)) s =
        (c s + expect K (work K c m) s) + expect K (rewardAt K c m) s
      have hfun : work K c (m + 1) =
          fun u => work K c m u + rewardAt K c m u := funext ih
      rw [hfun, expect_add]
      ring

theorem work_eq_sum_rewardAt (K : FiniteKernel S) (c : S → ℝ)
    (m : ℕ) (s : S) : work K c m s = ∑ t ∈ Finset.range m, rewardAt K c t s := by
  induction m with
  | zero => simp
  | succ m ih => rw [work_succ_eq_add_rewardAt, Finset.sum_range_succ, ih]

theorem work_monotone (K : FiniteKernel S) (c : S → ℝ)
    (hc : ∀ s, 0 ≤ c s) (s : S) : Monotone (fun m => work K c m s) := by
  apply monotone_nat_of_le_succ
  intro m
  rw [work_succ_eq_add_rewardAt]
  exact le_add_of_nonneg_right (rewardAt_nonneg K c hc m s)

/-- Infinite expected accumulated reward, defined without assuming finiteness. -/
noncomputable def totalWork (K : FiniteKernel S) (c : S → ℝ) (s : S) : ℝ≥0∞ :=
  ⨆ m : ℕ, ENNReal.ofReal (work K c m s)

theorem totalWork_eq_tsum (K : FiniteKernel S) (c : S → ℝ)
    (hc : ∀ s, 0 ≤ c s) (s : S) :
    totalWork K c s = ∑' t : ℕ, ENNReal.ofReal (rewardAt K c t s) := by
  rw [ENNReal.tsum_eq_iSup_nat]
  apply iSup_congr
  intro m
  rw [work_eq_sum_rewardAt]
  exact ENNReal.ofReal_sum_of_nonneg (fun t _ => rewardAt_nonneg K c hc t s)

theorem totalWork_le_supersolution (K : FiniteKernel S) (c V : S → ℝ)
    (hV : ∀ s, 0 ≤ V s)
    (hstep : ∀ s, c s + expect K V s ≤ V s) (s : S) :
    totalWork K c s ≤ ENNReal.ofReal (V s) := by
  apply iSup_le
  intro m
  exact ENNReal.ofReal_le_ofReal (work_le_supersolution K c V hV hstep m s)

theorem totalWork_lt_top (K : FiniteKernel S) (c V : S → ℝ)
    (hV : ∀ s, 0 ≤ V s)
    (hstep : ∀ s, c s + expect K V s ≤ V s) (s : S) :
    totalWork K c s < ∞ := by
  exact lt_of_le_of_lt (totalWork_le_supersolution K c V hV hstep s) ENNReal.ofReal_lt_top

theorem totalWork_cost_mono (K : FiniteKernel S) {c d : S → ℝ}
    (hcd : ∀ s, c s ≤ d s) (s : S) : totalWork K c s ≤ totalWork K d s := by
  apply iSup_mono
  intro m
  exact ENNReal.ofReal_le_ofReal (work_cost_mono K hcd m s)

theorem totalWork_mul_const (K : FiniteKernel S) (c : S → ℝ) (a : ℝ)
    (ha : 0 ≤ a) (s : S) :
    totalWork K (fun u => c u * a) s = totalWork K c s * ENNReal.ofReal a := by
  simp only [totalWork, work_mul_const, ENNReal.ofReal_mul' ha]
  exact (ENNReal.iSup_mul _ _).symm

theorem totalWork_le_mul (K : FiniteKernel S) (c d : S → ℝ) (a : ℝ)
    (ha : 0 ≤ a) (hcd : ∀ s, c s ≤ d s * a) (s : S) :
    totalWork K c s ≤ totalWork K d s * ENNReal.ofReal a := by
  exact (totalWork_cost_mono K hcd s).trans_eq (totalWork_mul_const K d a ha s)

theorem rewardAt_summable (K : FiniteKernel S) (c V : S → ℝ)
    (hc : ∀ s, 0 ≤ c s) (hV : ∀ s, 0 ≤ V s)
    (hstep : ∀ s, c s + expect K V s ≤ V s) (s : S) :
    Summable (fun t : ℕ => rewardAt K c t s) := by
  apply summable_of_sum_range_le (fun t => rewardAt_nonneg K c hc t s)
  intro m
  rw [← work_eq_sum_rewardAt]
  exact work_le_supersolution K c V hV hstep m s

theorem rewardAt_tendsto_zero (K : FiniteKernel S) (c V : S → ℝ)
    (hc : ∀ s, 0 ≤ c s) (hV : ∀ s, 0 ≤ V s)
    (hstep : ∀ s, c s + expect K V s ≤ V s) (s : S) :
    Tendsto (fun t : ℕ => ENNReal.ofReal (rewardAt K c t s)) atTop (nhds 0) := by
  apply ENNReal.tendsto_atTop_zero_of_tsum_ne_top
  rw [← totalWork_eq_tsum K c hc s]
  exact (totalWork_lt_top K c V hV hstep s).ne

/-- The t-step transition weights, defined by actual finite matrix multiplication. -/
noncomputable def kernelPower (K : FiniteKernel S) : ℕ → S → S → ℝ
  | 0 => by classical exact fun s u => if s = u then 1 else 0
  | t + 1 => fun s u => ∑ v, K.weight s v * kernelPower K t v u

theorem kernelPower_nonneg (K : FiniteKernel S) (t : ℕ) (s u : S) :
    0 ≤ kernelPower K t s u := by
  induction t generalizing s u with
  | zero => classical simp [kernelPower]; positivity
  | succ t ih => exact Finset.sum_nonneg (fun v _ => mul_nonneg (K.nonneg s v) (ih v u))

theorem kernelPower_sum (K : FiniteKernel S) (t : ℕ) (s : S) :
    ∑ u, kernelPower K t s u = 1 := by
  classical
  induction t generalizing s with
  | zero => simp [kernelPower]
  | succ t ih =>
      simp only [kernelPower]
      rw [Finset.sum_comm]
      simp_rw [← Finset.mul_sum, ih, mul_one]
      exact K.sum_eq_one s

theorem rewardAt_eq_kernelPower (K : FiniteKernel S) (c : S → ℝ)
    (t : ℕ) (s : S) : rewardAt K c t s = ∑ u, kernelPower K t s u * c u := by
  classical
  induction t generalizing s with
  | zero => simp [kernelPower]
  | succ t ih =>
      change (∑ v, K.weight s v * rewardAt K c t v) =
        ∑ u, (∑ v, K.weight s v * kernelPower K t v u) * c u
      simp_rw [ih, Finset.mul_sum, Finset.sum_mul]
      rw [Finset.sum_comm]
      simp only [mul_assoc]

theorem rewardAt_succ_le (K : FiniteKernel S) (c : S → ℝ)
    (hdec : ∀ s, expect K c s ≤ c s) (t : ℕ) (s : S) :
    rewardAt K c (t + 1) s ≤ rewardAt K c t s := by
  induction t generalizing s with
  | zero => exact hdec s
  | succ t ih => exact expect_mono K ih s

theorem rewardAt_antitone (K : FiniteKernel S) (c : S → ℝ)
    (hdec : ∀ s, expect K c s ≤ c s) (s : S) :
    Antitone (fun t => rewardAt K c t s) := by
  exact antitone_nat_of_succ_le (fun t => rewardAt_succ_le K c hdec t s)

/-- A quantitative tail bound from nonincreasing one-time expected rewards. -/
theorem rewardAt_le_div_time (K : FiniteKernel S) (c V : S → ℝ)
    (hV : ∀ s, 0 ≤ V s)
    (hstep : ∀ s, c s + expect K V s ≤ V s)
    (hdec : ∀ s, expect K c s ≤ c s) (m : ℕ) (s : S) :
    rewardAt K c m s ≤ V s / ((m : ℝ) + 1) := by
  have hsum : ((m : ℝ) + 1) * rewardAt K c m s ≤ work K c (m + 1) s := by
    rw [work_eq_sum_rewardAt]
    calc
      ((m : ℝ) + 1) * rewardAt K c m s =
          ∑ _t ∈ Finset.range (m + 1), rewardAt K c m s := by simp
      _ ≤ ∑ t ∈ Finset.range (m + 1), rewardAt K c t s := by
        apply Finset.sum_le_sum
        intro t ht
        exact rewardAt_antitone K c hdec s (Nat.le_of_lt_succ (Finset.mem_range.mp ht))
  apply (le_div_iff₀ (show (0 : ℝ) < (m : ℝ) + 1 by positivity)).2
  simpa only [mul_comm] using hsum.trans (work_le_supersolution K c V hV hstep (m + 1) s)

/-- Unit cost on active states. Inactive states cost zero. -/
def activeCost (active : S → Bool) (s : S) : ℝ := if active s then 1 else 0

omit [Fintype S] in
theorem activeCost_nonneg (active : S → Bool) (s : S) : 0 ≤ activeCost active s := by
  unfold activeCost
  split <;> norm_num

omit [Fintype S] in
theorem activeCost_le_one (active : S → Bool) (s : S) : activeCost active s ≤ 1 := by
  unfold activeCost
  split <;> norm_num

/-- Inactive states cannot regain active probability mass. -/
def InactiveAbsorbing (K : FiniteKernel S) (active : S → Bool) : Prop :=
  ∀ s u, active s = false → active u = true → K.weight s u = 0

theorem expect_activeCost_le (K : FiniteKernel S) (active : S → Bool)
    (habs : InactiveAbsorbing K active) (s : S) :
    expect K (activeCost active) s ≤ activeCost active s := by
  cases hs : active s with
  | false =>
      have hz : expect K (activeCost active) s = 0 := by
        apply Finset.sum_eq_zero
        intro u _
        cases hu : active u with
        | false => simp [activeCost, hu]
        | true => simp [activeCost, hu, habs s u hs hu]
      rw [hz]
      simp [activeCost, hs]
  | true =>
      calc
        expect K (activeCost active) s ≤ expect K (fun _ => 1) s :=
          expect_mono K (activeCost_le_one active) s
        _ = activeCost active s := by simp [expect_const, activeCost, hs]

/-- Survival probability at time t, obtained from the finite transition weights. -/
noncomputable def survivalMass (K : FiniteKernel S) (active : S → Bool)
    (t : ℕ) (s : S) : ℝ≥0∞ := ENNReal.ofReal (rewardAt K (activeCost active) t s)

theorem survivalMass_eq_finite_sum (K : FiniteKernel S) (active : S → Bool)
    (t : ℕ) (s : S) : survivalMass K active t s =
      ENNReal.ofReal (∑ u, if active u then kernelPower K t s u else 0) := by
  rw [survivalMass, rewardAt_eq_kernelPower]
  congr 1
  apply Finset.sum_congr rfl
  intro u _
  cases hu : active u <;> simp [activeCost, hu]

theorem survivalMass_antitone (K : FiniteKernel S) (active : S → Bool)
    (habs : InactiveAbsorbing K active) (s : S) :
    Antitone (fun t => survivalMass K active t s) := by
  intro m n hmn
  exact ENNReal.ofReal_le_ofReal
    (rewardAt_antitone K (activeCost active) (expect_activeCost_le K active habs) s hmn)

theorem survivalMass_le_div_time (K : FiniteKernel S) (active : S → Bool)
    (habs : InactiveAbsorbing K active) (V : S → ℝ)
    (hV : ∀ s, 0 ≤ V s)
    (hstep : ∀ s, activeCost active s + expect K V s ≤ V s) (m : ℕ) (s : S) :
    survivalMass K active m s ≤ ENNReal.ofReal (V s / ((m : ℝ) + 1)) := by
  exact ENNReal.ofReal_le_ofReal
    (rewardAt_le_div_time K (activeCost active) V hV hstep
      (expect_activeCost_le K active habs) m s)

theorem survivalMass_tendsto_zero (K : FiniteKernel S) (active : S → Bool)
    (V : S → ℝ) (hV : ∀ s, 0 ≤ V s)
    (hstep : ∀ s, activeCost active s + expect K V s ≤ V s) (s : S) :
    Tendsto (fun t => survivalMass K active t s) atTop (nhds 0) := by
  exact rewardAt_tendsto_zero K (activeCost active) V (activeCost_nonneg active) hV hstep s

/-- The decreasing survival-tail interpretation uses InactiveAbsorbing.
    No path-space measure or unproved expected-termination premise is inserted. -/
theorem survivalMass_iInf_eq_zero (K : FiniteKernel S) (active : S → Bool)
    (V : S → ℝ) (hV : ∀ s, 0 ≤ V s)
    (hstep : ∀ s, activeCost active s + expect K V s ≤ V s) (s : S) :
    (⨅ t : ℕ, survivalMass K active t s) = 0 := by
  apply le_antisymm _ bot_le
  exact ge_of_tendsto' (survivalMass_tendsto_zero K active V hV hstep s)
    (fun t => iInf_le (fun m => survivalMass K active m s) t)

/-- Finite-horizon expected reward under an explicitly supplied initial law. -/
noncomputable def initialWork (K : FiniteKernel S) (μ : S → ℝ) (c : S → ℝ)
    (m : ℕ) : ℝ := ∑ s, μ s * work K c m s

/-- The infinite expected reward is the supremum of the initial-law finite sums. -/
noncomputable def initialTotalWork (K : FiniteKernel S) (μ : S → ℝ) (c : S → ℝ) : ℝ≥0∞ :=
  ⨆ m : ℕ, ENNReal.ofReal (initialWork K μ c m)

/-- The expected single-time reward after averaging the explicit initial law. -/
noncomputable def initialRewardAt (K : FiniteKernel S) (μ : S → ℝ) (c : S → ℝ)
    (t : ℕ) : ℝ := ∑ s, μ s * rewardAt K c t s

theorem initialWork_eq_sum_rewardAt (K : FiniteKernel S) (μ c : S → ℝ) (m : ℕ) :
    initialWork K μ c m = ∑ t ∈ Finset.range m, initialRewardAt K μ c t := by
  simp only [initialWork, initialRewardAt, work_eq_sum_rewardAt, Finset.mul_sum]
  exact Finset.sum_comm

theorem initialTotalWork_eq_tsum (K : FiniteKernel S) (μ c : S → ℝ)
    (hμ : ∀ s, 0 ≤ μ s) (hc : ∀ s, 0 ≤ c s) :
    initialTotalWork K μ c = ∑' t : ℕ, ENNReal.ofReal (initialRewardAt K μ c t) := by
  rw [ENNReal.tsum_eq_iSup_nat]
  apply iSup_congr
  intro m
  rw [initialWork_eq_sum_rewardAt]
  apply ENNReal.ofReal_sum_of_nonneg
  intro t _
  exact Finset.sum_nonneg (fun s _ => mul_nonneg (hμ s) (rewardAt_nonneg K c hc t s))

theorem initialRewardAt_tendsto_zero (K : FiniteKernel S) (μ c : S → ℝ)
    (hμ : ∀ s, 0 ≤ μ s) (hc : ∀ s, 0 ≤ c s)
    (hfinite : initialTotalWork K μ c < ∞) :
    Tendsto (fun t : ℕ => ENNReal.ofReal (initialRewardAt K μ c t)) atTop (nhds 0) := by
  apply ENNReal.tendsto_atTop_zero_of_tsum_ne_top
  rw [← initialTotalWork_eq_tsum K μ c hμ hc]
  exact hfinite.ne

theorem initialWork_le_supersolution (K : FiniteKernel S) (μ c V : S → ℝ)
    (hμ : ∀ s, 0 ≤ μ s) (hV : ∀ s, 0 ≤ V s)
    (hstep : ∀ s, c s + expect K V s ≤ V s) (m : ℕ) :
    initialWork K μ c m ≤ ∑ s, μ s * V s := by
  apply Finset.sum_le_sum
  intro s _
  exact mul_le_mul_of_nonneg_left (work_le_supersolution K c V hV hstep m s) (hμ s)

theorem initialTotalWork_le_supersolution (K : FiniteKernel S) (μ c V : S → ℝ)
    (hμ : ∀ s, 0 ≤ μ s) (hV : ∀ s, 0 ≤ V s)
    (hstep : ∀ s, c s + expect K V s ≤ V s) :
    initialTotalWork K μ c ≤ ENNReal.ofReal (∑ s, μ s * V s) := by
  apply iSup_le
  intro m
  exact ENNReal.ofReal_le_ofReal (initialWork_le_supersolution K μ c V hμ hV hstep m)

theorem initialTotalWork_le_uniform (K : FiniteKernel S) (μ c V : S → ℝ)
    (hμ : ∀ s, 0 ≤ μ s) (hnorm : ∑ s, μ s = 1)
    (hV : ∀ s, 0 ≤ V s) (hstep : ∀ s, c s + expect K V s ≤ V s)
    (B : ℝ) (hB : ∀ s, V s ≤ B) :
    initialTotalWork K μ c ≤ ENNReal.ofReal B := by
  apply (initialTotalWork_le_supersolution K μ c V hμ hV hstep).trans
  apply ENNReal.ofReal_le_ofReal
  calc
    (∑ s, μ s * V s) ≤ ∑ s, μ s * B :=
      Finset.sum_le_sum (fun s _ => mul_le_mul_of_nonneg_left (hB s) (hμ s))
    _ = B := by rw [← Finset.sum_mul, hnorm, one_mul]

theorem initialWork_cost_mono (K : FiniteKernel S) (μ : S → ℝ)
    (hμ : ∀ s, 0 ≤ μ s) {c d : S → ℝ} (hcd : ∀ s, c s ≤ d s) (m : ℕ) :
    initialWork K μ c m ≤ initialWork K μ d m := by
  exact Finset.sum_le_sum (fun s _ =>
    mul_le_mul_of_nonneg_left (work_cost_mono K hcd m s) (hμ s))

theorem initialWork_mul_const (K : FiniteKernel S) (μ c : S → ℝ) (a : ℝ) (m : ℕ) :
    initialWork K μ (fun s => c s * a) m = initialWork K μ c m * a := by
  simp [initialWork, work_mul_const, mul_assoc, Finset.sum_mul]

theorem initialTotalWork_cost_mono (K : FiniteKernel S) (μ : S → ℝ)
    (hμ : ∀ s, 0 ≤ μ s) {c d : S → ℝ} (hcd : ∀ s, c s ≤ d s) :
    initialTotalWork K μ c ≤ initialTotalWork K μ d := by
  apply iSup_mono
  intro m
  exact ENNReal.ofReal_le_ofReal (initialWork_cost_mono K μ hμ hcd m)

theorem initialTotalWork_mul_const (K : FiniteKernel S) (μ c : S → ℝ)
    (a : ℝ) (ha : 0 ≤ a) :
    initialTotalWork K μ (fun s => c s * a) = initialTotalWork K μ c * ENNReal.ofReal a := by
  simp only [initialTotalWork, initialWork_mul_const, ENNReal.ofReal_mul' ha]
  exact (ENNReal.iSup_mul _ _).symm

theorem initialTotalWork_le_mul (K : FiniteKernel S) (μ c d : S → ℝ)
    (hμ : ∀ s, 0 ≤ μ s) (a : ℝ) (ha : 0 ≤ a) (hcd : ∀ s, c s ≤ d s * a) :
    initialTotalWork K μ c ≤ initialTotalWork K μ d * ENNReal.ofReal a := by
  exact (initialTotalWork_cost_mono K μ hμ hcd).trans_eq
    (initialTotalWork_mul_const K μ d a ha)

end MTChainFormal
