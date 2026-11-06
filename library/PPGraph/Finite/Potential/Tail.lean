/-
  First-hit tail probabilities for a finite rational transition kernel.

  The killed first-step recursion computes Pr[T > N] exactly. It requires
  the one-step conditional law, not independence of whole successive states.
  It works even when global accessibility fails. The mean gives a Markov
  upper bound; a checked uniform block bound gives geometric decay.

  Sources: Mitzenmacher--Upfal, Probability and Computing, 2nd ed.,
  Theorem 3.1, p. 47 (Markov inequality), and Section 7.1.1;
  Levin--Peres, Markov Chains and Mixing Times, 2nd ed., Lemma 1.13
  (uniform block escape). These are finite killed-kernel specializations,
  not claims about physical time or deterministic hardware deadlines.
-/

module

public import PPGraph.Finite.Potential.Expectation
public import PPGraph.Finite.Potential.Refutation
public import Mathlib.Analysis.SpecificLimits.Basic

@[expose] public section

set_option linter.unusedSectionVars false

open MeasureTheory Filter
open scoped ENNReal NNReal Topology

namespace FinitePotential

variable {S : Type*} [Fintype S] [DecidableEq S]

/-- Probability of no good state through time N, counting the initial state. -/
def survival (M : FiniteDrift.Model S) : ℕ → S → ℚ
  | 0, s => if M.good s then 0 else 1
  | n + 1, s => if M.good s then 0 else ∑ t, M.transition s t * survival M n t

theorem survival_good (M : FiniteDrift.Model S) (n : ℕ) (s : S)
    (hs : M.good s = true) : survival M n s = 0 := by
  cases n <;> simp [survival, hs]

theorem survival_nonnegative (M : FiniteDrift.Model S) (hm : Stochastic M)
    (n : ℕ) (s : S) : 0 ≤ survival M n s := by
  induction n generalizing s with
  | zero => simp [survival]; split <;> norm_num
  | succ n ih =>
    cases hs : M.good s <;> simp only [survival, hs, Bool.false_eq_true, ↓reduceIte]
    · exact Finset.sum_nonneg (fun t _ => mul_nonneg (hm.1 s t) (ih t))
    · exact le_rfl

theorem survival_le_one (M : FiniteDrift.Model S) (hm : Stochastic M)
    (n : ℕ) (s : S) : survival M n s ≤ 1 := by
  induction n generalizing s with
  | zero => simp [survival]; split <;> norm_num
  | succ n ih =>
    cases hs : M.good s <;> simp only [survival, hs, Bool.false_eq_true, ↓reduceIte]
    · calc
        _ ≤ ∑ t, M.transition s t * 1 := Finset.sum_le_sum
          (fun t _ => mul_le_mul_of_nonneg_left (ih t) (hm.1 s t))
        _ = 1 := by simpa using hm.2 s
    · norm_num

theorem survival_antitone (M : FiniteDrift.Model S) (hm : Stochastic M)
    (s : S) : Antitone (fun n => survival M n s) := by
  have hstep : ∀ n s, survival M (n + 1) s ≤ survival M n s := by
    intro n
    induction n with
    | zero =>
      intro s
      cases hs : M.good s
      · simpa [survival, hs] using survival_le_one M hm 1 s
      · simp [survival, hs]
    | succ n ih =>
      intro s
      cases hs : M.good s <;> simp only [survival, hs, Bool.false_eq_true, ↓reduceIte]
      · exact Finset.sum_le_sum (fun t _ => mul_le_mul_of_nonneg_left (ih t) (hm.1 s t))
      · exact le_rfl
  exact antitone_nat_of_succ_le (fun n => hstep n s)

/-- A uniform bound on one block can be applied after any preceding steps. -/
theorem survival_add_le (M : FiniteDrift.Model S) (hm : Stochastic M)
    (L : ℕ) (b : ℚ) (hb : ∀ s, survival M L s ≤ b) (n : ℕ) (s : S) :
    survival M (n + L) s ≤ b * survival M n s := by
  induction n generalizing s with
  | zero =>
    cases hs : M.good s
    · simpa [survival, hs] using hb s
    · simp [survival_good M L s hs, survival, hs]
  | succ n ih =>
    rw [Nat.succ_add]
    cases hs : M.good s <;> simp only [survival, hs, Bool.false_eq_true, ↓reduceIte]
    · calc
        _ ≤ ∑ t, M.transition s t * (b * survival M n t) :=
          Finset.sum_le_sum (fun t _ => mul_le_mul_of_nonneg_left (ih t) (hm.1 s t))
        _ = _ := by rw [Finset.mul_sum]; apply Finset.sum_congr rfl; intro t _; ring
    · simp

theorem survival_blocks_le (M : FiniteDrift.Model S) (hm : Stochastic M)
    (L : ℕ) (b : ℚ) (hb0 : 0 ≤ b) (hb : ∀ s, survival M L s ≤ b)
    (k : ℕ) (s : S) : survival M (k * L) s ≤ b ^ k := by
  induction k with
  | zero => simpa using survival_le_one M hm 0 s
  | succ k ih =>
    rw [Nat.succ_mul, pow_succ]
    exact (survival_add_le M hm L b hb (k * L) s).trans
      (by nlinarith [mul_le_mul_of_nonneg_left ih hb0])

theorem survival_blocks_tendsto_zero (M : FiniteDrift.Model S) (hm : Stochastic M)
    (L : ℕ) (b : ℚ) (hb0 : 0 ≤ b) (hb1 : b < 1)
    (hb : ∀ s, survival M L s ≤ b) (s : S) :
    Tendsto (fun k => (survival M (k * L) s : ℝ)) atTop (𝓝 0) := by
  have hb0' : (0 : ℝ) ≤ (b : ℝ) := by exact_mod_cast hb0
  have hb1' : (b : ℝ) < 1 := by exact_mod_cast hb1
  apply squeeze_zero (fun k => by exact_mod_cast survival_nonnegative M hm (k * L) s)
    (fun k => by exact_mod_cast survival_blocks_le M hm L b hb0 hb k s)
    (tendsto_pow_atTop_nhds_zero_of_lt_one hb0' hb1')

theorem survival_closedBad (M : FiniteDrift.Model S) (hm : Stochastic M)
    (U : S → Bool) (hu : ClosedBad M U) (n : ℕ) (s : S) (hs : U s = true) :
    survival M n s = 1 := by
  induction n generalizing s with
  | zero => simp [survival, hu.2.1 s hs]
  | succ n ih =>
    simp only [survival, hu.2.1 s hs, Bool.false_eq_true, ↓reduceIte]
    calc
      _ = ∑ t, M.transition s t := by
        apply Finset.sum_congr rfl
        intro t _
        cases ht : U t
        · simp [hu.2.2 s t hs ht]
        · rw [ih t ht, mul_one]
      _ = 1 := hm.2 s

variable {Ω : Type*} [MeasurableSpace S] [MeasurableSingletonClass S]
    [mΩ : MeasurableSpace Ω]

theorem stoppedValue_shift_of_good_zero (M : FiniteDrift.Model S) (f : S → ℚ)
    (hf : ∀ s, M.good s = true → f s = 0) (X : ℕ → Ω → S) (n : ℕ) :
    stoppedValue M f X (n + 1) =
      (FiniteDrift.runningEvent M X n).indicator (fun ω => (f (X (n + 1) ω) : ℝ)) := by
  funext ω
  unfold stoppedValue
  rw [runningEvent_succ]
  by_cases hr : ω ∈ FiniteDrift.runningEvent M X n
  · cases hg : M.good (X (n + 1) ω)
    · have ha : ω ∈ FiniteDrift.activeEvent M X (n + 1) := hg
      have hboth : ω ∈ FiniteDrift.runningEvent M X n ∩ FiniteDrift.activeEvent M X (n + 1) := ⟨hr, ha⟩
      rw [Set.indicator_of_mem hboth, Set.indicator_of_mem hr]
    · have ha : ω ∉ FiniteDrift.activeEvent M X (n + 1) := by
        change ¬ M.good (X (n + 1) ω) = false
        simp [hg]
      rw [Set.indicator_of_notMem (fun h => ha h.2), Set.indicator_of_mem hr, hf _ hg]
      simp
  · rw [Set.indicator_of_notMem (fun h => hr h.1), Set.indicator_of_notMem hr]

theorem stopped_survival_zero (M : FiniteDrift.Model S) (X : ℕ → Ω → S) (n : ℕ) :
    stoppedValue M (survival M 0) X n =
      (FiniteDrift.runningEvent M X n).indicator (fun _ => (1 : ℝ)) := by
  funext ω
  by_cases hr : ω ∈ FiniteDrift.runningEvent M X n
  · simp [stoppedValue, Set.indicator_of_mem hr, survival, hr n le_rfl]
  · simp [stoppedValue, Set.indicator_of_notMem hr]

theorem stopped_survival_initial (M : FiniteDrift.Model S) (X : ℕ → Ω → S) (N : ℕ) :
    stoppedValue M (survival M N) X 0 = fun ω => (survival M N (X 0 ω) : ℝ) := by
  funext ω
  cases hg : M.good (X 0 ω)
  · have hr : ω ∈ FiniteDrift.runningEvent M X 0 := fun k hk => by
      have : k = 0 := Nat.eq_zero_of_le_zero hk
      simpa [this] using hg
    exact Set.indicator_of_mem hr _
  · have hr : ω ∉ FiniteDrift.runningEvent M X 0 := by
      intro h
      simpa [hg] using h 0 le_rfl
    simp [stoppedValue, Set.indicator_of_notMem hr, survival_good M N _ hg]

theorem stopped_survival_integral_step (M : FiniteDrift.Model S)
    (μ : Measure Ω) [IsFiniteMeasure μ] (history : Filtration ℕ mΩ)
    (X : ℕ → Ω → S) (L : FiniteDrift.Realization M μ history X) (n k : ℕ) :
    (∫ ω, stoppedValue M (survival M k) X (n + 1) ω ∂μ) =
      ∫ ω, stoppedValue M (survival M (k + 1)) X n ω ∂μ := by
  rw [stoppedValue_shift_of_good_zero M _ (survival_good M k) X n]
  have hi := FiniteDrift.integrable_finite_value μ (fun s => (survival M k s : ℝ))
    (X (n + 1)) (FiniteDrift.realization_measurable M μ history X L (n + 1))
  have hp := condExp_indicator hi (runningEvent_measurable_history M μ history X L n)
  have hn := FiniteDrift.conditional_next_value M μ history X L
    (fun s => (survival M k s : ℝ)) n
  have he : μ[(FiniteDrift.runningEvent M X n).indicator
      (fun ω => (survival M k (X (n + 1) ω) : ℝ)) | history n] =ᵐ[μ]
      stoppedValue M (survival M (k + 1)) X n := by
    filter_upwards [hp, hn] with ω hpω hnω
    rw [hpω]
    by_cases hr : ω ∈ FiniteDrift.runningEvent M X n
    · rw [Set.indicator_of_mem hr, hnω, stoppedValue, Set.indicator_of_mem hr]
      simp [survival, hr n le_rfl]
    · rw [Set.indicator_of_notMem hr, stoppedValue, Set.indicator_of_notMem hr]
  calc
    _ = ∫ ω, (μ[(FiniteDrift.runningEvent M X n).indicator
        (fun ω => (survival M k (X (n + 1) ω) : ℝ)) | history n]) ω ∂μ :=
      (integral_condExp (history.le n)).symm
    _ = _ := integral_congr_ae he

theorem stopped_survival_integral_horizon (M : FiniteDrift.Model S)
    (μ : Measure Ω) [IsFiniteMeasure μ] (history : Filtration ℕ mΩ)
    (X : ℕ → Ω → S) (L : FiniteDrift.Realization M μ history X) (n N : ℕ) :
    (∫ ω, stoppedValue M (survival M N) X n ω ∂μ) =
      μ.real (FiniteDrift.runningEvent M X (n + N)) := by
  induction N generalizing n with
  | zero =>
    rw [stopped_survival_zero, integral_indicator_const _
      (FiniteDrift.runningEvent_measurable M X (FiniteDrift.realization_measurable M μ history X L) n)]
    simp
  | succ N ih =>
    rw [← stopped_survival_integral_step M μ history X L n N, ih]
    congr 2
    omega

/-- Exact timeout probability, without accessibility or termination premises. -/
theorem running_measure_eq_survival (M : FiniteDrift.Model S)
    (μ : Measure Ω) [IsFiniteMeasure μ] (history : Filtration ℕ mΩ)
    (X : ℕ → Ω → S) (L : FiniteDrift.Realization M μ history X) (N : ℕ) :
    μ (FiniteDrift.runningEvent M X N) =
      ENNReal.ofReal (∫ ω, (survival M N (X 0 ω) : ℝ) ∂μ) := by
  have hh := stopped_survival_integral_horizon M μ history X L 0 N
  rw [stopped_survival_initial] at hh
  simpa using (congrArg ENNReal.ofReal hh).symm

theorem running_measure_fixed_eq_survival (M : FiniteDrift.Model S)
    (μ : Measure Ω) [IsProbabilityMeasure μ] (history : Filtration ℕ mΩ)
    (X : ℕ → Ω → S) (L : FiniteDrift.Realization M μ history X)
    (s₀ : S) (hi : ∀ ω, X 0 ω = s₀) (N : ℕ) :
    μ (FiniteDrift.runningEvent M X N) = ENNReal.ofReal (survival M N s₀ : ℝ) := by
  simpa only [hi, integral_const, probReal_univ, one_smul] using
    running_measure_eq_survival M μ history X L N

theorem runningEvent_eq_hitCount_gt (M : FiniteDrift.Model S) (X : ℕ → Ω → S) (N : ℕ) :
    FiniteDrift.runningEvent M X N = {ω | (N : ℝ≥0∞) < FiniteDrift.hitCount M X ω} := by
  ext ω
  constructor
  · intro hr
    have hsum : (N + 1 : ℝ≥0∞) ≤ FiniteDrift.hitCount M X ω := by
      have he : (∑ n ∈ Finset.range (N + 1),
          (FiniteDrift.runningEvent M X n).indicator (fun _ => (1 : ℝ≥0∞)) ω) = N + 1 := by
        calc
          _ = ∑ _n ∈ Finset.range (N + 1), (1 : ℝ≥0∞) := by
            apply Finset.sum_congr rfl
            intro n hn
            have hmem : ω ∈ FiniteDrift.runningEvent M X n := fun k hk => hr k
              (le_trans hk (Nat.le_of_lt_succ (Finset.mem_range.mp hn)))
            exact Set.indicator_of_mem hmem _
          _ = _ := by simp
      rw [← he]
      exact ENNReal.sum_le_tsum (Finset.range (N + 1))
    exact lt_of_lt_of_le (by exact_mod_cast Nat.lt_succ_self N) hsum
  · intro hh k hk
    cases hg : M.good (X k ω)
    · rfl
    · have hb := FiniteDrift.hitCount_le_of_good M X ω k hg
      have hk' : (k : ℝ≥0∞) ≤ N := by exact_mod_cast hk
      exact False.elim ((not_le_of_gt hh) (hb.trans hk'))

/-- Integer-valued first-hit Markov bound, including the N=0 endpoint. -/
theorem running_measure_le_mean_div (M : FiniteDrift.Model S)
    (μ : Measure Ω) (X : ℕ → Ω → S) (hX : ∀ n, Measurable (X n)) (N : ℕ) :
    μ (FiniteDrift.runningEvent M X N) ≤ FiniteDrift.expectedHitCount M μ X / (N + 1) := by
  have hsum : (N + 1 : ℝ≥0∞) * μ (FiniteDrift.runningEvent M X N) ≤
      ∑ n ∈ Finset.range (N + 1), μ (FiniteDrift.runningEvent M X n) := by
    calc
      _ = ∑ _n ∈ Finset.range (N + 1), μ (FiniteDrift.runningEvent M X N) := by simp
      _ ≤ _ := Finset.sum_le_sum (fun n hn => measure_mono
        (fun _ hr k hk => hr k (le_trans hk (Nat.le_of_lt_succ (Finset.mem_range.mp hn)))))
  have ht : (∑ n ∈ Finset.range (N + 1), μ (FiniteDrift.runningEvent M X n)) ≤
      FiniteDrift.expectedHitCount M μ X := by
    change (∑ n ∈ Finset.range (N + 1), μ (FiniteDrift.runningEvent M X n)) ≤
      RepairDrift.expectedActiveCount μ (FiniteDrift.runningEvent M X)
    rw [RepairDrift.expectedActiveCount_eq_tsum μ _ (FiniteDrift.runningEvent_measurable M X hX)]
    exact ENNReal.sum_le_tsum _
  apply (ENNReal.le_div_iff_mul_le (Or.inl (by positivity)) (Or.inl (by finiteness))).mpr
  simpa only [mul_comm] using hsum.trans ht

theorem running_measure_fixed_le_potential (M : FiniteDrift.Model S) (f : S → ℚ)
    (hm : Stochastic M) (ha : Absorbing M) (he : Equations M f)
    (μ : Measure Ω) [IsProbabilityMeasure μ] (history : Filtration ℕ mΩ)
    (X : ℕ → Ω → S) (L : FiniteDrift.Realization M μ history X)
    (s₀ : S) (hi : ∀ ω, X 0 ω = s₀) (N : ℕ) :
    μ (FiniteDrift.runningEvent M X N) ≤ ENNReal.ofReal (f s₀ : ℝ) / (N + 1) := by
  rw [← expectedHitCount_fixed_eq_of_equations M f hm ha he μ history X L s₀ hi]
  exact running_measure_le_mean_div M μ X (FiniteDrift.realization_measurable M μ history X L) N

theorem running_measure_fixed_blocks_le (M : FiniteDrift.Model S) (hm : Stochastic M)
    (Lblock : ℕ) (b : ℚ) (hb0 : 0 ≤ b) (hb : ∀ s, survival M Lblock s ≤ b)
    (μ : Measure Ω) [IsProbabilityMeasure μ] (history : Filtration ℕ mΩ)
    (X : ℕ → Ω → S) (L : FiniteDrift.Realization M μ history X)
    (s₀ : S) (hi : ∀ ω, X 0 ω = s₀) (k : ℕ) :
    μ (FiniteDrift.runningEvent M X (k * Lblock)) ≤ ENNReal.ofReal (b ^ k : ℝ) := by
  rw [running_measure_fixed_eq_survival M μ history X L s₀ hi]
  apply ENNReal.ofReal_le_ofReal
  exact_mod_cast survival_blocks_le M hm Lblock b hb0 hb k s₀

theorem running_measure_blocks_le (M : FiniteDrift.Model S) (hm : Stochastic M)
    (Lblock : ℕ) (b : ℚ) (hb0 : 0 ≤ b) (hb : ∀ s, survival M Lblock s ≤ b)
    (μ : Measure Ω) [IsProbabilityMeasure μ] (history : Filtration ℕ mΩ)
    (X : ℕ → Ω → S) (L : FiniteDrift.Realization M μ history X) (k : ℕ) :
    μ (FiniteDrift.runningEvent M X (k * Lblock)) ≤ ENNReal.ofReal (b ^ k : ℝ) := by
  rw [running_measure_eq_survival M μ history X L (k * Lblock)]
  apply ENNReal.ofReal_le_ofReal
  have hi : Integrable (fun ω => (survival M (k * Lblock) (X 0 ω) : ℝ)) μ :=
    FiniteDrift.integrable_finite_value μ (fun s => (survival M (k * Lblock) s : ℝ))
      (X 0) (FiniteDrift.realization_measurable M μ history X L 0)
  have hb' (ω : Ω) : (survival M (k * Lblock) (X 0 ω) : ℝ) ≤ (b ^ k : ℝ) := by
    exact_mod_cast survival_blocks_le M hm Lblock b hb0 hb k (X 0 ω)
  simpa only [integral_const, probReal_univ, one_smul] using
    integral_mono hi (integrable_const (b ^ k : ℝ)) hb'

theorem running_measure_closedBad_eq_one (M : FiniteDrift.Model S) (hm : Stochastic M)
    (U : S → Bool) (hc : checkClosedBad M U = true)
    (μ : Measure Ω) [IsProbabilityMeasure μ] (history : Filtration ℕ mΩ)
    (X : ℕ → Ω → S) (L : FiniteDrift.Realization M μ history X)
    (s₀ : S) (hs : U s₀ = true) (hi : ∀ ω, X 0 ω = s₀) (N : ℕ) :
    μ (FiniteDrift.runningEvent M X N) = 1 := by
  rw [running_measure_fixed_eq_survival M μ history X L s₀ hi,
    survival_closedBad M hm U ((checkClosedBad_iff M U).mp hc) N s₀ hs]
  simp

theorem expectedHitCount_closedBad_eq_top (M : FiniteDrift.Model S) (hm : Stochastic M)
    (U : S → Bool) (hc : checkClosedBad M U = true)
    (μ : Measure Ω) [IsProbabilityMeasure μ] (history : Filtration ℕ mΩ)
    (X : ℕ → Ω → S) (L : FiniteDrift.Realization M μ history X)
    (s₀ : S) (hs : U s₀ = true) (hi : ∀ ω, X 0 ω = s₀) :
    FiniteDrift.expectedHitCount M μ X = ⊤ := by
  change RepairDrift.expectedActiveCount μ (FiniteDrift.runningEvent M X) = ⊤
  rw [RepairDrift.expectedActiveCount_eq_tsum μ _
    (FiniteDrift.runningEvent_measurable M X (FiniteDrift.realization_measurable M μ history X L))]
  simp_rw [running_measure_closedBad_eq_one M hm U hc μ history X L s₀ hs hi]
  exact ENNReal.tsum_const_eq_top_of_ne_zero one_ne_zero

theorem ae_never_good_closedBad (M : FiniteDrift.Model S) (hm : Stochastic M)
    (U : S → Bool) (hc : checkClosedBad M U = true)
    (μ : Measure Ω) [IsProbabilityMeasure μ] (history : Filtration ℕ mΩ)
    (X : ℕ → Ω → S) (L : FiniteDrift.Realization M μ history X)
    (s₀ : S) (hs : U s₀ = true) (hi : ∀ ω, X 0 ω = s₀) :
    ∀ᵐ ω ∂μ, ∀ n, M.good (X n ω) = false := by
  have hae : ∀ n, ∀ᵐ ω ∂μ, ω ∈ FiniteDrift.runningEvent M X n := by
    intro n
    have hmeas := FiniteDrift.runningEvent_measurable M X
      (FiniteDrift.realization_measurable M μ history X L) n
    apply (ae_iff_measure_eq hmeas.nullMeasurableSet).mpr
    simpa only [measure_univ, FiniteDrift.runningEvent, Set.mem_ofPred_eq] using
      running_measure_closedBad_eq_one M hm U hc μ history X L s₀ hs hi n
  filter_upwards [ae_all_iff.mpr hae] with ω hω
  intro n
  exact hω n n le_rfl

end FinitePotential

#check @FinitePotential.survival_good
#check @FinitePotential.survival_nonnegative
#check @FinitePotential.survival_le_one
#check @FinitePotential.survival_antitone
#check @FinitePotential.survival_add_le
#check @FinitePotential.survival_blocks_le
#check @FinitePotential.survival_blocks_tendsto_zero
#check @FinitePotential.survival_closedBad
#check @FinitePotential.stoppedValue_shift_of_good_zero
#check @FinitePotential.stopped_survival_zero
#check @FinitePotential.stopped_survival_initial
#check @FinitePotential.stopped_survival_integral_step
#check @FinitePotential.stopped_survival_integral_horizon
#check @FinitePotential.running_measure_eq_survival
#check @FinitePotential.running_measure_fixed_eq_survival
#check @FinitePotential.runningEvent_eq_hitCount_gt
#check @FinitePotential.running_measure_le_mean_div
#check @FinitePotential.running_measure_fixed_le_potential
#check @FinitePotential.running_measure_fixed_blocks_le
#check @FinitePotential.running_measure_blocks_le
#check @FinitePotential.running_measure_closedBad_eq_one
#check @FinitePotential.expectedHitCount_closedBad_eq_top
#check @FinitePotential.ae_never_good_closedBad
