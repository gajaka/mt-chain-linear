/-
  First-step potentials equal the expected first-hit work.

  Source: Levin--Peres, Markov Chains and Mixing Times, 2nd ed.,
  Exercise 10.22(a), printed p. 149; Mitzenmacher--Upfal, Probability
  and Computing, 2nd ed., Section 7.1.1, pp. 173--174.

  This is the finite rational stopped-model specialization. Conditional
  transition probabilities determine an exact stopped-potential telescope.
  Finiteness and almost-sure success are derived by the existing drift
  theorem. Boundedness of a finite state function then permits dominated
  convergence, so the residual budget vanishes. No optional-stopping or
  termination premise is supplied. This concerns steps, not hardware time.
-/

module

public import PPGraph.Finite.Potential.Basic
public import PPGraph.Finite.Drift.Process
public import Mathlib.MeasureTheory.Function.ConditionalExpectation.Indicator
public import Mathlib.MeasureTheory.Integral.DominatedConvergence

@[expose] public section

set_option linter.unusedSectionVars false

open MeasureTheory Filter
open scoped ENNReal NNReal Topology

namespace FinitePotential

variable {S Ω : Type*} [Fintype S] [DecidableEq S]
  [MeasurableSpace S] [MeasurableSingletonClass S] [mΩ : MeasurableSpace Ω]

/-- Evaluate the state potential only while the first success has not occurred. -/
noncomputable def stoppedValue (M : FiniteDrift.Model S) (f : S → ℚ)
    (X : ℕ → Ω → S) (n : ℕ) : Ω → ℝ :=
  (FiniteDrift.runningEvent M X n).indicator (fun ω => (f (X n ω) : ℝ))

theorem runningEvent_succ (M : FiniteDrift.Model S) (X : ℕ → Ω → S) (n : ℕ) :
    FiniteDrift.runningEvent M X (n + 1) =
      FiniteDrift.runningEvent M X n ∩ FiniteDrift.activeEvent M X (n + 1) := by
  ext ω
  change (∀ k ≤ n + 1, M.good (X k ω) = false) ↔
    (∀ k ≤ n, M.good (X k ω) = false) ∧ M.good (X (n + 1) ω) = false
  constructor
  · intro h
    exact ⟨fun k hk => h k (by omega), h (n + 1) le_rfl⟩
  · rintro ⟨h, hnext⟩ k hk
    by_cases heq : k = n + 1
    · simpa [heq] using hnext
    · exact h k (by omega)

theorem runningEvent_measurable_history (M : FiniteDrift.Model S) (μ : Measure Ω)
    (history : Filtration ℕ mΩ) (X : ℕ → Ω → S)
    (L : FiniteDrift.Realization M μ history X) (n : ℕ) :
    MeasurableSet[history n] (FiniteDrift.runningEvent M X n) := by
  have heq : FiniteDrift.runningEvent M X n =
      ⋂ k ∈ Finset.range (n + 1), FiniteDrift.activeEvent M X k := by
    ext ω
    simp [FiniteDrift.runningEvent, FiniteDrift.activeEvent]
  rw [heq]
  apply Finset.measurableSet_biInter
  intro k hk
  exact (history.mono (Nat.le_of_lt_succ (Finset.mem_range.mp hk))) _
    (FiniteDrift.activeEvent_measurable_history M μ history X L k)

theorem stoppedValue_initial (M : FiniteDrift.Model S) (f : S → ℚ)
    (he : Equations M f) (X : ℕ → Ω → S) :
    stoppedValue M f X 0 = fun ω => (f (X 0 ω) : ℝ) := by
  funext ω
  cases hs : M.good (X 0 ω)
  · simp [stoppedValue, FiniteDrift.runningEvent, hs]
  · simp [stoppedValue, FiniteDrift.runningEvent, hs, he.1 _ hs]

/-- The next good state has zero potential, so the previous running event suffices. -/
theorem stoppedValue_shift (M : FiniteDrift.Model S) (f : S → ℚ)
    (he : Equations M f) (X : ℕ → Ω → S) (n : ℕ) :
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
      rw [Set.indicator_of_notMem (fun h => ha h.2), Set.indicator_of_mem hr, he.1 _ hg]
      simp
  · rw [Set.indicator_of_notMem (fun h => hr h.1), Set.indicator_of_notMem hr]

theorem stoppedValue_nonnegative (M : FiniteDrift.Model S) (f : S → ℚ)
    (hf : ∀ s, 0 ≤ f s) (X : ℕ → Ω → S) (n : ℕ) (ω : Ω) :
    0 ≤ stoppedValue M f X n ω := by
  apply Set.indicator_nonneg _ ω
  intro _ _
  exact_mod_cast hf _

theorem stoppedValue_norm_le_sum (M : FiniteDrift.Model S) (f : S → ℚ)
    (hf : ∀ s, 0 ≤ f s) (X : ℕ → Ω → S) (n : ℕ) (ω : Ω) :
    ‖stoppedValue M f X n ω‖ ≤ ∑ s, (f s : ℝ) := by
  have hreal (s : S) : (0 : ℝ) ≤ (f s : ℝ) := by exact_mod_cast hf s
  have hsum : (0 : ℝ) ≤ ∑ s, (f s : ℝ) := Finset.sum_nonneg (fun s _ => hreal s)
  by_cases hr : ω ∈ FiniteDrift.runningEvent M X n
  · rw [stoppedValue, Set.indicator_of_mem hr, Real.norm_eq_abs, abs_of_nonneg (hreal _)]
    exact Finset.single_le_sum (fun s _ => hreal s) (Finset.mem_univ _)
  · rw [stoppedValue, Set.indicator_of_notMem hr, norm_zero]
    exact hsum

theorem stoppedValue_measurable (M : FiniteDrift.Model S) (f : S → ℚ)
    (μ : Measure Ω) (history : Filtration ℕ mΩ) (X : ℕ → Ω → S)
    (L : FiniteDrift.Realization M μ history X) (n : ℕ) :
    Measurable (stoppedValue M f X n) :=
  ((measurable_of_finite (fun s => (f s : ℝ))).comp
    (FiniteDrift.realization_measurable M μ history X L n)).indicator
    (FiniteDrift.runningEvent_measurable M X
      (FiniteDrift.realization_measurable M μ history X L) n)

theorem stoppedValue_integrable (M : FiniteDrift.Model S) (f : S → ℚ)
    (μ : Measure Ω) [IsFiniteMeasure μ] (history : Filtration ℕ mΩ)
    (X : ℕ → Ω → S) (L : FiniteDrift.Realization M μ history X) (n : ℕ) :
    Integrable (stoppedValue M f X n) μ :=
  (FiniteDrift.integrable_finite_value μ (fun s => (f s : ℝ)) (X n)
    (FiniteDrift.realization_measurable M μ history X L n)).indicator
    (FiniteDrift.runningEvent_measurable M X
      (FiniteDrift.realization_measurable M μ history X L) n)

theorem equations_real_bad (M : FiniteDrift.Model S) (f : S → ℚ)
    (he : Equations M f) (s : S) (hs : M.good s = false) :
    (∑ t, (M.transition s t : ℝ) * (f t : ℝ)) + 1 = (f s : ℝ) := by
  have hh : (f s : ℝ) = 1 + ∑ t, (M.transition s t : ℝ) * (f t : ℝ) := by
    exact_mod_cast he.2 s hs
  linarith

/-- Exact conditional decrease by one active step; this is not a termination premise. -/
theorem stoppedValue_conditional_exact (M : FiniteDrift.Model S) (f : S → ℚ)
    (he : Equations M f) (μ : Measure Ω) [IsFiniteMeasure μ]
    (history : Filtration ℕ mΩ) (X : ℕ → Ω → S)
    (L : FiniteDrift.Realization M μ history X) (n : ℕ) :
    ∀ᵐ ω ∂μ, (μ[stoppedValue M f X (n + 1) | history n]) ω +
      (FiniteDrift.runningEvent M X n).indicator (fun _ => (1 : ℝ)) ω =
        stoppedValue M f X n ω := by
  rw [stoppedValue_shift M f he X n]
  have hi := FiniteDrift.integrable_finite_value μ (fun s => (f s : ℝ)) (X (n + 1))
    (FiniteDrift.realization_measurable M μ history X L (n + 1))
  have hp := condExp_indicator hi (runningEvent_measurable_history M μ history X L n)
  have hn := FiniteDrift.conditional_next_value M μ history X L (fun s => (f s : ℝ)) n
  filter_upwards [hp, hn] with ω hpω hnω
  rw [hpω]
  by_cases hr : ω ∈ FiniteDrift.runningEvent M X n
  · rw [Set.indicator_of_mem hr, Set.indicator_of_mem hr, hnω,
      stoppedValue, Set.indicator_of_mem hr]
    exact equations_real_bad M f he _ (hr n le_rfl)
  · rw [Set.indicator_of_notMem hr, Set.indicator_of_notMem hr,
      stoppedValue, Set.indicator_of_notMem hr]
    simp

theorem stoppedValue_integrated_exact (M : FiniteDrift.Model S) (f : S → ℚ)
    (hm : Stochastic M) (he : Equations M f) (μ : Measure Ω) [IsFiniteMeasure μ]
    (history : Filtration ℕ mΩ) (X : ℕ → Ω → S)
    (L : FiniteDrift.Realization M μ history X) (n : ℕ) :
    μ (FiniteDrift.runningEvent M X n) +
      ENNReal.ofReal (∫ ω, stoppedValue M f X (n + 1) ω ∂μ) =
      ENNReal.ofReal (∫ ω, stoppedValue M f X n ω ∂μ) := by
  have hs := FiniteDrift.runningEvent_measurable M X
    (FiniteDrift.realization_measurable M μ history X L) n
  have hi : Integrable ((FiniteDrift.runningEvent M X n).indicator (fun _ => (1 : ℝ))) μ :=
    (integrable_const _).indicator hs
  have hre := integral_congr_ae (stoppedValue_conditional_exact M f he μ history X L n)
  rw [integral_add integrable_condExp hi, integral_condExp (history.le n),
    integral_indicator_const _ hs, smul_eq_mul, mul_one] at hre
  have hn : 0 ≤ ∫ ω, stoppedValue M f X (n + 1) ω ∂μ :=
    integral_nonneg_of_ae (Eventually.of_forall
      (stoppedValue_nonnegative M f (solution_nonnegative M hm f he) X (n + 1)))
  have ht : 0 ≤ μ.real (FiniteDrift.runningEvent M X n) := by positivity
  have hmeasure : ENNReal.ofReal (μ.real (FiniteDrift.runningEvent M X n)) =
      μ (FiniteDrift.runningEvent M X n) := ENNReal.ofReal_toReal (measure_ne_top μ _)
  have henn := congrArg ENNReal.ofReal hre
  rw [ENNReal.ofReal_add hn ht, hmeasure] at henn
  simpa only [add_comm] using henn

theorem finite_horizon_exact (M : FiniteDrift.Model S) (f : S → ℚ)
    (hm : Stochastic M) (he : Equations M f) (μ : Measure Ω) [IsFiniteMeasure μ]
    (history : Filtration ℕ mΩ) (X : ℕ → Ω → S)
    (L : FiniteDrift.Realization M μ history X) (N : ℕ) :
    (∑ n ∈ Finset.range N, μ (FiniteDrift.runningEvent M X n)) +
      ENNReal.ofReal (∫ ω, stoppedValue M f X N ω ∂μ) =
      ENNReal.ofReal (∫ ω, (f (X 0 ω) : ℝ) ∂μ) := by
  induction N with
  | zero => simp [stoppedValue_initial M f he X]
  | succ N ih =>
    rw [Finset.sum_range_succ, add_assoc, stoppedValue_integrated_exact M f hm he μ history X L N]
    exact ih

theorem stoppedValue_zero_after_good (M : FiniteDrift.Model S) (f : S → ℚ)
    (X : ℕ → Ω → S) (ω : Ω) (T n : ℕ) (hg : M.good (X T ω) = true)
    (hn : T ≤ n) : stoppedValue M f X n ω = 0 := by
  apply Set.indicator_of_notMem
  intro hr
  have hb := hr T hn
  exact Bool.false_ne_true (hb.symm.trans hg)

/-- Drift proves success first; no almost-sure termination hypothesis is used. -/
theorem stoppedValue_ae_tendsto_zero (M : FiniteDrift.Model S) (f : S → ℚ)
    (hc : FiniteDrift.check M ⟨f, 1⟩ = true)
    (μ : Measure Ω) [IsFiniteMeasure μ] (history : Filtration ℕ mΩ)
    (X : ℕ → Ω → S) (L : FiniteDrift.Realization M μ history X) :
    ∀ᵐ ω ∂μ, Tendsto (fun n => stoppedValue M f X n ω) atTop (𝓝 0) := by
  filter_upwards [FiniteDrift.ae_exists_good M ⟨f, 1⟩ hc μ history X L] with ω hω
  obtain ⟨T, hT⟩ := hω
  apply tendsto_const_nhds.congr'
  filter_upwards [eventually_ge_atTop T] with n hn
  exact (stoppedValue_zero_after_good M f X ω T n hT hn).symm

theorem stoppedValue_integral_tendsto_zero (M : FiniteDrift.Model S) (f : S → ℚ)
    (hc : FiniteDrift.check M ⟨f, 1⟩ = true)
    (μ : Measure Ω) [IsFiniteMeasure μ] (history : Filtration ℕ mΩ)
    (X : ℕ → Ω → S) (L : FiniteDrift.Realization M μ history X) :
    Tendsto (fun n => ∫ ω, stoppedValue M f X n ω ∂μ) atTop (𝓝 0) := by
  have hf : ∀ s, 0 ≤ f s := FiniteDrift.potential_nonnegative M ⟨f, 1⟩ hc
  have hd := tendsto_integral_of_dominated_convergence (μ := μ) (f := fun _ : Ω => (0 : ℝ))
    (fun _ => ∑ s, (f s : ℝ))
    (fun n => (stoppedValue_measurable M f μ history X L n).aestronglyMeasurable)
    (integrable_const _)
    (fun n => Eventually.of_forall (stoppedValue_norm_le_sum M f hf X n))
    (stoppedValue_ae_tendsto_zero M f hc μ history X L)
  simpa using hd

/-- Exact expectation for any faithful realization of this stopped finite kernel. -/
theorem expectedHitCount_eq_of_equations (M : FiniteDrift.Model S) (f : S → ℚ)
    (hm : Stochastic M) (ha : Absorbing M) (he : Equations M f)
    (μ : Measure Ω) [IsFiniteMeasure μ] (history : Filtration ℕ mΩ)
    (X : ℕ → Ω → S) (L : FiniteDrift.Realization M μ history X) :
    FiniteDrift.expectedHitCount M μ X =
      ENNReal.ofReal (∫ ω, (f (X 0 ω) : ℝ) ∂μ) := by
  have hc := solution_checked M hm ha f he
  have hseries : FiniteDrift.expectedHitCount M μ X =
      ∑' n, μ (FiniteDrift.runningEvent M X n) :=
    RepairDrift.expectedActiveCount_eq_tsum μ _ (FiniteDrift.runningEvent_measurable M X
      (FiniteDrift.realization_measurable M μ history X L))
  have hs : Tendsto (fun N => ∑ n ∈ Finset.range N, μ (FiniteDrift.runningEvent M X n))
      atTop (𝓝 (FiniteDrift.expectedHitCount M μ X)) := by
    rw [hseries]
    exact ENNReal.tendsto_nat_tsum _
  have hb : Tendsto (fun N => ENNReal.ofReal (∫ ω, stoppedValue M f X N ω ∂μ))
      atTop (𝓝 0) := by
    simpa using ENNReal.tendsto_ofReal (stoppedValue_integral_tendsto_zero M f hc μ history X L)
  have hsum := hs.add hb
  have hconst : Tendsto (fun N => (∑ n ∈ Finset.range N, μ (FiniteDrift.runningEvent M X n)) +
      ENNReal.ofReal (∫ ω, stoppedValue M f X N ω ∂μ))
      atTop (𝓝 (ENNReal.ofReal (∫ ω, (f (X 0 ω) : ℝ) ∂μ))) := by
    apply tendsto_const_nhds.congr'
    exact Eventually.of_forall (fun N => (finite_horizon_exact M f hm he μ history X L N).symm)
  simpa using tendsto_nhds_unique hsum hconst

theorem expectedHitCount_fixed_eq_of_equations (M : FiniteDrift.Model S) (f : S → ℚ)
    (hm : Stochastic M) (ha : Absorbing M) (he : Equations M f)
    (μ : Measure Ω) [IsProbabilityMeasure μ] (history : Filtration ℕ mΩ)
    (X : ℕ → Ω → S) (L : FiniteDrift.Realization M μ history X)
    (s₀ : S) (hi : ∀ ω, X 0 ω = s₀) :
    FiniteDrift.expectedHitCount M μ X = ENNReal.ofReal (f s₀ : ℝ) := by
  simpa only [hi, integral_const, probReal_univ, one_smul] using
    expectedHitCount_eq_of_equations M f hm ha he μ history X L

theorem potential_expectedHitCount_eq (M : FiniteDrift.Model S)
    (hm : Stochastic M) (ha : Absorbing M) (hr : Accessible M)
    (μ : Measure Ω) [IsFiniteMeasure μ] (history : Filtration ℕ mΩ)
    (X : ℕ → Ω → S) (L : FiniteDrift.Realization M μ history X) :
    FiniteDrift.expectedHitCount M μ X =
      ENNReal.ofReal (∫ ω, (potential M (X 0 ω) : ℝ) ∂μ) :=
  expectedHitCount_eq_of_equations M _ hm ha
    (potential_equations M (det_ne_zero_of_accessible M hm hr)) μ history X L

theorem potential_expectedHitCount_fixed_eq (M : FiniteDrift.Model S)
    (hm : Stochastic M) (ha : Absorbing M) (hr : Accessible M)
    (μ : Measure Ω) [IsProbabilityMeasure μ] (history : Filtration ℕ mΩ)
    (X : ℕ → Ω → S) (L : FiniteDrift.Realization M μ history X)
    (s₀ : S) (hi : ∀ ω, X 0 ω = s₀) :
    FiniteDrift.expectedHitCount M μ X = ENNReal.ofReal (potential M s₀ : ℝ) :=
  expectedHitCount_fixed_eq_of_equations M _ hm ha
    (potential_equations M (det_ne_zero_of_accessible M hm hr)) μ history X L s₀ hi

end FinitePotential

#check @FinitePotential.runningEvent_succ
#check @FinitePotential.runningEvent_measurable_history
#check @FinitePotential.stoppedValue_initial
#check @FinitePotential.stoppedValue_shift
#check @FinitePotential.stoppedValue_nonnegative
#check @FinitePotential.stoppedValue_norm_le_sum
#check @FinitePotential.stoppedValue_measurable
#check @FinitePotential.stoppedValue_integrable
#check @FinitePotential.equations_real_bad
#check @FinitePotential.stoppedValue_conditional_exact
#check @FinitePotential.stoppedValue_integrated_exact
#check @FinitePotential.finite_horizon_exact
#check @FinitePotential.stoppedValue_zero_after_good
#check @FinitePotential.stoppedValue_ae_tendsto_zero
#check @FinitePotential.stoppedValue_integral_tendsto_zero
#check @FinitePotential.expectedHitCount_eq_of_equations
#check @FinitePotential.expectedHitCount_fixed_eq_of_equations
#check @FinitePotential.potential_expectedHitCount_eq
#check @FinitePotential.potential_expectedHitCount_fixed_eq
