/-
  Additive drift for a stopped random process.

  Sources:
  Johannes Lengler, Drift Analysis, Theorem 1 / book Theorem 2.3.1:
    https://arxiv.org/abs/1712.00964
  Chatterjee--Fu--Novotny, Foundations of Probabilistic Programming,
  Definition 7.4 and Proposition 7.5 (integrable ranking supermartingales):
    https://doi.org/10.1017/9781108770750

  Nonnegative potential and a local conditional expected decrease imply
  a bound on the expected number of active steps. Neither termination
  nor finite expected duration is a hypothesis. The finite-horizon proof
  telescopes before taking the countable supremum, so no optional-stopping
  hypothesis is hidden in the argument.

  This is the nonnegative, stopped-potential version of additive drift,
  not the full lower-bounded or lexicographic ranking theorem.
-/

module

public import Mathlib.MeasureTheory.Function.ConditionalExpectation.Basic
public import Mathlib.MeasureTheory.Integral.Bochner.Set
public import Mathlib.MeasureTheory.Integral.Lebesgue.Markov
public import Mathlib.Probability.Process.Filtration
public import Mathlib.Tactic

@[expose] public section

set_option linter.unusedSectionVars false

open MeasureTheory
open scoped ENNReal NNReal

namespace RepairDrift

variable {Ω : Type*} [mΩ : MeasurableSpace Ω]

/-- Count active steps, allowing an infinite duration. -/
noncomputable def activeCount (active : ℕ → Set Ω) (ω : Ω) : ℝ≥0∞ :=
  ∑' n : ℕ, (active n).indicator (fun _ => (1 : ℝ≥0∞)) ω

noncomputable def expectedActiveCount (μ : Measure Ω) (active : ℕ → Set Ω) : ℝ≥0∞ :=
  ∫⁻ ω, activeCount active ω ∂μ

theorem measurable_activeCount (active : ℕ → Set Ω)
    (hmeas : ∀ n, MeasurableSet (active n)) : Measurable (activeCount active) := by
  apply Measurable.tsum
  intro n
  exact measurable_const.indicator (hmeas n)

theorem expectedActiveCount_eq_tsum (μ : Measure Ω) (active : ℕ → Set Ω)
    (hmeas : ∀ n, MeasurableSet (active n)) :
    expectedActiveCount μ active = ∑' n, μ (active n) := by
  unfold expectedActiveCount activeCount
  rw [lintegral_tsum (fun n => (measurable_const.indicator (hmeas n)).aemeasurable)]
  apply tsum_congr
  intro n
  rw [lintegral_indicator_const (hmeas n) 1, one_mul]

/-- The remaining potential is retained in every finite-horizon bound. -/
theorem sum_cost_add_budget_le (cost budget : ℕ → ℝ≥0∞)
    (hstep : ∀ n, cost n + budget (n + 1) ≤ budget n) (N : ℕ) :
    (∑ n ∈ Finset.range N, cost n) + budget N ≤ budget 0 := by
  induction N with
  | zero => simp
  | succ N ih =>
    rw [Finset.sum_range_succ, add_assoc]
    exact (add_le_add le_rfl (hstep N)).trans ih

theorem tsum_cost_le_budget (cost budget : ℕ → ℝ≥0∞)
    (hstep : ∀ n, cost n + budget (n + 1) ≤ budget n) :
    (∑' n, cost n) ≤ budget 0 := by
  apply ENNReal.tsum_le_of_sum_range_le
  intro N
  exact (le_add_of_nonneg_right (show 0 ≤ budget N from zero_le)).trans
    (sum_cost_add_budget_le cost budget hstep N)

theorem expectedActiveCount_le_of_budget (μ : Measure Ω) (active : ℕ → Set Ω)
    (hmeas : ∀ n, MeasurableSet (active n)) (δ : ℝ≥0) (hδ : 0 < δ)
    (budget : ℕ → ℝ≥0∞)
    (hstep : ∀ n, (δ : ℝ≥0∞) * μ (active n) + budget (n + 1) ≤ budget n) :
    expectedActiveCount μ active ≤ budget 0 / (δ : ℝ≥0∞) := by
  have hδ0 : (δ : ℝ≥0∞) ≠ 0 := by exact_mod_cast hδ.ne'
  rw [ENNReal.le_div_iff_mul_le (Or.inl hδ0) (Or.inl ENNReal.coe_ne_top),
    expectedActiveCount_eq_tsum μ active hmeas, mul_comm, ← ENNReal.tsum_mul_left]
  exact tsum_cost_le_budget (fun n => (δ : ℝ≥0∞) * μ (active n)) budget hstep

/-- All premises describe local potential behavior, not eventual success. -/
structure ConditionalCertificate (μ : Measure Ω) (active : ℕ → Set Ω)
    (history : Filtration ℕ mΩ) (δ : ℝ≥0) where
  value : ℕ → Ω → ℝ
  integrable : ∀ n, Integrable (value n) μ
  nonnegative : ∀ n, 0 ≤ᵐ[μ] value n
  adapted : ∀ n, StronglyMeasurable[history n] (value n)
  active_measurable : ∀ n, MeasurableSet[history n] (active n)
  decrease : ∀ n, ∀ᵐ ω ∂μ,
    (μ[value (n + 1) | history n]) ω +
      (active n).indicator (fun _ => (δ : ℝ)) ω ≤ value n ω

namespace ConditionalCertificate

variable {μ : Measure Ω} [IsFiniteMeasure μ] {active : ℕ → Set Ω}
    {history : Filtration ℕ mΩ} {δ : ℝ≥0}

theorem measurable_active (C : ConditionalCertificate μ active history δ) (n : ℕ) :
    MeasurableSet (active n) := history.le n _ (C.active_measurable n)

/-- Integrate the local conditional inequality by the tower property. -/
theorem integrated_decrease (C : ConditionalCertificate μ active history δ) (n : ℕ) :
    (δ : ℝ≥0∞) * μ (active n) +
      ENNReal.ofReal (∫ ω, C.value (n + 1) ω ∂μ) ≤
      ENNReal.ofReal (∫ ω, C.value n ω ∂μ) := by
  have hi : Integrable ((active n).indicator (fun _ : Ω => (δ : ℝ))) μ :=
    (integrable_const _).indicator (C.measurable_active n)
  have hreal := integral_mono_ae
    (integrable_condExp.add hi) (C.integrable n) (C.decrease n)
  change (∫ ω, (μ[C.value (n + 1) | history n]) ω +
    (active n).indicator (fun _ => (δ : ℝ)) ω ∂μ) ≤ ∫ ω, C.value n ω ∂μ at hreal
  rw [integral_add integrable_condExp hi, integral_condExp (history.le n),
    integral_indicator_const _ (C.measurable_active n), smul_eq_mul] at hreal
  have hnext : 0 ≤ ∫ ω, C.value (n + 1) ω ∂μ := integral_nonneg_of_ae (C.nonnegative _)
  have hterm : 0 ≤ μ.real (active n) * (δ : ℝ) := mul_nonneg (by positivity) δ.coe_nonneg
  have henn := ENNReal.ofReal_le_ofReal hreal
  rw [ENNReal.ofReal_add hnext hterm, ENNReal.ofReal_mul (by positivity)] at henn
  have hmeasure : ENNReal.ofReal (μ.real (active n)) = μ (active n) := by
    exact ENNReal.ofReal_toReal (measure_ne_top μ _)
  rw [hmeasure, ENNReal.ofReal_coe_nnreal] at henn
  simpa only [add_comm, mul_comm] using henn

theorem expectedActiveCount_le (C : ConditionalCertificate μ active history δ)
    (hδ : 0 < δ) :
    expectedActiveCount μ active ≤
      ENNReal.ofReal (∫ ω, C.value 0 ω ∂μ) / (δ : ℝ≥0∞) := by
  exact expectedActiveCount_le_of_budget μ active C.measurable_active δ hδ
    (fun n => ENNReal.ofReal (∫ ω, C.value n ω ∂μ)) C.integrated_decrease

theorem expectedActiveCount_lt_top (C : ConditionalCertificate μ active history δ)
    (hδ : 0 < δ) : expectedActiveCount μ active < ⊤ := by
  have hδ0 : (δ : ℝ≥0∞) ≠ 0 := by exact_mod_cast hδ.ne'
  exact lt_of_le_of_lt (C.expectedActiveCount_le hδ)
    (ENNReal.div_lt_top ENNReal.ofReal_ne_top hδ0)

theorem ae_activeCount_lt_top (C : ConditionalCertificate μ active history δ)
    (hδ : 0 < δ) : ∀ᵐ ω ∂μ, activeCount active ω < ⊤ := by
  exact MeasureTheory.ae_lt_top (measurable_activeCount active C.measurable_active)
    (C.expectedActiveCount_lt_top hδ).ne

end ConditionalCertificate
end RepairDrift

#check @RepairDrift.measurable_activeCount
#check @RepairDrift.expectedActiveCount_eq_tsum
#check @RepairDrift.sum_cost_add_budget_le
#check @RepairDrift.tsum_cost_le_budget
#check @RepairDrift.expectedActiveCount_le_of_budget
#check @RepairDrift.ConditionalCertificate.measurable_active
#check @RepairDrift.ConditionalCertificate.integrated_decrease
#check @RepairDrift.ConditionalCertificate.expectedActiveCount_le
#check @RepairDrift.ConditionalCertificate.expectedActiveCount_lt_top
#check @RepairDrift.ConditionalCertificate.ae_activeCount_lt_top
