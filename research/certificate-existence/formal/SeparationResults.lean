module

public import SeparableWitness
public import SeparableProduct
public import SeparableSequence
public import TightnessResults

@[expose] public section

set_option autoImplicit false

namespace PotentialSeparation

open MTChainFormal
open scoped BigOperators

/-- All helper obligations are discharged from the actual raw-state drift
    and nonnegativity assumptions. No score restriction is imposed at Good. -/
theorem initial_budget_lower {n : ℕ} (hn : 4 ≤ n)
    (c : ℝ) (f : ThresholdCosts) (g : TacticCosts) (δ : ℝ)
    (hnonneg : ∀ s : ChainState n, 0 ≤ potential c f g s)
    (hdrift : PointwiseDrift (n := n) c f g δ) :
    δ * (((n - 2) ^ 2 / 4 : ℕ) : ℝ) / 12 ≤ initialBudget n c f g := by
  have hgradient := contrast_gradient hn c f g δ hdrift
  have hsequence := gradient_oscillation_lower f δ hgradient
  have hproduct := initial_budget_oscillation hn c f g hnonneg
  nlinarith

theorem budget_ratio_lower {n : ℕ} (hn : 4 ≤ n)
    (c : ℝ) (f : ThresholdCosts) (g : TacticCosts) (δ : ℝ) (hδ : 0 < δ)
    (hnonneg : ∀ s : ChainState n, 0 ≤ potential c f g s)
    (hdrift : PointwiseDrift (n := n) c f g δ) :
    (((n - 2) ^ 2 / 4 : ℕ) : ℝ) / 12 ≤ initialBudget n c f g / δ := by
  apply (le_div_iff₀ hδ).mpr
  have h := initial_budget_lower hn c f g δ hnonneg hdrift
  nlinarith

theorem budget_quadratic_lower {n : ℕ} (hn : 8 ≤ n)
    (c : ℝ) (f : ThresholdCosts) (g : TacticCosts) (δ : ℝ) (hδ : 0 < δ)
    (hnonneg : ∀ s : ChainState n, 0 ≤ potential c f g s)
    (hdrift : PointwiseDrift (n := n) c f g δ) :
    (n : ℝ) ^ 2 / 384 ≤ initialBudget n c f g / δ :=
  le_trans (floor_budget_quadratic_lower hn)
    (budget_ratio_lower (by omega) c f g δ hδ hnonneg hdrift)

/-- Packaging the intended assumptions does not assert that this class is
    inhabited for every n, or that its lower bound is attained. -/
structure DriftCertificate (n : ℕ) where
  offset : ℝ
  thresholdCosts : ThresholdCosts
  tacticCosts : TacticCosts
  delta : ℝ
  delta_positive : 0 < delta
  nonnegative : ∀ s : ChainState n, 0 ≤ potential offset thresholdCosts tacticCosts s
  pointwise_drift : PointwiseDrift (n := n) offset thresholdCosts tacticCosts delta

noncomputable def certificateBudget {n : ℕ} (C : DriftCertificate n) : ℝ :=
  initialBudget n C.offset C.thresholdCosts C.tacticCosts / C.delta

theorem certificate_budget_lower {n : ℕ} (hn : 4 ≤ n) (C : DriftCertificate n) :
    (((n - 2) ^ 2 / 4 : ℕ) : ℝ) / 12 ≤ certificateBudget C :=
  budget_ratio_lower hn C.offset C.thresholdCosts C.tacticCosts C.delta
    C.delta_positive C.nonnegative C.pointwise_drift

theorem family_budget_quadratic_lower (C : (n : ℕ) → DriftCertificate n) :
    ∀ᶠ n : ℕ in Filter.atTop, (n : ℝ) ^ 2 / 384 ≤ certificateBudget (C n) := by
  filter_upwards [Filter.eventually_ge_atTop 8] with n hn
  exact budget_quadratic_lower hn (C n).offset (C n).thresholdCosts
    (C n).tacticCosts (C n).delta (C n).delta_positive
    (C n).nonnegative (C n).pointwise_drift

theorem family_budget_isOmega_quadratic (C : (n : ℕ) → DriftCertificate n) :
    Asymptotics.IsBigO Filter.atTop (fun n : ℕ => (n : ℝ) ^ 2)
      (fun n : ℕ => certificateBudget (C n)) :=
  quadratic_lower_isBigO _ (family_budget_quadratic_lower C)

theorem family_budget_not_linear (C : (n : ℕ) → DriftCertificate n) :
    ¬ Asymptotics.IsBigO Filter.atTop (fun n : ℕ => certificateBudget (C n))
      (fun n : ℕ => (n : ℝ)) :=
  quadratic_lower_not_linear _ (family_budget_quadratic_lower C)

/-- The process bound and the restricted certificate bound concern the same
    original initialized process, with different mathematical quantities. -/
theorem process_bounds_and_budget_separation {n : ℕ} (hn : 4 ≤ n)
    (c : ℝ) (f : ThresholdCosts) (g : TacticCosts) (δ : ℝ) (hδ : 0 < δ)
    (hnonneg : ∀ s : ChainState n, 0 ≤ potential c f g s)
    (hdrift : PointwiseDrift (n := n) c f g δ) :
    (ENNReal.ofReal ((n : ℝ) / 18) ≤ expectedSteps n ∧
      expectedSteps n ≤ ENNReal.ofReal (1054 * (n : ℝ))) ∧
      (((n - 2) ^ 2 / 4 : ℕ) : ℝ) / 12 ≤ initialBudget n c f g / δ :=
  ⟨MTChainFormal.Tightness.linear_work_bounds (by omega),
    budget_ratio_lower hn c f g δ hδ hnonneg hdrift⟩

theorem process_theta_and_certificate_omega (C : (n : ℕ) → DriftCertificate n) :
    Asymptotics.IsTheta Filter.atTop
      (fun n : ℕ => (expectedSteps n).toReal) (fun n : ℕ => (n : ℝ)) ∧
    Asymptotics.IsBigO Filter.atTop (fun n : ℕ => (n : ℝ) ^ 2)
      (fun n : ℕ => certificateBudget (C n)) ∧
    ¬ Asymptotics.IsBigO Filter.atTop (fun n : ℕ => certificateBudget (C n))
      (fun n : ℕ => (n : ℝ)) :=
  ⟨MTChainFormal.Tightness.expected_steps_isTheta_linear,
    family_budget_isOmega_quadratic C, family_budget_not_linear C⟩

end PotentialSeparation

#print axioms PotentialSeparation.initial_budget_lower
#print axioms PotentialSeparation.budget_ratio_lower
#print axioms PotentialSeparation.family_budget_not_linear
#print axioms PotentialSeparation.process_bounds_and_budget_separation
#print axioms PotentialSeparation.process_theta_and_certificate_omega
