module

public import NeighborGauge
public import NeighborProduct
public import NeighborTransfer
public import NeighborFlux
public import NeighborAsymptotics
public import TightnessResults

@[expose] public section

set_option autoImplicit false

namespace NeighborSeparation

open MTChainFormal
open scoped BigOperators

/-- The gauge, local witnesses, flux gradient and actual product budget are
    all derived here, rather than assumed as additional final hypotheses. -/
theorem initial_budget_lower {n : ℕ} (hn : 6 ≤ n) (c : ℝ) (h : EdgeCosts) (δ : ℝ)
    (hnonneg : ∀ s : ChainState n, 0 ≤ potential c h s)
    (hdrift : PointwiseDrift (n := n) c h δ) :
    δ * (((n - 4) ^ 2 / 4 : ℕ) : ℝ) / 78 ≤ initialBudget n c h := by
  have hremote (s : ChainState n) (hs : Remote s) : 0 ≤ rawScore c h s := by
    have ht := hnonneg s
    rw [potential_of_active c h s
      (PotentialSeparation.remote_active (by omega) s hs)] at ht
    exact ht
  obtain ⟨b, k, hb, hk, hagree⟩ := gauge_exists (by omega : 2 ≤ n) c h hremote
  have hbulk := bulkDrift_of_gauge hn c h b k δ hdrift hagree
  have hflux := flux_budget_bound hn k δ hk hbulk
  have hproduct := product_budget_bulk hn c h b k hnonneg hb hk hagree
  nlinarith

theorem budget_ratio_lower {n : ℕ} (hn : 6 ≤ n) (c : ℝ) (h : EdgeCosts)
    (δ : ℝ) (hδ : 0 < δ)
    (hnonneg : ∀ s : ChainState n, 0 ≤ potential c h s)
    (hdrift : PointwiseDrift (n := n) c h δ) :
    (((n - 4) ^ 2 / 4 : ℕ) : ℝ) / 78 ≤ initialBudget n c h / δ := by
  apply (le_div_iff₀ hδ).mpr
  have hbudget := initial_budget_lower hn c h δ hnonneg hdrift
  nlinarith

theorem budget_quadratic_lower {n : ℕ} (hn : 10 ≤ n) (c : ℝ) (h : EdgeCosts)
    (δ : ℝ) (hδ : 0 < δ)
    (hnonneg : ∀ s : ChainState n, 0 ≤ potential c h s)
    (hdrift : PointwiseDrift (n := n) c h δ) :
    (n : ℝ) ^ 2 / 1248 ≤ initialBudget n c h / δ :=
  (floor_budget_quadratic_lower hn).trans
    (budget_ratio_lower (by omega) c h δ hδ hnonneg hdrift)

/-- Packaging does not assert all-length existence or tightness of this class. -/
structure DriftCertificate (n : ℕ) where
  offset : ℝ
  edgeCosts : EdgeCosts
  delta : ℝ
  delta_positive : 0 < delta
  nonnegative : ∀ s : ChainState n, 0 ≤ potential offset edgeCosts s
  pointwise_drift : PointwiseDrift (n := n) offset edgeCosts delta

noncomputable def certificateBudget {n : ℕ} (C : DriftCertificate n) : ℝ :=
  initialBudget n C.offset C.edgeCosts / C.delta

theorem certificate_budget_lower {n : ℕ} (hn : 6 ≤ n) (C : DriftCertificate n) :
    (((n - 4) ^ 2 / 4 : ℕ) : ℝ) / 78 ≤ certificateBudget C :=
  budget_ratio_lower hn C.offset C.edgeCosts C.delta C.delta_positive
    C.nonnegative C.pointwise_drift

theorem family_budget_quadratic_lower (C : (n : ℕ) → DriftCertificate n) :
    ∀ᶠ n : ℕ in Filter.atTop, (n : ℝ) ^ 2 / 1248 ≤ certificateBudget (C n) := by
  filter_upwards [Filter.eventually_ge_atTop 10] with n hn
  exact budget_quadratic_lower hn (C n).offset (C n).edgeCosts (C n).delta
    (C n).delta_positive (C n).nonnegative (C n).pointwise_drift

theorem family_budget_isOmega_quadratic (C : (n : ℕ) → DriftCertificate n) :
    Asymptotics.IsBigO Filter.atTop (fun n : ℕ => (n : ℝ) ^ 2)
      (fun n : ℕ => certificateBudget (C n)) :=
  quadratic_lower_isBigO _ (family_budget_quadratic_lower C)

theorem family_budget_not_linear (C : (n : ℕ) → DriftCertificate n) :
    ¬ Asymptotics.IsBigO Filter.atTop (fun n : ℕ => certificateBudget (C n))
      (fun n : ℕ => (n : ℝ)) :=
  quadratic_lower_not_linear _ (family_budget_quadratic_lower C)

theorem process_bounds_and_budget_separation {n : ℕ} (hn : 6 ≤ n)
    (c : ℝ) (h : EdgeCosts) (δ : ℝ) (hδ : 0 < δ)
    (hnonneg : ∀ s : ChainState n, 0 ≤ potential c h s)
    (hdrift : PointwiseDrift (n := n) c h δ) :
    (ENNReal.ofReal ((n : ℝ) / 18) ≤ expectedSteps n ∧
      expectedSteps n ≤ ENNReal.ofReal (1054 * (n : ℝ))) ∧
      (((n - 4) ^ 2 / 4 : ℕ) : ℝ) / 78 ≤ initialBudget n c h / δ :=
  ⟨MTChainFormal.Tightness.linear_work_bounds (by omega),
    budget_ratio_lower hn c h δ hδ hnonneg hdrift⟩

theorem process_theta_and_certificate_omega (C : (n : ℕ) → DriftCertificate n) :
    Asymptotics.IsTheta Filter.atTop
      (fun n : ℕ => (expectedSteps n).toReal) (fun n : ℕ => (n : ℝ)) ∧
    Asymptotics.IsBigO Filter.atTop (fun n : ℕ => (n : ℝ) ^ 2)
      (fun n : ℕ => certificateBudget (C n)) ∧
    ¬ Asymptotics.IsBigO Filter.atTop (fun n : ℕ => certificateBudget (C n))
      (fun n : ℕ => (n : ℝ)) :=
  ⟨MTChainFormal.Tightness.expected_steps_isTheta_linear,
    family_budget_isOmega_quadratic C, family_budget_not_linear C⟩

end NeighborSeparation

#print axioms NeighborSeparation.initial_budget_lower
#print axioms NeighborSeparation.budget_ratio_lower
#print axioms NeighborSeparation.process_theta_and_certificate_omega
