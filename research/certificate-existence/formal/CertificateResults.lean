module

public import NeighborEmbedding
public import ExponentialObstruction

@[expose] public section

set_option autoImplicit false

namespace CertificateStudy

open MTChainFormal

/-- This conjunction includes an actual inhabitant: the class-wide obstruction
does not rely on an empty certificate class. Both bounds concern the same chain. -/
theorem nonvacuous_separable_separation {n : ℕ} (hn : 4 ≤ n) :
    Nonempty (PotentialSeparation.DriftCertificate n) ∧
    (∀ C : PotentialSeparation.DriftCertificate n,
      ((5 : ℝ)^((n - 4) / 2 + 1) - 3) / 36 ≤ PotentialSeparation.certificateBudget C) ∧
    (ENNReal.ofReal ((n : ℝ) / 18) ≤ expectedSteps n ∧
      expectedSteps n ≤ ENNReal.ofReal (1054 * (n : ℝ))) :=
  ⟨PotentialSeparation.Construction.certificate_exists (by omega),
    PotentialSeparation.Exponential.certificate_budget_floor_lower hn,
    MTChainFormal.Tightness.linear_work_bounds (by omega)⟩

/-- The larger one-bridge class is inhabited too. Only its existing quadratic
lower bound is asserted here; the narrower exponential obstruction is not used. -/
theorem nonvacuous_neighbor_separation {n : ℕ} (hn : 10 ≤ n) :
    Nonempty (NeighborSeparation.DriftCertificate n) ∧
    (∀ C : NeighborSeparation.DriftCertificate n,
      (n : ℝ)^2 / 1248 ≤ NeighborSeparation.certificateBudget C) ∧
    (ENNReal.ofReal ((n : ℝ) / 18) ≤ expectedSteps n ∧
      expectedSteps n ≤ ENNReal.ofReal (1054 * (n : ℝ))) := by
  refine ⟨NeighborSeparation.Embedding.certificate_exists (by omega), ?_,
    MTChainFormal.Tightness.linear_work_bounds (by omega)⟩
  intro C
  exact NeighborSeparation.budget_quadratic_lower hn C.offset C.edgeCosts C.delta
    C.delta_positive C.nonnegative C.pointwise_drift

end CertificateStudy

#print axioms CertificateStudy.nonvacuous_separable_separation
#print axioms CertificateStudy.nonvacuous_neighbor_separation
