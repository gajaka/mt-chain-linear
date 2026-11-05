module

public import NeighborResults
public import CertificateConstruction

@[expose] public section

set_option autoImplicit false

/-! The one-bridge score class contains the stopped separable-score class.
This transfers a concrete certificate, not merely a conditional lower bound. -/

namespace NeighborSeparation.Embedding

open MTChainFormal
open scoped BigOperators

def edgeCosts (f : PotentialSeparation.ThresholdCosts)
    (g : PotentialSeparation.TacticCosts) : EdgeCosts :=
  fun i a _b r => (if i = 0 then 0 else f i a) + g i r

theorem rawScore_eq {n : ℕ} (c : ℝ)
    (f : PotentialSeparation.ThresholdCosts) (g : PotentialSeparation.TacticCosts)
    (s : ChainState n) :
    rawScore c (edgeCosts f g) s = PotentialSeparation.rawScore c f g s := by
  have hsum : (∑ i : Fin n, if i.val = 0 then 0 else f i.val (value s i.val)) =
      ∑ j : Fin (n - 1), f (j.val + 1) (s.values j) := by
    cases n with
    | zero => simp
    | succ m =>
      rw [Fin.sum_univ_succ]
      simp [value_internal]
  simp only [rawScore, edgeCosts, Finset.sum_add_distrib, hsum,
    PotentialSeparation.rawScore]
  ring

theorem potential_eq {n : ℕ} (c : ℝ)
    (f : PotentialSeparation.ThresholdCosts) (g : PotentialSeparation.TacticCosts)
    (s : ChainState n) :
    potential c (edgeCosts f g) s = PotentialSeparation.potential c f g s := by
  simp only [potential, PotentialSeparation.potential, rawScore_eq]

noncomputable def certificate {n : ℕ} (C : PotentialSeparation.DriftCertificate n) :
    DriftCertificate n where
  offset := C.offset
  edgeCosts := edgeCosts C.thresholdCosts C.tacticCosts
  delta := C.delta
  delta_positive := C.delta_positive
  nonnegative := by
    intro s
    rw [potential_eq]
    exact C.nonnegative s
  pointwise_drift := by
    intro s i hi
    simp_rw [potential_eq]
    exact C.pointwise_drift s i hi

theorem certificate_budget_eq {n : ℕ} (C : PotentialSeparation.DriftCertificate n) :
    certificateBudget (certificate C) = PotentialSeparation.certificateBudget C := by
  simp only [certificateBudget, PotentialSeparation.certificateBudget, certificate,
    initialBudget, PotentialSeparation.initialBudget, potential_eq]

theorem certificate_exists {n : ℕ} (hn : 2 ≤ n) : Nonempty (DriftCertificate n) :=
  ⟨certificate (PotentialSeparation.Construction.certificate n hn)⟩

end NeighborSeparation.Embedding

#print axioms NeighborSeparation.Embedding.certificate_exists
