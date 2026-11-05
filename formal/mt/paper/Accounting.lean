module

public import Mathlib.Data.Fintype.BigOperators
public import Mathlib.Tactic

@[expose] public section

set_option autoImplicit false

namespace MTChainProof

open scoped BigOperators

variable {C : Type*} [Fintype C]

/-- A certificate is counted once per actual passing-to-failing transition. -/
def invalidation (before after : C → Bool) (j : C) : ℚ :=
  if before j && !after j then 1 else 0

/-- Repairs include changes of unselected neighbouring certificates. -/
def repair (before after : C → Bool) (j : C) : ℚ :=
  if !before j && after j then 1 else 0

def failures (holds : C → Bool) : ℚ :=
  ∑ j, if holds j then 0 else 1

def invalidations (before after : C → Bool) : ℚ :=
  ∑ j, invalidation before after j

def repairs (before after : C → Bool) : ℚ :=
  ∑ j, repair before after j

omit [Fintype C] in
theorem repair_nonneg (before after : C → Bool) (j : C) :
    0 ≤ repair before after j := by
  unfold repair
  split <;> norm_num

theorem failures_nonneg (holds : C → Bool) : 0 ≤ failures holds := by
  apply Finset.sum_nonneg
  intro j _
  split <;> norm_num

theorem repairs_nonneg (before after : C → Bool) :
    0 ≤ repairs before after := by
  exact Finset.sum_nonneg (fun j _ => repair_nonneg before after j)

/-- Exact balance for every simultaneous change of a finite certificate family. -/
theorem status_balance (before after : C → Bool) :
    failures after + repairs before after =
      failures before + invalidations before after := by
  unfold failures repairs invalidations
  rw [← Finset.sum_add_distrib, ← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro j _
  cases hb : before j <;> cases ha : after j <;>
    simp [repair, invalidation, hb, ha]

theorem selected_success_le_repairs (before after : C → Bool)
    (selected : C) (hfailed : before selected = false) :
    (if after selected then (1 : ℚ) else 0) ≤ repairs before after := by
  have hsingle : repair before after selected ≤ repairs before after := by
    exact Finset.single_le_sum (fun j _ => repair_nonneg before after j)
      (Finset.mem_univ selected)
  simpa [repair, hfailed] using hsingle

/-- One update can repair additional neighbours; selected successes only bound
    the total from below. This inequality never assumes selected = all repairs. -/
theorem selected_success_budget (before after : C → Bool)
    (selected : C) (hfailed : before selected = false) :
    (if after selected then (1 : ℚ) else 0) ≤
      failures before + invalidations before after - failures after := by
  have h := selected_success_le_repairs before after selected hfailed
  have hb := status_balance before after
  linarith

/-- A finite fresh-outcome law turns the exact balance into a one-step drift
    bound. The success assumption is checked separately against the catalog. -/
theorem expected_failure_drift
    {U : Type*} [Fintype U]
    (before : C → Bool) (after : U → C → Bool)
    (selected : C) (hfailed : before selected = false)
    (weight : U → ℚ) (hweight : ∀ u, 0 ≤ weight u)
    (hnormalized : ∑ u, weight u = 1)
    (c : ℚ)
    (hsuccess : c ≤ ∑ u, weight u * (if after u selected then 1 else 0)) :
    (∑ u, weight u * failures (after u)) + c ≤
      failures before + ∑ u, weight u * invalidations before (after u) := by
  have hpoint : ∀ u,
      weight u * failures (after u) +
          weight u * (if after u selected then 1 else 0) ≤
        weight u * failures before +
          weight u * invalidations before (after u) := by
    intro u
    have hb := selected_success_budget before (after u) selected hfailed
    have hm := mul_le_mul_of_nonneg_left hb (hweight u)
    nlinarith
  have hsum := Finset.sum_le_sum (fun u (_ : u ∈ Finset.univ) => hpoint u)
  simp only [Finset.sum_add_distrib] at hsum
  rw [← Finset.sum_mul, hnormalized, one_mul] at hsum
  linarith

/-- No selected bridge means no selected success. Other repairs are still
    counted by the exact status balance. -/
def selectedRepair (holds : ℕ → C → Bool) (selected : ℕ → Option C)
    (t : ℕ) : ℚ :=
  match selected t with
  | none => 0
  | some j => if holds (t + 1) j then 1 else 0

theorem path_selected_budget (holds : ℕ → C → Bool)
    (selected : ℕ → Option C)
    (hfailed : ∀ t j, selected t = some j → holds t j = false)
    (t : ℕ) :
    selectedRepair holds selected t + failures (holds (t + 1)) ≤
      failures (holds t) + invalidations (holds t) (holds (t + 1)) := by
  cases hj : selected t with
  | none =>
    have hp := repairs_nonneg (holds t) (holds (t + 1))
    have hb := status_balance (holds t) (holds (t + 1))
    simp only [selectedRepair, hj]
    linarith
  | some j =>
    have hp := selected_success_budget (holds t) (holds (t + 1)) j
      (hfailed t j hj)
    simp only [selectedRepair, hj]
    linarith

/-- The finite-horizon pathwise inequality does not assume termination. -/
theorem finite_horizon_accounting (holds : ℕ → C → Bool)
    (selected : ℕ → Option C)
    (hfailed : ∀ t j, selected t = some j → holds t j = false)
    (m : ℕ) :
    (∑ t ∈ Finset.range m, selectedRepair holds selected t) +
        failures (holds m) ≤
      failures (holds 0) +
        ∑ t ∈ Finset.range m, invalidations (holds t) (holds (t + 1)) := by
  induction m with
  | zero => simp
  | succ m ih =>
    have hp := path_selected_budget holds selected hfailed m
    simp only [Finset.sum_range_succ]
    linarith

theorem finite_horizon_selected_le_budget (holds : ℕ → C → Bool)
    (selected : ℕ → Option C)
    (hfailed : ∀ t j, selected t = some j → holds t j = false)
    (m : ℕ) :
    (∑ t ∈ Finset.range m, selectedRepair holds selected t) ≤
      failures (holds 0) +
        ∑ t ∈ Finset.range m, invalidations (holds t) (holds (t + 1)) := by
  have hb := finite_horizon_accounting holds selected hfailed m
  have hn := failures_nonneg (holds m)
  linarith

def activeStep (selected : ℕ → Option C) (t : ℕ) : ℚ :=
  if (selected t).isSome then 1 else 0

omit [Fintype C] in
theorem weighted_time_sum {Ω : Type*} [Fintype Ω]
    (weight : Ω → ℚ) (f : Ω → ℕ → ℚ) (m : ℕ) :
    (∑ ω, weight ω * ∑ t ∈ Finset.range m, f ω t) =
      ∑ t ∈ Finset.range m, ∑ ω, weight ω * f ω t := by
  simp_rw [Finset.mul_sum]
  rw [Finset.sum_comm]

/-- Finite laws suffice for the finite-horizon averaging step. The per-step
    success premise is an expectation inequality, not an IID-attempt claim.
    A stochastic-process instantiation must still establish this premise. -/
theorem finite_law_work_budget {Ω : Type*} [Fintype Ω]
    (weight : Ω → ℚ) (hweight : ∀ ω, 0 ≤ weight ω)
    (holds : Ω → ℕ → C → Bool) (selected : Ω → ℕ → Option C)
    (hfailed : ∀ ω t j, selected ω t = some j → holds ω t j = false)
    (c : ℚ) (m : ℕ)
    (hsuccess : ∀ t < m,
      c * (∑ ω, weight ω * activeStep (selected ω) t) ≤
        ∑ ω, weight ω * selectedRepair (holds ω) (selected ω) t) :
    c * (∑ ω, weight ω * ∑ t ∈ Finset.range m,
        activeStep (selected ω) t) ≤
      ∑ ω, weight ω * (failures (holds ω 0) +
        ∑ t ∈ Finset.range m,
          invalidations (holds ω t) (holds ω (t + 1))) := by
  calc
    c * (∑ ω, weight ω * ∑ t ∈ Finset.range m,
          activeStep (selected ω) t) =
        ∑ t ∈ Finset.range m, c *
          (∑ ω, weight ω * activeStep (selected ω) t) := by
      rw [weighted_time_sum, Finset.mul_sum]
    _ ≤ ∑ t ∈ Finset.range m,
        ∑ ω, weight ω * selectedRepair (holds ω) (selected ω) t := by
      exact Finset.sum_le_sum (fun t ht => hsuccess t (Finset.mem_range.mp ht))
    _ = ∑ ω, weight ω * ∑ t ∈ Finset.range m,
        selectedRepair (holds ω) (selected ω) t := by
      exact (weighted_time_sum weight
        (fun ω t => selectedRepair (holds ω) (selected ω) t) m).symm
    _ ≤ ∑ ω, weight ω * (failures (holds ω 0) +
        ∑ t ∈ Finset.range m,
          invalidations (holds ω t) (holds ω (t + 1))) := by
      apply Finset.sum_le_sum
      intro ω _
      exact mul_le_mul_of_nonneg_left
        (finite_horizon_selected_le_budget (holds ω) (selected ω) (hfailed ω) m)
        (hweight ω)

omit [Fintype C] in
theorem sum_time_differences (z : ℕ → ℚ) (m : ℕ) :
    (∑ t ∈ Finset.range m, (z (t + 1) - z t)) = z m - z 0 := by
  induction m with
  | zero => simp
  | succ m ih =>
    rw [Finset.sum_range_succ, ih]
    ring

omit [Fintype C] in
/-- Finite-horizon form of the bounded positive-drift episode argument.
    The potential is bounded above, and drift is accumulated only while the
    episode is active. No independence of distinct times is assumed. -/
theorem finite_law_bounded_positive_drift {Ω : Type*} [Fintype Ω]
    (weight : Ω → ℚ) (hweight : ∀ ω, 0 ≤ weight ω)
    (hnormalized : ∑ ω, weight ω = 1)
    (potential active : Ω → ℕ → ℚ) (c bound : ℚ) (m : ℕ)
    (hbound : ∀ ω, potential ω m ≤ bound)
    (hstep : ∀ t < m,
      c * (∑ ω, weight ω * active ω t) ≤
        ∑ ω, weight ω * (potential ω (t + 1) - potential ω t)) :
    c * (∑ ω, weight ω * ∑ t ∈ Finset.range m, active ω t) ≤
      bound - ∑ ω, weight ω * potential ω 0 := by
  have hz : (∑ ω, weight ω * potential ω m) ≤ bound := by
    calc
      (∑ ω, weight ω * potential ω m) ≤ ∑ ω, weight ω * bound := by
        exact Finset.sum_le_sum
          (fun ω _ => mul_le_mul_of_nonneg_left (hbound ω) (hweight ω))
      _ = bound := by rw [← Finset.sum_mul, hnormalized, one_mul]
  calc
    c * (∑ ω, weight ω * ∑ t ∈ Finset.range m, active ω t) =
        ∑ t ∈ Finset.range m, c * (∑ ω, weight ω * active ω t) := by
      rw [weighted_time_sum, Finset.mul_sum]
    _ ≤ ∑ t ∈ Finset.range m,
        ∑ ω, weight ω * (potential ω (t + 1) - potential ω t) := by
      exact Finset.sum_le_sum (fun t ht => hstep t (Finset.mem_range.mp ht))
    _ = ∑ ω, weight ω * (potential ω m - potential ω 0) := by
      rw [← weighted_time_sum]
      simp_rw [sum_time_differences]
    _ = (∑ ω, weight ω * potential ω m) -
        ∑ ω, weight ω * potential ω 0 := by
      simp only [mul_sub, Finset.sum_sub_distrib]
    _ ≤ bound - ∑ ω, weight ω * potential ω 0 := by linarith

end MTChainProof

#print axioms MTChainProof.status_balance
#print axioms MTChainProof.expected_failure_drift
#print axioms MTChainProof.finite_horizon_accounting
#print axioms MTChainProof.finite_law_work_budget
#print axioms MTChainProof.finite_law_bounded_positive_drift
