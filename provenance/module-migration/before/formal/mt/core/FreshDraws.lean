import Mathlib.Data.Fintype.BigOperators
import Mathlib.Tactic

set_option autoImplicit false

namespace MTChainProof

open scoped BigOperators

/-- This models the measured finite pass table, not arbitrary Lean tactics. -/
def bridgePass (a b : Fin 3) (tactic : Fin 4) : Bool :=
  if tactic = 1 then decide (a = b) else decide (b ≤ a)

theorem measured_profile_table : ∀ a b : Fin 3,
    (Finset.univ.filter (fun r : Fin 4 => bridgePass a b r)).card =
      if a = b then 4 else if b < a then 3 else 0 := by
  decide

theorem interior_success_count :
    (Finset.univ.filter (fun u : Fin 3 × Fin 3 × Fin 4 =>
      bridgePass u.1 u.2.1 u.2.2)).card = 21 := by
  decide

theorem first_success_count :
    (Finset.univ.filter (fun u : Fin 3 × Fin 4 =>
      bridgePass 2 u.1 u.2)).card = 10 := by
  decide

theorem last_success_count :
    (Finset.univ.filter (fun u : Fin 3 × Fin 4 =>
      bridgePass u.1 0 u.2)).card = 10 := by
  decide

def interiorSuccess : ℚ :=
  ∑ u : Fin 3 × Fin 3 × Fin 4,
    if bridgePass u.1 u.2.1 u.2.2 then 1 / 36 else 0

def firstSuccess : ℚ :=
  ∑ u : Fin 3 × Fin 4, if bridgePass 2 u.1 u.2 then 1 / 12 else 0

def lastSuccess : ℚ :=
  ∑ u : Fin 3 × Fin 4, if bridgePass u.1 0 u.2 then 1 / 12 else 0

theorem interior_success_probability : interiorSuccess = 7 / 12 := by
  norm_num [interiorSuccess, Fintype.sum_prod_type, Fin.sum_univ_succ, bridgePass]

theorem first_success_probability : firstSuccess = 5 / 6 := by
  norm_num [firstSuccess, Fintype.sum_prod_type, Fin.sum_univ_succ, bridgePass]

theorem last_success_probability : lastSuccess = 5 / 6 := by
  norm_num [lastSuccess, Fintype.sum_prod_type, Fin.sum_univ_succ, bridgePass]

theorem uniform_success_lower_bound :
    (7 / 12 : ℚ) ≤ interiorSuccess ∧
    (7 / 12 : ℚ) ≤ firstSuccess ∧
    (7 / 12 : ℚ) ≤ lastSuccess := by
  rw [interior_success_probability, first_success_probability,
    last_success_probability]
  norm_num

/-- The left-neighbour loss law is conditioned on its present threshold and
    profile; it does not assume the retained prefix was sampled afresh. -/
def leftLoss (u : Fin 3) (weak : Bool) : ℚ :=
  ∑ fresh : Fin 3,
    if (if weak then decide (fresh ≠ u) else decide (u < fresh))
      then 1 / 3 else 0

def rightLoss (u : Fin 3) (weak : Bool) : ℚ :=
  ∑ fresh : Fin 3,
    if (if weak then decide (fresh ≠ u) else decide (fresh < u))
      then 1 / 3 else 0

theorem strong_left_loss : ∀ u : Fin 3,
    leftLoss u false = ((2 : ℚ) - u.val) / 3 := by
  intro u
  fin_cases u <;> norm_num [leftLoss, Fin.sum_univ_succ]

theorem weak_left_loss : ∀ u : Fin 3, leftLoss u true = 2 / 3 := by
  intro u
  fin_cases u <;> norm_num [leftLoss, Fin.sum_univ_succ]

theorem strong_right_loss : ∀ u : Fin 3,
    rightLoss u false = (u.val : ℚ) / 3 := by
  intro u
  fin_cases u <;> norm_num [rightLoss, Fin.sum_univ_succ]

theorem weak_right_loss : ∀ u : Fin 3, rightLoss u true = 2 / 3 := by
  intro u
  fin_cases u <;> norm_num [rightLoss, Fin.sum_univ_succ]

def differentPair (t a b : Fin 3) : ℚ :=
  (if a = t then 0 else 1) + (if b = t then 0 else 1)

def freshDifferentPair (t : Fin 3) : ℚ :=
  ∑ u : Fin 3 × Fin 3, (1 / 9) * differentPair t u.1 u.2

theorem failed_pair_has_one_different : ∀ t b : Fin 3, ∀ r : Fin 4,
    bridgePass t b r = false → differentPair t t b = 1 := by
  intro t b r hf
  have hne : b ≠ t := by
    intro heq
    subst b
    simp [bridgePass] at hf
  simp [differentPair, hne]

theorem fresh_pair_difference_mean : ∀ t : Fin 3,
    freshDifferentPair t = 4 / 3 := by
  intro t
  fin_cases t <;>
    norm_num [freshDifferentPair, differentPair, Fintype.sum_prod_type,
      Fin.sum_univ_succ]

/-- This is the positive drift used inside a fixed-incoming-mode episode.
    It concerns the two mutable coordinates of an interior operation. -/
theorem fixed_mode_pair_drift (t b : Fin 3) (r : Fin 4)
    (hf : bridgePass t b r = false) :
    freshDifferentPair t - differentPair t t b = 1 / 3 := by
  rw [fresh_pair_difference_mean, failed_pair_has_one_different t b r hf]
  norm_num

def freshDifferentSingle (t : Fin 3) : ℚ :=
  ∑ a : Fin 3, (1 / 3) * (if a = t then 0 else 1)

theorem fresh_single_difference_mean : ∀ t : Fin 3,
    freshDifferentSingle t = 2 / 3 := by
  intro t
  fin_cases t <;> norm_num [freshDifferentSingle, Fin.sum_univ_succ]

def interiorBarrierChance : ℚ :=
  ∑ u : Fin 3 × Fin 3 × Fin 4,
    if u.1 = 2 ∧ u.2.2 ≠ 1 then 1 / 36 else 0

theorem interior_barrier_creation_probability : interiorBarrierChance = 1 / 4 := by
  norm_num [interiorBarrierChance, Fintype.sum_prod_type, Fin.sum_univ_succ]

end MTChainProof

#print axioms MTChainProof.measured_profile_table
#print axioms MTChainProof.interior_success_probability
#print axioms MTChainProof.first_success_probability
#print axioms MTChainProof.last_success_probability
#print axioms MTChainProof.uniform_success_lower_bound
#print axioms MTChainProof.strong_left_loss
#print axioms MTChainProof.strong_right_loss
#print axioms MTChainProof.fixed_mode_pair_drift
#print axioms MTChainProof.interior_barrier_creation_probability
