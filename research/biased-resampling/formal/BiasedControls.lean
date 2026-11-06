module

public import BiasedDrift

@[expose] public section

set_option autoImplicit false

namespace MTChainFormal.BiasedResampling.Controls

open scoped BigOperators

/-- A strong ascending interior bridge; all earlier bridges pass. -/
def interiorWitness : ChainState 3 where
  values j := if j = 0 then 1 else 2
  tactic _ := 0

def interiorTarget : Fin 3 := 1

theorem interior_failed : passes interiorWitness interiorTarget = false := by
  decide

theorem interior_firstFailure :
    firstFailure interiorWitness = some interiorTarget := by
  apply firstFailure_of_failed_prefix interiorWitness interiorTarget interior_failed
  intro i hi
  have hi0 : i = 0 := by
    apply Fin.ext
    change i.val = 0
    have hi' : i.val < 1 := hi
    omega
  subst i
  decide

theorem interior_potential : potential interiorWitness = 6 := by
  norm_num [potential, interiorWitness, thresholdCost, tacticCost, Fin.sum_univ_succ]

private theorem interior_replaced_potential (u : Draw) :
    potential (replace interiorWitness interiorTarget u) =
      thresholdCost u.1 + thresholdCost u.2.1 + tacticCost u.2.2 := by
  simp [potential, replace, interiorWitness, interiorTarget, tacticCost,
    Fin.sum_univ_succ]

private theorem interior_average (p : ℝ) :
    average p (fun u => potential (replace interiorWitness interiorTarget u)) =
      12 * (1 - p) + 1 := by
  simp_rw [interior_replaced_potential]
  rw [average_add, average_add, average_incoming_thresholdCost,
    average_outgoing_thresholdCost, average_tacticCost]
  ring

theorem interior_uniform_average :
    average (1 / 3) (fun u => potential (replace interiorWitness interiorTarget u)) = 9 := by
  rw [interior_average]
  norm_num

theorem interior_biased_average :
    average (2 / 3) (fun u => potential (replace interiorWitness interiorTarget u)) = 5 := by
  rw [interior_average]
  norm_num

/-- The old uniform redraw law does not admit this new unit-drift score. -/
theorem uniform_unit_drift_fails :
    ¬ (1 + average (1 / 3)
      (fun u => potential (replace interiorWitness interiorTarget u)) ≤
        potential interiorWitness) := by
  rw [interior_uniform_average, interior_potential]
  norm_num

theorem biased_unit_drift_tight :
    1 + average (2 / 3)
      (fun u => potential (replace interiorWitness interiorTarget u)) =
        potential interiorWitness := by
  rw [interior_biased_average, interior_potential]
  norm_num

/-- The final weak bridge fails although every internal threshold is maximal. -/
def endpointWitness : ChainState 2 where
  values _ := 2
  tactic i := if i = 1 then 1 else 0

def endpointTarget : Fin 2 := 1

theorem endpoint_failed : passes endpointWitness endpointTarget = false := by
  decide

theorem endpoint_firstFailure :
    firstFailure endpointWitness = some endpointTarget := by
  apply firstFailure_of_failed_prefix endpointWitness endpointTarget endpoint_failed
  intro i hi
  have hi0 : i = 0 := by
    apply Fin.ext
    change i.val = 0
    have hi' : i.val < 1 := hi
    omega
  subst i
  decide

theorem endpoint_potential : potential endpointWitness = 4 := by
  norm_num [potential, endpointWitness, thresholdCost, tacticCost, Fin.sum_univ_succ]

private theorem endpoint_replaced_potential (u : Draw) :
    potential (replace endpointWitness endpointTarget u) =
      thresholdCost u.1 + tacticCost u.2.2 := by
  simp [potential, replace, endpointWitness, endpointTarget, tacticCost,
    Fin.sum_univ_succ]

theorem endpoint_biased_average :
    average (2 / 3) (fun u => potential (replace endpointWitness endpointTarget u)) = 3 := by
  simp_rw [endpoint_replaced_potential]
  rw [average_add, average_incoming_thresholdCost, average_tacticCost]
  norm_num

theorem endpoint_unit_drift_tight :
    1 + average (2 / 3)
      (fun u => potential (replace endpointWitness endpointTarget u)) =
        potential endpointWitness := by
  rw [endpoint_biased_average, endpoint_potential]
  norm_num

noncomputable def thresholdScore {n : ℕ} (s : ChainState n) : ℝ :=
  ∑ j, thresholdCost (s.values j)

theorem endpoint_thresholdScore : thresholdScore endpointWitness = 0 := by
  norm_num [thresholdScore, endpointWitness, thresholdCost, Fin.sum_univ_succ]

private theorem endpoint_replaced_thresholdScore (u : Draw) :
    thresholdScore (replace endpointWitness endpointTarget u) = thresholdCost u.1 := by
  simp [thresholdScore, replace, endpointWitness, endpointTarget]

theorem endpoint_threshold_average :
    average (2 / 3)
      (fun u => thresholdScore (replace endpointWitness endpointTarget u)) = 2 := by
  simp_rw [endpoint_replaced_thresholdScore]
  rw [average_incoming_thresholdCost]
  norm_num

/-- Removing the tactic term fails even after nonnegative rescaling of
    the remaining threshold score. This does not exclude other potentials. -/
theorem threshold_only_scaled_drift_fails (c : ℝ) (hc : 0 ≤ c) :
    ¬ (1 + average (2 / 3)
      (fun u => c * thresholdScore (replace endpointWitness endpointTarget u)) ≤
        c * thresholdScore endpointWitness) := by
  rw [average_const_mul, endpoint_threshold_average, endpoint_thresholdScore]
  nlinarith

end MTChainFormal.BiasedResampling.Controls
