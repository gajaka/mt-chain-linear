import FilteredKernel
import CompletionExpect

set_option autoImplicit false

namespace MTChainFormal

open scoped BigOperators
open Filtering

noncomputable def killedPotential {n : ℕ} : KilledState n → ℝ
  | none => 0
  | some a => chainPotential a.val

noncomputable def observedPotential {n : ℕ} : ObservedState n → ℝ
  | none => 0
  | some q => chainPotential q.val.2

@[simp] theorem killedPotential_kill {n : ℕ} (s : ChainState n) :
    killedPotential (kill s) = chainPotential s := by
  classical
  by_cases hbad : (badIndices s).Nonempty
  · simp [kill, hbad, killedPotential]
  · have hg : firstFailure s = none := by simp [firstFailure, hbad]
    simp [kill, hbad, killedPotential, chainPotential_of_good s hg]

theorem completion_chain_potential {n : ℕ} (q : ObservedState n) :
    disaggregate completionWeight killedPotential q = observedPotential q := by
  classical
  cases q with
  | none => simp [disaggregate, completionWeight, killedPotential, observedPotential]
  | some q =>
      rw [disaggregate, completionWeight_expect]
      simp only [killedPotential_kill]
      exact completionMean_chainPotential q.val q.property

theorem expect_chainKernel_kill_selected {n : ℕ} (s : ChainState n) (i : Fin n)
    (hi : firstFailure s = some i) :
    expect (chainKernel n) killedPotential (kill s) =
      drawAverage (fun u => chainPotential (replace s i u)) := by
  have hbad : (badIndices s).Nonempty :=
    ⟨i, (mem_badIndices s i).mpr (selected_failed s i hi)⟩
  let a : ActiveState n := ⟨s, hbad⟩
  have hkill : kill s = some a := kill_of_bad a
  have hsel : activeSelected a = i :=
    Option.some.inj ((activeSelected_firstFailure a).symm.trans hi)
  rw [hkill, expect_chainKernel]
  simp only [killedStep_some, hsel, killedPotential_kill]
  rfl

/-- This lemma transports one step through the exact filtering identity.
    Its concrete identity is proved separately, not supplied by the final user. -/
theorem expect_observedPotential_eq_completed {n : ℕ}
    (hDP : Intertwines (observedKernel n) (chainKernel n) completionWeight)
    (q : ActivePrefix n) :
    expect (observedKernel n) observedPotential (some q) =
      completionMean q.val (fun s => drawAverage
        (fun u => chainPotential (replace s q.val.1 u))) := by
  have hfun : (observedPotential : ObservedState n → ℝ) =
      fun p => disaggregate completionWeight killedPotential p :=
    funext fun p => (completion_chain_potential p).symm
  rw [hfun, expect_disaggregate (observedKernel n) (chainKernel n)
    completionWeight hDP, disaggregate, completionWeight_expect]
  change (∑ s, rawCompletion q.val s * expect (chainKernel n) killedPotential (kill s)) = _
  apply Finset.sum_congr rfl
  intro s _
  by_cases hs : rawCompletion q.val s = 0
  · simp [hs]
  · rw [expect_chainKernel_kill_selected s q.val.1 (firstFailure_of_completion q s hs)]

theorem observedPotential_nonneg {n : ℕ} (q : ObservedState n) :
    0 ≤ observedPotential q := by
  cases q with
  | none => exact le_rfl
  | some q => exact chainPotential_nonneg q.val.2

theorem observedPotential_le {n : ℕ} (hn : 2 ≤ n) (q : ObservedState n) :
    observedPotential q ≤ 283 * (n : ℝ) ^ 2 := by
  cases q with
  | none => change 0 ≤ _; positivity
  | some q => exact chainPotential_le hn q.val.2

end MTChainFormal
