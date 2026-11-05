module

public import ExceptionalBound
public import FinalQuadratic

@[expose] public section

/-!
A linear potential for the same registered initialized chain.
The additional ingredient is a uniform constant bound on exceptional
local-potential growth; all actual filtering and regular-row theorems
are reused without changing the prior formalization.
-/

set_option autoImplicit false

namespace MTChainFormal.Tightness

open scoped BigOperators ENNReal
open Filtering ProductFiltering ObservedFeatures

noncomputable def linearPotential {n : ℕ} (s : ChainState n) : ℝ :=
  1000 * ((n : ℝ) - (barrierHeight s : ℝ)) + localPotential s

theorem linearPotential_nonneg {n : ℕ} (s : ChainState n) :
    0 ≤ linearPotential s := by
  have hf : (barrierHeight s : ℝ) ≤ n := by exact_mod_cast barrierHeight_le s
  have hb := localPotential_nonneg s
  unfold linearPotential
  linarith

theorem linearPotential_le {n : ℕ} (hn : 2 ≤ n) (s : ChainState n) :
    linearPotential s ≤ 1054 * (n : ℝ) := by
  have hf : (0 : ℝ) ≤ barrierHeight s := Nat.cast_nonneg _
  have hb := localPotential_le hn s
  unfold linearPotential
  linarith

@[simp] theorem linearPotential_of_good {n : ℕ} (s : ChainState n)
    (hg : firstFailure s = none) : linearPotential s = 0 := by
  simp [linearPotential, barrierHeight_of_good s hg, localPotential_of_good s hg]

theorem completionMean_linearPotential {n : ℕ} (q : PrefixDatum n) (hq : ValidDatum q) :
    completionMean q linearPotential = linearPotential q.2 := by
  calc
    _ = completionMean q (fun _ => linearPotential q.2) :=
      completionMean_congr q hq _ _ fun s hs => by
        unfold linearPotential
        rw [barrierHeight_congr q.2 s q.1 hq.1 hs,
          localPotential_congr q.2 s q.1 hq.1 hs]
    _ = _ := completionMean_const _ _

theorem linear_expected_decomposition {n : ℕ} (s : ChainState n) (i : Fin n) :
    drawAverage (fun u => linearPotential (replace s i u)) =
      1000 * ((n : ℝ) - drawAverage
        (fun u => (barrierHeight (replace s i u) : ℝ))) +
      drawAverage (fun u => localPotential (replace s i u)) := by
  simp only [linearPotential, drawAverage_add, drawAverage_mul, drawAverage_sub,
    drawAverage_const]

theorem completed_barrier_mono {n : ℕ} (hn : 2 ≤ n)
    (q : PrefixDatum n) (hq : ValidDatum q) :
    (barrierHeight q.2 : ℝ) ≤ completionMean q (fun s => drawAverage
      (fun u => (barrierHeight (replace s q.1 u) : ℝ))) := by
  calc
    _ = completionMean q (fun _ => (barrierHeight q.2 : ℝ)) := (completionMean_const _ _).symm
    _ ≤ _ := completionMean_mono q hq _ _ fun s hs => by
      have hi := firstFailure_eq_of_agrees q.2 s q.1 hq.1 _ le_rfl hs
      have heq := barrierHeight_congr q.2 s q.1 hq.1 hs
      calc
        _ = drawAverage (fun _ => (barrierHeight q.2 : ℝ)) := (drawAverage_const _).symm
        _ ≤ _ := drawAverage_mono fun u => by
          have hm := barrierHeight_mono_replace hn s q.1 u hi
          rw [heq] at hm
          exact_mod_cast hm

theorem completed_exceptional_barrier_advance {n : ℕ} (hn : 2 ≤ n)
    (q : PrefixDatum n) (hq : ValidDatum q)
    (he : q.1.val = 0 ∨ value q.2 (q.1.val - 1) = 2) :
    (barrierHeight q.2 : ℝ) + 1 / 4 ≤ completionMean q (fun s => drawAverage
      (fun u => (barrierHeight (replace s q.1 u) : ℝ))) := by
  calc
    _ = completionMean q (fun _ => (barrierHeight q.2 : ℝ) + 1 / 4) :=
      (completionMean_const _ _).symm
    _ ≤ _ := completionMean_mono q hq _ _ fun s hs => by
      have hi := firstFailure_eq_of_agrees q.2 s q.1 hq.1 _ le_rfl hs
      have hex : q.1.val = 0 ∨ value s (q.1.val - 1) = 2 := by
        rcases he with hfirst | hprev
        · exact Or.inl hfirst
        · right
          rw [value_eq_of_agrees q.2 s _ hs _ (by omega)]
          exact hprev
      have hbar := barrierHeight_average_advance hn s q.1 hi hex
      rw [← drawAverage_eq_sum_div] at hbar
      rw [barrierHeight_congr q.2 s q.1 hq.1 hs] at hbar
      exact hbar

theorem completed_linear_potential_drift {n : ℕ} (hn : 2 ≤ n)
    (q : PrefixDatum n) (hq : ValidDatum q) :
    completionMean q (fun s => drawAverage
      (fun u => linearPotential (replace s q.1 u))) ≤ linearPotential q.2 - 1 := by
  by_cases he : q.1.val = 0 ∨ value q.2 (q.1.val - 1) = 2
  · have hbar := completed_exceptional_barrier_advance hn q hq he
    have hlocal := ExceptionalBound.completed_exceptional_local_growth hn q hq he
    simp_rw [linear_expected_decomposition]
    rw [completionMean_add, completionMean_mul, completionMean_sub, completionMean_const]
    unfold linearPotential
    linarith
  · have hbar := completed_barrier_mono hn q hq
    have hlocal := completed_regular_local_drift hn q hq he
    simp_rw [linear_expected_decomposition]
    rw [completionMean_add, completionMean_mul, completionMean_sub, completionMean_const]
    unfold linearPotential
    linarith

noncomputable def killedLinearPotential {n : ℕ} : KilledState n → ℝ
  | none => 0
  | some a => linearPotential a.val

noncomputable def observedLinearPotential {n : ℕ} : ObservedState n → ℝ
  | none => 0
  | some q => linearPotential q.val.2

@[simp] theorem killedLinearPotential_kill {n : ℕ} (s : ChainState n) :
    killedLinearPotential (kill s) = linearPotential s := by
  classical
  by_cases hbad : (badIndices s).Nonempty
  · simp [kill, hbad, killedLinearPotential]
  · have hg : firstFailure s = none := by simp [firstFailure, hbad]
    simp [kill, hbad, killedLinearPotential, linearPotential_of_good s hg]

theorem completion_linear_potential {n : ℕ} (q : ObservedState n) :
    disaggregate completionWeight killedLinearPotential q = observedLinearPotential q := by
  classical
  cases q with
  | none => simp [disaggregate, completionWeight, killedLinearPotential, observedLinearPotential]
  | some q =>
      rw [disaggregate, completionWeight_expect]
      simp only [killedLinearPotential_kill]
      exact completionMean_linearPotential q.val q.property

theorem expect_chainKernel_linear_selected {n : ℕ} (s : ChainState n) (i : Fin n)
    (hi : firstFailure s = some i) :
    expect (chainKernel n) killedLinearPotential (kill s) =
      drawAverage (fun u => linearPotential (replace s i u)) := by
  have hbad : (badIndices s).Nonempty :=
    ⟨i, (mem_badIndices s i).mpr (selected_failed s i hi)⟩
  let a : ActiveState n := ⟨s, hbad⟩
  have hkill : kill s = some a := kill_of_bad a
  have hsel : activeSelected a = i :=
    Option.some.inj ((activeSelected_firstFailure a).symm.trans hi)
  rw [hkill, expect_chainKernel]
  simp only [killedStep_some, hsel, killedLinearPotential_kill]
  rfl

theorem expect_observedLinearPotential_eq_completed {n : ℕ} (hn : 2 ≤ n)
    (q : ActivePrefix n) :
    expect (observedKernel n) observedLinearPotential (some q) =
      completionMean q.val (fun s => drawAverage
        (fun u => linearPotential (replace s q.val.1 u))) := by
  have hfun : (observedLinearPotential : ObservedState n → ℝ) =
      fun p => disaggregate completionWeight killedLinearPotential p :=
    funext fun p => (completion_linear_potential p).symm
  rw [hfun, expect_disaggregate (observedKernel n) (chainKernel n)
    completionWeight (actual_intertwining hn), disaggregate, completionWeight_expect]
  change (∑ s, rawCompletion q.val s * expect (chainKernel n) killedLinearPotential (kill s)) = _
  apply Finset.sum_congr rfl
  intro s _
  by_cases hs : rawCompletion q.val s = 0
  · simp [hs]
  · rw [expect_chainKernel_linear_selected s q.val.1 (firstFailure_of_completion q s hs)]

theorem observedLinearPotential_nonneg {n : ℕ} (q : ObservedState n) :
    0 ≤ observedLinearPotential q := by
  cases q with
  | none => exact le_rfl
  | some q => exact linearPotential_nonneg q.val.2

theorem observedLinearPotential_le {n : ℕ} (hn : 2 ≤ n) (q : ObservedState n) :
    observedLinearPotential q ≤ 1054 * (n : ℝ) := by
  cases q with
  | none => change 0 ≤ _; positivity
  | some q => exact linearPotential_le hn q.val.2

theorem observed_linear_supersolution {n : ℕ} (hn : 2 ≤ n) :
    ∀ q : ObservedState n,
      activeCost observedActive q + expect (observedKernel n) observedLinearPotential q ≤
        observedLinearPotential q := by
  intro q
  cases q with
  | none =>
      simp [activeCost, observedActive, observedLinearPotential, expect, observedKernel, observedWeight]
  | some q =>
      have hstep := completed_linear_potential_drift hn q.val q.property
      rw [← expect_observedLinearPotential_eq_completed hn q] at hstep
      change 1 + expect (observedKernel n) observedLinearPotential (some q) ≤
        linearPotential q.val.2
      linarith

theorem expected_steps_le_linear {n : ℕ} (hn : 2 ≤ n) :
    expectedSteps n ≤ ENNReal.ofReal (1054 * (n : ℝ)) := by
  exact transported_initialTotalWork_le_uniform (observedKernel n) (chainKernel n)
    completionWeight (actual_intertwining hn) (activeCost observedActive)
    (activeCost killedActive) completion_active_cost initialObserved initialLaw
    (initialLaw_completion n) initialObserved_nonneg (initialObserved_sum n)
    observedLinearPotential observedLinearPotential_nonneg (observed_linear_supersolution hn)
    (1054 * (n : ℝ)) (observedLinearPotential_le hn)

theorem expected_invalidations_le_linear {n : ℕ} (hn : 2 ≤ n) :
    expectedInvalidations n ≤ ENNReal.ofReal (2108 * (n : ℝ)) := by
  calc
    _ ≤ expectedSteps n * 2 := expected_invalidations_le_twice_steps hn
    _ ≤ ENNReal.ofReal (1054 * (n : ℝ)) * 2 :=
      mul_le_mul_of_nonneg_right (expected_steps_le_linear hn) (by positivity)
    _ = _ := by
      rw [show (2 : ℝ≥0∞) = ENNReal.ofReal (2 : ℝ) by norm_num,
        ← ENNReal.ofReal_mul' (by norm_num : (0 : ℝ) ≤ 2)]
      congr 1
      ring

end MTChainFormal.Tightness
