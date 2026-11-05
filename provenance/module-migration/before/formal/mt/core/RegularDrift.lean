import PayoffAverages

set_option autoImplicit false

namespace MTChainFormal

open scoped BigOperators
open Filtering ProductFiltering ObservedFeatures ActualScan ActualStep
open PotentialAlgebra TailScan ScanBounds

/-- The zero-boundary and one-mode rows share the same affine proxy. -/
theorem localPotential_previous_one {n : ℕ} (s : ChainState n) (i : Fin n)
    (hi : firstFailure s = some i) (hip : 0 < i.val)
    (hv : value s (i.val - 1) = 1) :
    localPotential s = 35 * (((i.val + 1 : ℕ) : ℝ) - (barrierHeight s : ℝ)) := by
  have hz := zeroCount_before_previous_one s i hi hip hv
  have hrun : zeroRun s = if value s i.val = 0 then 1 else 0 := by
    rw [zeroRun_of_selected s i hi, prefixZeroCount_succ, hz, zero_add]
  have hnat := retainedDistance_identity s i hi
  rw [failureIndex_of_selected s i hi] at hnat
  have hreal : (retainedDistance s : ℝ) + (zeroRun s : ℝ) + (barrierHeight s : ℝ) =
      ((i.val + 1 : ℕ) : ℝ) := by exact_mod_cast hnat
  by_cases hin : value s i.val = 0
  · rw [ite_eq_left hin] at hrun
    simp only [localPotential, localValue, zeroIndicator, hrun]
    norm_num
    rw [hrun] at hreal
    norm_num at hreal
    linarith
  · rw [ite_eq_right hin] at hrun
    simp only [localPotential, localValue, zeroIndicator, hrun]
    norm_num
    rw [hrun] at hreal
    norm_num at hreal
    linarith

theorem completed_previous_one_local_drift {n : ℕ} (hn : 2 ≤ n)
    (q : PrefixDatum n) (hq : ValidDatum q) (hip : 0 < q.1.val)
    (hv : value q.2 (q.1.val - 1) = 1)
    (m : ℕ) (hm : q.1.val + 1 + m + 1 = n) :
    completionMean q (fun s => drawAverage
      (fun u => localPotential (replace s q.1 u))) ≤ localPotential q.2 - 1 := by
  let b : ℕ := barrierHeight q.2
  let d : ℝ := ((q.1.val + 1 : ℕ) : ℝ) - (b : ℝ)
  have hlin : d + (b : ℝ) = ((q.1.val + 1 : ℕ) : ℝ) := by dsimp [d]; ring
  have hd : 1 ≤ d := by
    have hf := barrierHeight_le_selected q.2 q.1 hq.1
    have hcast : (b : ℝ) ≤ (q.1.val : ℝ) := by exact_mod_cast hf
    dsimp [d]
    push_cast
    linarith
  have hlocal : localPotential q.2 = localValue d 0 0 := by
    rw [localPotential_previous_one q.2 q.1 hq.1 hip hv]
    simp [localValue, d, b]
  let prev : Fin n := ⟨q.1.val - 1, by omega⟩
  by_cases ht : q.2.tactic prev = 1
  · have hrow := completed_step_le_payoff q hq m hm (weakPayoff m d) (by
      intro s hs u
      have hi := firstFailure_eq_of_agrees q.2 s q.1 hq.1 _ le_rfl hs
      have hb : b ≤ barrierHeight s := by rw [barrierHeight_congr q.2 s q.1 hq.1 hs]
      have hpv : value s (q.1.val - 1) = 1 := by
        rw [value_eq_of_agrees q.2 s _ hs _ (by omega)]; exact hv
      have hpt := hs (.inr prev) (by simp [prev])
      change s.tactic prev = q.2.tactic prev at hpt
      have hts : s.tactic prev = 1 := hpt.trans ht
      exact actual_weak_step_bound hn s q.1 hi hip hpv hts m hm b d hb hd hlin
        u.1 u.2.1 u.2.2)
    simp only [average_weakPayoff] at hrow
    rw [hlocal]
    have hscalar := average_weakStep_le m d hd
    linarith
  · have hrow := completed_step_le_payoff q hq m hm (strongPayoff m d) (by
      intro s hs u
      have hi := firstFailure_eq_of_agrees q.2 s q.1 hq.1 _ le_rfl hs
      have hb : b ≤ barrierHeight s := by rw [barrierHeight_congr q.2 s q.1 hq.1 hs]
      have hpv : value s (q.1.val - 1) = 1 := by
        rw [value_eq_of_agrees q.2 s _ hs _ (by omega)]; exact hv
      have hpt := hs (.inr prev) (by simp [prev])
      change s.tactic prev = q.2.tactic prev at hpt
      have hts : s.tactic prev ≠ 1 := by rw [hpt]; exact ht
      exact actual_strong_step_bound hn s q.1 hi hip hpv hts m hm b d hb hd hlin
        u.1 u.2.1 u.2.2)
    simp only [average_strongPayoff] at hrow
    rw [hlocal]
    exact le_trans hrow (average_strongStep_le m d hd)

theorem completed_deepZero_local_drift {n : ℕ} (hn : 2 ≤ n)
    (q : PrefixDatum n) (hq : ValidDatum q) (hip : 0 < q.1.val)
    (hv : value q.2 (q.1.val - 1) = 0)
    (m : ℕ) (hm : q.1.val + 1 + m + 1 = n) :
    completionMean q (fun s => drawAverage
      (fun u => localPotential (replace s q.1 u))) ≤ localPotential q.2 - 1 := by
  let b : ℕ := barrierHeight q.2
  let r : ℕ := zeroRun q.2
  let d : ℝ := (retainedDistance q.2 : ℝ)
  have hd : 0 ≤ d := Nat.cast_nonneg _
  have hr2 : (2 : ℝ) ≤ (r : ℝ) := by
    exact_mod_cast zeroRun_two_le_of_previous_zero q.2 q.1 hq.1 hip hv
  have hlin : d + (r : ℝ) + (b : ℝ) = ((q.1.val + 1 : ℕ) : ℝ) := by
    have heq := retainedDistance_identity q.2 q.1 hq.1
    rw [failureIndex_of_selected q.2 q.1 hq.1] at heq
    dsimp [d, r, b]
    exact_mod_cast heq
  have hlocal : localPotential q.2 = localValue d (r : ℝ) 1 := by
    unfold localPotential
    have hrpos : zeroRun q.2 ≠ 0 := by
      have hh := zeroRun_two_le_of_previous_zero q.2 q.1 hq.1 hip hv
      omega
    simp only [zeroIndicator, hrpos, ite_false]
    rfl
  have hrow := completed_step_le_payoff q hq m hm (deepZeroPayoff m d (r : ℝ)) (by
    intro s hs u
    have hi := firstFailure_eq_of_agrees q.2 s q.1 hq.1 _ le_rfl hs
    have hb : b ≤ barrierHeight s := by rw [barrierHeight_congr q.2 s q.1 hq.1 hs]
    have hpv : value s (q.1.val - 1) = 0 := by
      rw [value_eq_of_agrees q.2 s _ hs _ (by omega)]; exact hv
    have hr : zeroRun s = r := zeroRun_congr q.2 s q.1 hq.1 hs
    exact actual_deepZero_step_bound hn s q.1 hi hip hpv m hm b r d hb hd hr hlin
      u.1 u.2.1 u.2.2)
  simp only [MTChainFormal.average_deepZeroPayoff] at hrow
  rw [hlocal]
  exact le_trans hrow (average_deepZeroStep_le m d (r : ℝ) hd hr2)

theorem completed_last_previous_one_local_drift {n : ℕ} (hn : 2 ≤ n)
    (q : PrefixDatum n) (hq : ValidDatum q) (hip : 0 < q.1.val)
    (hv : value q.2 (q.1.val - 1) = 1) (hlast : q.1.val + 1 = n) :
    completionMean q (fun s => drawAverage
      (fun u => localPotential (replace s q.1 u))) ≤ localPotential q.2 - 1 := by
  let b : ℕ := barrierHeight q.2
  let d : ℝ := ((q.1.val + 1 : ℕ) : ℝ) - (b : ℝ)
  have hlin : d + (b : ℝ) = ((q.1.val + 1 : ℕ) : ℝ) := by dsimp [d]; ring
  have hlocal : localPotential q.2 = localValue d 0 0 := by
    rw [localPotential_previous_one q.2 q.1 hq.1 hip hv]
    simp [localValue, d, b]
  have hnonneg : 0 ≤ localValue d 0 0 := by rw [← hlocal]; exact localPotential_nonneg _
  let prev : Fin n := ⟨q.1.val - 1, by omega⟩
  have hpoint (s : ChainState n)
      (hs : Agrees (readCoords (q.1.val + 1)) (toCoords q.2) (toCoords s)) :
      drawAverage (fun u => localPotential (replace s q.1 u)) ≤ localPotential q.2 - 1 := by
    have hi := firstFailure_eq_of_agrees q.2 s q.1 hq.1 _ le_rfl hs
    have hb : b ≤ barrierHeight s := by rw [barrierHeight_congr q.2 s q.1 hq.1 hs]
    have hpv : value s (q.1.val - 1) = 1 := by
      rw [value_eq_of_agrees q.2 s _ hs _ (by omega)]; exact hv
    have hpt := hs (.inr prev) (by simp [prev])
    change s.tactic prev = q.2.tactic prev at hpt
    rw [hlocal]
    by_cases ht : q.2.tactic prev = 1
    · have hts : s.tactic prev = 1 := hpt.trans ht
      calc
        _ ≤ drawAverage (fun u => lastWeakStep (localValue d 0 0) u.1 u.2.1 u.2.2) :=
          drawAverage_mono fun u => actual_last_weak_step_bound hn s q.1 hi hip hpv hts
            hlast b d hb hlin u.1 u.2.1 u.2.2
        _ = _ := drawAverage_eq_average36 _
        _ ≤ _ := average_lastWeakStep_le _ hnonneg
    · have hts : s.tactic prev ≠ 1 := by rw [hpt]; exact ht
      calc
        _ ≤ drawAverage (fun u => lastStrongStep (localValue d 0 0) u.1 u.2.1 u.2.2) :=
          drawAverage_mono fun u => actual_last_strong_step_bound hn s q.1 hi hip hpv hts
            hlast b d hb hlin u.1 u.2.1 u.2.2
        _ = _ := drawAverage_eq_average36 _
        _ ≤ _ := average_lastStrongStep_le _ hnonneg
  calc
    _ ≤ completionMean q (fun _ => localPotential q.2 - 1) :=
      completionMean_mono q hq _ _ hpoint
    _ = _ := completionMean_const _ _

theorem last_previous_ne_zero {n : ℕ} (s : ChainState n) (i : Fin n)
    (hi : firstFailure s = some i) (hip : 0 < i.val) (hlast : i.val + 1 = n) :
    value s (i.val - 1) ≠ 0 := by
  intro hv
  have hle := selected_incoming_le_previous s i hi hip
  rw [hv] at hle
  have hin : value s i.val = 0 := Fin.le_zero_iff.mp hle
  have hf := selected_failed s i hi
  have hp : passes s i = true := by
    simp only [passes, hin, hlast, value_right (by omega : 0 < n)]
    exact bridge_equal_table _ _
  rw [hf] at hp
  cases hp

theorem completed_regular_local_drift {n : ℕ} (hn : 2 ≤ n)
    (q : PrefixDatum n) (hq : ValidDatum q)
    (he : ¬(q.1.val = 0 ∨ value q.2 (q.1.val - 1) = 2)) :
    completionMean q (fun s => drawAverage
      (fun u => localPotential (replace s q.1 u))) ≤ localPotential q.2 - 1 := by
  have hip : 0 < q.1.val := by omega
  have hcases : ∀ v : Fin 3, v = 0 ∨ v = 1 ∨ v = 2 := by decide
  rcases hcases (value q.2 (q.1.val - 1)) with hv | hv | hv
  · by_cases hlast : q.1.val + 1 = n
    · exact (last_previous_ne_zero q.2 q.1 hq.1 hip hlast hv).elim
    · let m := n - (q.1.val + 1) - 1
      have hm : q.1.val + 1 + m + 1 = n := by dsimp [m]; omega
      exact completed_deepZero_local_drift hn q hq hip hv m hm
  · by_cases hlast : q.1.val + 1 = n
    · exact completed_last_previous_one_local_drift hn q hq hip hv hlast
    · let m := n - (q.1.val + 1) - 1
      have hm : q.1.val + 1 + m + 1 = n := by dsimp [m]; omega
      exact completed_previous_one_local_drift hn q hq hip hv m hm
  · exact (he (Or.inr hv)).elim

theorem completed_chain_potential_drift {n : ℕ} (hn : 2 ≤ n)
    (q : PrefixDatum n) (hq : ValidDatum q) :
    completionMean q (fun s => drawAverage
      (fun u => chainPotential (replace s q.1 u))) ≤ chainPotential q.2 - 1 := by
  by_cases he : q.1.val = 0 ∨ value q.2 (q.1.val - 1) = 2
  · exact completed_exceptional_potential_drift hn q hq he
  · exact completed_potential_drift_of_local_drift hn q hq
      (completed_regular_local_drift hn q hq he)

end MTChainFormal
