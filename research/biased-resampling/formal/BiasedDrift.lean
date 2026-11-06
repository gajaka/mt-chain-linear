module

public import BiasedLaw

@[expose] public section

set_option autoImplicit false

namespace MTChainFormal.BiasedResampling

open scoped BigOperators

private theorem sum_update_delta {m : ℕ} (h : Fin m → ℝ) (i : Fin m) (a : ℝ) :
    (∑ k, Function.update h i a k) = (∑ k, h k) - h i + a := by
  classical
  have hnew := Finset.sum_update_of_mem (Finset.mem_univ i) h a
  have hold := Finset.sum_update_of_mem (Finset.mem_univ i) h (h i)
  rw [Function.update_eq_self_iff.mpr rfl] at hold
  linarith

private theorem tacticSum_replace {n : ℕ} (s : ChainState n) (i : Fin n)
    (u : Draw) :
    (∑ k, tacticCost ((replace s i u).tactic k)) =
      (∑ k, tacticCost (s.tactic k)) - tacticCost (s.tactic i) + tacticCost u.2.2 := by
  classical
  let h : Fin n → ℝ := fun k => tacticCost (s.tactic k)
  have heq : (fun k : Fin n => tacticCost ((replace s i u).tactic k)) =
      Function.update h i (tacticCost u.2.2) := by
    funext k
    by_cases hk : k = i
    · subst k
      simp [replace]
    · simp [replace, hk, h]
  rw [heq, sum_update_delta]

private theorem potential_replace_first {n : ℕ} (hn : 2 ≤ n)
    (s : ChainState n) (u : Draw) :
    potential (replace s ⟨0, by omega⟩ u) = potential s
      - thresholdCost (value s 1) + thresholdCost u.2.1
      - tacticCost (s.tactic ⟨0, by omega⟩) + tacticCost u.2.2 := by
  classical
  let first : Fin (n - 1) := ⟨0, by omega⟩
  let i : Fin n := ⟨0, by omega⟩
  let costs : Fin (n - 1) → ℝ := fun k => thresholdCost (s.values k)
  have hvals : (fun k : Fin (n - 1) => thresholdCost ((replace s i u).values k)) =
      Function.update costs first (thresholdCost u.2.1) := by
    funext k
    by_cases hk : k = first
    · subst k
      simp [replace, first, i]
    · have hk0 : k.val ≠ 0 := by
        intro h
        exact hk (Fin.ext h)
      simp [replace, i, costs, hk, hk0]
  have hv : s.values first = value s 1 := by
    simpa [first] using (value_internal s first).symm
  unfold potential
  rw [hvals, sum_update_delta, tacticSum_replace]
  simp only [costs, first] at *
  rw [hv]
  ring

private theorem potential_replace_last {n : ℕ} (hn : 2 ≤ n)
    (s : ChainState n) (u : Draw) :
    potential (replace s ⟨n - 1, by omega⟩ u) = potential s
      - thresholdCost (value s (n - 1)) + thresholdCost u.1
      - tacticCost (s.tactic ⟨n - 1, by omega⟩) + tacticCost u.2.2 := by
  classical
  let last : Fin (n - 1) := ⟨n - 2, by omega⟩
  let i : Fin n := ⟨n - 1, by omega⟩
  let costs : Fin (n - 1) → ℝ := fun k => thresholdCost (s.values k)
  have hvals : (fun k : Fin (n - 1) => thresholdCost ((replace s i u).values k)) =
      Function.update costs last (thresholdCost u.1) := by
    funext k
    by_cases hk : k = last
    · subst k
      simp [replace, last, i, show n - 2 + 1 = n - 1 by omega]
    · have hleft : k.val + 1 ≠ n - 1 := by
        intro h
        apply hk
        apply Fin.ext
        simp only [last]
        omega
      have hkEnd : k.val ≠ n - 1 := by have := k.isLt; omega
      simp [replace, i, costs, hk, hleft, hkEnd]
  have hv : s.values last = value s (n - 1) := by
    simpa [last, show n - 2 + 1 = n - 1 by omega] using
      (value_internal s last).symm
  unfold potential
  rw [hvals, sum_update_delta, tacticSum_replace]
  simp only [costs, last] at *
  rw [hv]
  ring

private theorem potential_replace_internal {n j : ℕ} (hn : 2 ≤ n)
    (hj : 0 < j) (hjn : j + 1 < n) (s : ChainState n) (u : Draw) :
    potential (replace s ⟨j, by omega⟩ u) = potential s
      - thresholdCost (value s j) + thresholdCost u.1
      - thresholdCost (value s (j + 1)) + thresholdCost u.2.1
      - tacticCost (s.tactic ⟨j, by omega⟩) + tacticCost u.2.2 := by
  classical
  let left : Fin (n - 1) := ⟨j - 1, by omega⟩
  let right : Fin (n - 1) := ⟨j, by omega⟩
  let i : Fin n := ⟨j, by omega⟩
  let costs : Fin (n - 1) → ℝ := fun k => thresholdCost (s.values k)
  have hvals : (fun k : Fin (n - 1) => thresholdCost ((replace s i u).values k)) =
      Function.update (Function.update costs left (thresholdCost u.1))
        right (thresholdCost u.2.1) := by
    funext k
    by_cases hr : k = right
    · subst k
      simp [replace, i, right]
    · by_cases hl : k = left
      · subst k
        simp [replace, i, left, right, show j - 1 + 1 = j by omega,
          show j - 1 ≠ j by omega]
      · have hleft : k.val + 1 ≠ j := by
          intro h
          apply hl
          apply Fin.ext
          simp only [left]
          omega
        have hright : k.val ≠ j := by
          intro h
          apply hr
          exact Fin.ext h
        simp [replace, i, costs, hr, hl, hleft, hright]
  have hrl : right ≠ left := by
    intro h
    have := congrArg Fin.val h
    simp only [right, left] at this
    omega
  have hvleft : s.values left = value s j := by
    rw [show j = left.val + 1 by simp only [left]; omega, value_internal]
  have hvright : s.values right = value s (j + 1) := by
    simpa only [right] using (value_internal s right).symm
  unfold potential
  rw [hvals, sum_update_delta, sum_update_delta, tacticSum_replace]
  simp only [Function.update_of_ne hrl, costs] at *
  rw [hvleft, hvright]
  ring

private theorem failed_pair_cost (a b : Fin 3) (r : Fin 4)
    (hf : MTChainProof.bridgePass a b r = false) :
    6 ≤ thresholdCost a + thresholdCost b := by
  have hne : a ≠ b := by
    intro h
    subst b
    simp [MTChainProof.bridgePass] at hf
  by_cases ha : a = 2
  · have hb : b ≠ 2 := by simpa [ha] using Ne.symm hne
    simp [thresholdCost, ha, hb]
  · by_cases hb : b = 2 <;> simp [thresholdCost, ha, hb]

private theorem failed_first_cost (b : Fin 3) (r : Fin 4)
    (hf : MTChainProof.bridgePass 2 b r = false) :
    thresholdCost b = 6 ∧ tacticCost r = 4 := by
  fin_cases b <;> fin_cases r <;>
    simp_all [MTChainProof.bridgePass, thresholdCost, tacticCost]

private theorem failed_last_tacticCost (a : Fin 3) (r : Fin 4)
    (hf : MTChainProof.bridgePass a 0 r = false) : tacticCost r = 4 := by
  fin_cases a <;> fin_cases r <;>
    simp_all [MTChainProof.bridgePass, tacticCost]

private theorem average_potential_first {n : ℕ} (hn : 2 ≤ n)
    (p : ℝ) (s : ChainState n) :
    average p (fun u => potential (replace s ⟨0, by omega⟩ u)) = potential s
      - thresholdCost (value s 1) + 6 * (1 - p)
      - tacticCost (s.tactic ⟨0, by omega⟩) + 1 := by
  simp_rw [potential_replace_first hn s]
  simp only [average_add, average_sub, average_const,
    average_outgoing_thresholdCost, average_tacticCost]

private theorem average_potential_last {n : ℕ} (hn : 2 ≤ n)
    (p : ℝ) (s : ChainState n) :
    average p (fun u => potential (replace s ⟨n - 1, by omega⟩ u)) = potential s
      - thresholdCost (value s (n - 1)) + 6 * (1 - p)
      - tacticCost (s.tactic ⟨n - 1, by omega⟩) + 1 := by
  simp_rw [potential_replace_last hn s]
  simp only [average_add, average_sub, average_const,
    average_incoming_thresholdCost, average_tacticCost]

private theorem average_potential_internal {n j : ℕ} (hn : 2 ≤ n)
    (hj : 0 < j) (hjn : j + 1 < n) (p : ℝ) (s : ChainState n) :
    average p (fun u => potential (replace s ⟨j, by omega⟩ u)) = potential s
      - thresholdCost (value s j) + 6 * (1 - p)
      - thresholdCost (value s (j + 1)) + 6 * (1 - p)
      - tacticCost (s.tactic ⟨j, by omega⟩) + 1 := by
  simp_rw [potential_replace_internal hn hj hjn s]
  simp only [average_add, average_sub, average_const,
    average_incoming_thresholdCost, average_outgoing_thresholdCost, average_tacticCost]

/-- This bound uses only failure of the selected original bridge. The
    selector need not be least-failed, and no completion law is assumed. -/
theorem pointwise_drift {n : ℕ} (hn : 2 ≤ n) (p : ℝ)
    (hp : (2 / 3 : ℝ) ≤ p) (_hp1 : p ≤ 1) (s : ChainState n) (i : Fin n)
    (hf : passes s i = false) :
    1 + average p (fun u => potential (replace s i u)) ≤ potential s := by
  obtain ⟨j, hj⟩ := i
  by_cases hfirst : j = 0
  · subst j
    rw [average_potential_first hn p s]
    have hf' : MTChainProof.bridgePass 2 (value s 1)
        (s.tactic ⟨0, hj⟩) = false := by simpa [passes] using hf
    obtain ⟨hthreshold, htactic⟩ := failed_first_cost _ _ hf'
    rw [hthreshold, htactic]
    linarith
  · by_cases hlast : j = n - 1
    · subst j
      rw [average_potential_last hn p s]
      have hf' : MTChainProof.bridgePass (value s (n - 1)) 0
          (s.tactic ⟨n - 1, hj⟩) = false := by
        simpa [passes, show n - 1 + 1 = n by omega,
          value_right (by omega : 0 < n)] using hf
      have htactic := failed_last_tacticCost _ _ hf'
      have hthreshold := thresholdCost_nonneg (value s (n - 1))
      rw [htactic]
      linarith
    · have hjpos : 0 < j := by omega
      have hjn : j + 1 < n := by omega
      rw [average_potential_internal hn hjpos hjn p s]
      have hcost := failed_pair_cost (value s j) (value s (j + 1))
        (s.tactic ⟨j, hj⟩) hf
      have htactic := tacticCost_nonneg (s.tactic ⟨j, hj⟩)
      linarith

end MTChainFormal.BiasedResampling
