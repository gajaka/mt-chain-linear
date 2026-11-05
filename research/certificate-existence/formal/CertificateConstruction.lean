module

public import SeparationResults

@[expose] public section

set_option autoImplicit false
set_option maxHeartbeats 4000000

/-!
An explicit globally nonnegative separable score with unit stopped pointwise
 drift. The construction proves inhabitedness, not a quadratic upper budget.
The internal replacement helper adapts the pure score algebra from
SeparableWitness.rawScore_replace to every internal mutable pair.
-/

namespace PotentialSeparation.Construction

open MTChainFormal
open scoped BigOperators

def siteWeight (n j : ℕ) : ℝ := (9 : ℝ) ^ (n - 1 - j)

def thresholdCost (n : ℕ) : ThresholdCosts :=
  fun j a => if a = 2 then 0 else 3 * siteWeight n j

def labelWeight (n i : ℕ) : ℝ :=
  if i = 0 ∨ i = n - 1 then 1 else 6 * siteWeight n (i + 1)

def tacticCost (n : ℕ) : TacticCosts :=
  fun i r => if r = 1 then 4 * labelWeight n i else 0

theorem siteWeight_ge_one (n j : ℕ) : 1 ≤ siteWeight n j := by
  exact one_le_pow₀ (by norm_num : (1 : ℝ) ≤ 9)

theorem siteWeight_nonneg (n j : ℕ) : 0 ≤ siteWeight n j :=
  le_trans (by norm_num) (siteWeight_ge_one n j)

theorem siteWeight_step {n j : ℕ} (hj : j + 1 < n) :
    siteWeight n j = 9 * siteWeight n (j + 1) := by
  unfold siteWeight
  rw [show n - 1 - j = (n - 1 - (j + 1)) + 1 by omega, pow_succ]
  ring

@[simp] theorem siteWeight_last (n : ℕ) : siteWeight n (n - 1) = 1 := by
  simp [siteWeight]

theorem thresholdCost_nonneg (n j : ℕ) (a : Fin 3) : 0 ≤ thresholdCost n j a := by
  unfold thresholdCost
  split_ifs
  · exact le_rfl
  · exact mul_nonneg (by norm_num) (siteWeight_nonneg n j)

theorem labelWeight_nonneg (n i : ℕ) : 0 ≤ labelWeight n i := by
  unfold labelWeight
  split_ifs
  · norm_num
  · exact mul_nonneg (by norm_num) (siteWeight_nonneg n (i + 1))

theorem tacticCost_nonneg (n i : ℕ) (r : Fin 4) : 0 ≤ tacticCost n i r := by
  unfold tacticCost
  split_ifs
  · exact mul_nonneg (by norm_num) (labelWeight_nonneg n i)
  · exact le_rfl

theorem mean_thresholdCost (n j : ℕ) : mean3 (thresholdCost n j) = 2 * siteWeight n j := by
  norm_num [mean3, thresholdCost, Fin.sum_univ_succ]
  ring

theorem mean_tacticCost (n i : ℕ) : mean4 (tacticCost n i) = labelWeight n i := by
  norm_num [mean4, tacticCost, Fin.sum_univ_succ]

theorem centered_thresholdCost (n j : ℕ) (a : Fin 3) :
    thresholdCost n j a - mean3 (thresholdCost n j) =
      if a = 2 then -2 * siteWeight n j else siteWeight n j := by
  rw [mean_thresholdCost]
  unfold thresholdCost
  split_ifs <;> ring

theorem centered_tacticCost (n i : ℕ) (r : Fin 4) :
    tacticCost n i r - mean4 (tacticCost n i) =
      if r = 1 then 3 * labelWeight n i else -labelWeight n i := by
  rw [mean_tacticCost]
  unfold tacticCost
  split_ifs <;> ring

theorem rawScore_nonneg {n : ℕ} (s : ChainState n) :
    0 ≤ rawScore 0 (thresholdCost n) (tacticCost n) s := by
  unfold rawScore
  exact add_nonneg (add_nonneg (by norm_num)
    (Finset.sum_nonneg fun j _ => thresholdCost_nonneg n _ _))
    (Finset.sum_nonneg fun i _ => tacticCost_nonneg n _ _)

theorem potential_nonneg {n : ℕ} (s : ChainState n) :
    0 ≤ potential 0 (thresholdCost n) (tacticCost n) s := by
  unfold potential
  split_ifs
  · norm_num
  · exact rawScore_nonneg s

theorem potential_le_rawScore {n : ℕ} (s : ChainState n) :
    potential 0 (thresholdCost n) (tacticCost n) s ≤
      rawScore 0 (thresholdCost n) (tacticCost n) s := by
  unfold potential
  split_ifs
  · exact rawScore_nonneg s
  · exact le_rfl

theorem rawScore_replace_internal {n j : ℕ} (hn : 2 ≤ n) (hj : 1 ≤ j)
    (hjn : j + 1 < n) (c : ℝ) (f : ThresholdCosts) (g : TacticCosts)
    (s : ChainState n) (u : Draw) :
    rawScore c f g (replace s ⟨j, by omega⟩ u) = rawScore c f g s
      - f j (value s j) + f j u.1
      - f (j + 1) (value s (j + 1)) + f (j + 1) u.2.1
      - g j (s.tactic ⟨j, by omega⟩) + g j u.2.2 := by
  classical
  let left : Fin (n - 1) := ⟨j - 1, by omega⟩
  let right : Fin (n - 1) := ⟨j, by omega⟩
  let i : Fin n := ⟨j, by omega⟩
  let costs : Fin (n - 1) → ℝ := fun k => f (k.val + 1) (s.values k)
  let tactics : Fin n → ℝ := fun k => g k.val (s.tactic k)
  have hvals : (fun k : Fin (n - 1) => f (k.val + 1) ((replace s i u).values k)) =
      Function.update (Function.update costs left (f j u.1)) right (f (j + 1) u.2.1) := by
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
        have hvalright : k.val ≠ j := by
          intro h
          apply hr
          exact Fin.ext h
        simp [replace, i, costs, hr, hl, hleft, hvalright]
  have htacs : (fun k : Fin n => g k.val ((replace s i u).tactic k)) =
      Function.update tactics i (g j u.2.2) := by
    funext k
    by_cases hki : k = i
    · subst k
      simp [replace, i]
    · simp [replace, hki, tactics]
  have hrl : right ≠ left := by intro h; have := congrArg Fin.val h; simp only [right, left] at this; omega
  have hvleft : s.values left = value s j := by
    rw [show j = left.val + 1 by simp only [left]; omega, value_internal]
  have hvright : s.values right = value s (j + 1) := by
    simpa only [right] using (value_internal s right).symm
  unfold rawScore
  rw [hvals, htacs, sum_update_delta, sum_update_delta, sum_update_delta]
  simp only [Function.update_of_ne hrl, costs, tactics, left, right, i] at *
  rw [hvleft, hvright]
  rw [show j - 1 + 1 = j by omega]
  ring


theorem tacticSum_replace {n : ℕ} (s : ChainState n) (i : Fin n)
    (u : Draw) (g : TacticCosts) :
    (∑ k : Fin n, g k.val ((replace s i u).tactic k)) =
      (∑ k : Fin n, g k.val (s.tactic k)) - g i.val (s.tactic i) + g i.val u.2.2 := by
  classical
  let h : Fin n → ℝ := fun k => g k.val (s.tactic k)
  have heq : (fun k : Fin n => g k.val ((replace s i u).tactic k)) =
      Function.update h i (g i.val u.2.2) := by
    funext k
    by_cases hk : k = i
    · subst k
      simp [replace]
    · simp [replace, hk, h]
  rw [heq, sum_update_delta]

theorem rawScore_replace_first {n : ℕ} (hn : 2 ≤ n)
    (c : ℝ) (f : ThresholdCosts) (g : TacticCosts)
    (s : ChainState n) (u : Draw) :
    rawScore c f g (replace s ⟨0, by omega⟩ u) = rawScore c f g s
      - f 1 (value s 1) + f 1 u.2.1
      - g 0 (s.tactic ⟨0, by omega⟩) + g 0 u.2.2 := by
  classical
  let first : Fin (n - 1) := ⟨0, by omega⟩
  let i : Fin n := ⟨0, by omega⟩
  let costs : Fin (n - 1) → ℝ := fun k => f (k.val + 1) (s.values k)
  have hvals : (fun k : Fin (n - 1) => f (k.val + 1) ((replace s i u).values k)) =
      Function.update costs first (f 1 u.2.1) := by
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
  unfold rawScore
  rw [hvals, sum_update_delta, tacticSum_replace]
  simp only [costs, first, zero_add] at *
  rw [hv]
  ring

theorem rawScore_replace_last {n : ℕ} (hn : 2 ≤ n)
    (c : ℝ) (f : ThresholdCosts) (g : TacticCosts)
    (s : ChainState n) (u : Draw) :
    rawScore c f g (replace s ⟨n - 1, by omega⟩ u) = rawScore c f g s
      - f (n - 1) (value s (n - 1)) + f (n - 1) u.1
      - g (n - 1) (s.tactic ⟨n - 1, by omega⟩) + g (n - 1) u.2.2 := by
  classical
  let last : Fin (n - 1) := ⟨n - 2, by omega⟩
  let i : Fin n := ⟨n - 1, by omega⟩
  let costs : Fin (n - 1) → ℝ := fun k => f (k.val + 1) (s.values k)
  have hvals : (fun k : Fin (n - 1) => f (k.val + 1) ((replace s i u).values k)) =
      Function.update costs last (f (n - 1) u.1) := by
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
    simpa [last, show n - 2 + 1 = n - 1 by omega] using (value_internal s last).symm
  unfold rawScore
  rw [hvals, sum_update_delta, tacticSum_replace]
  simp only [costs, last, show n - 2 + 1 = n - 1 by omega] at *
  rw [hv]
  ring

theorem average_rawScore_replace_internal {n j : ℕ} (hn : 2 ≤ n)
    (hj : 1 ≤ j) (hjn : j + 1 < n) (c : ℝ) (f : ThresholdCosts)
    (g : TacticCosts) (s : ChainState n) :
    drawAverage (fun u => rawScore c f g (replace s ⟨j, by omega⟩ u)) =
      rawScore c f g s - f j (value s j) + mean3 (f j)
        - f (j + 1) (value s (j + 1)) + mean3 (f (j + 1))
        - g j (s.tactic ⟨j, by omega⟩) + mean4 (g j) := by
  simp_rw [rawScore_replace_internal hn hj hjn c f g]
  simp only [drawAverage_add, drawAverage_sub, drawAverage_const,
    drawAverage_fst, drawAverage_snd, drawAverage_third]

theorem average_rawScore_replace_first {n : ℕ} (hn : 2 ≤ n)
    (c : ℝ) (f : ThresholdCosts) (g : TacticCosts) (s : ChainState n) :
    drawAverage (fun u => rawScore c f g (replace s ⟨0, by omega⟩ u)) =
      rawScore c f g s - f 1 (value s 1) + mean3 (f 1)
        - g 0 (s.tactic ⟨0, by omega⟩) + mean4 (g 0) := by
  simp_rw [rawScore_replace_first hn c f g]
  simp only [drawAverage_add, drawAverage_sub, drawAverage_const,
    drawAverage_snd, drawAverage_third]

theorem average_rawScore_replace_last {n : ℕ} (hn : 2 ≤ n)
    (c : ℝ) (f : ThresholdCosts) (g : TacticCosts) (s : ChainState n) :
    drawAverage (fun u => rawScore c f g (replace s ⟨n - 1, by omega⟩ u)) =
      rawScore c f g s - f (n - 1) (value s (n - 1)) + mean3 (f (n - 1))
        - g (n - 1) (s.tactic ⟨n - 1, by omega⟩) + mean4 (g (n - 1)) := by
  simp_rw [rawScore_replace_last hn c f g]
  simp only [drawAverage_add, drawAverage_sub, drawAverage_const,
    drawAverage_fst, drawAverage_third]

theorem interior_bad_drift (A B : ℝ) (hAB : A = 9 * B) (hB : 1 ≤ B)
    (a b : Fin 3) (r : Fin 4) (hbad : MTChainProof.bridgePass a b r = false) :
    1 ≤ (if a = 2 then -2 * A else A) +
      (if b = 2 then -2 * B else B) + (if r = 1 then 18 * B else -6 * B) := by
  fin_cases a <;> fin_cases b <;> fin_cases r <;>
    norm_num [MTChainProof.bridgePass] at * <;> nlinarith

theorem first_bad_drift (B : ℝ) (hB : 1 ≤ B) (b : Fin 3) (r : Fin 4)
    (hbad : MTChainProof.bridgePass 2 b r = false) :
    1 ≤ (if b = 2 then -2 * B else B) + (if r = 1 then (3 : ℝ) else -1) := by
  fin_cases b <;> fin_cases r <;>
    norm_num [MTChainProof.bridgePass] at * <;> nlinarith

theorem last_bad_drift (a : Fin 3) (r : Fin 4)
    (hbad : MTChainProof.bridgePass a 0 r = false) :
    1 ≤ (if a = 2 then (-2 : ℝ) else 1) + (if r = 1 then (3 : ℝ) else -1) := by
  fin_cases a <;> fin_cases r <;>
    norm_num [MTChainProof.bridgePass] at *

theorem raw_drift_at_failed {n : ℕ} (hn : 2 ≤ n) (s : ChainState n) (i : Fin n)
    (hbad : passes s i = false) :
    1 ≤ rawScore 0 (thresholdCost n) (tacticCost n) s -
      drawAverage (fun u => rawScore 0 (thresholdCost n) (tacticCost n) (replace s i u)) := by
  by_cases hfirst : i.val = 0
  · have hi : i = ⟨0, by omega⟩ := Fin.ext hfirst
    rw [hi] at hbad ⊢
    rw [average_rawScore_replace_first hn]
    have hbad' : MTChainProof.bridgePass 2 (value s 1) (s.tactic ⟨0, by omega⟩) = false := by
      simpa [passes] using hbad
    have h := first_bad_drift (siteWeight n 1) (siteWeight_ge_one n 1)
      (value s 1) (s.tactic ⟨0, by omega⟩) hbad'
    have hf := centered_thresholdCost n 1 (value s 1)
    have hg := centered_tacticCost n 0 (s.tactic ⟨0, by omega⟩)
    simp [labelWeight] at hg
    linarith
  by_cases hlast : i.val = n - 1
  · have hi : i = ⟨n - 1, by omega⟩ := Fin.ext hlast
    rw [hi] at hbad ⊢
    rw [average_rawScore_replace_last hn]
    have hbad' : MTChainProof.bridgePass (value s (n - 1)) 0
        (s.tactic ⟨n - 1, by omega⟩) = false := by
      simpa [passes, show n - 1 + 1 = n by omega, value_right (by omega : 0 < n)] using hbad
    have h := last_bad_drift (value s (n - 1)) (s.tactic ⟨n - 1, by omega⟩) hbad'
    have hf := centered_thresholdCost n (n - 1) (value s (n - 1))
    have hg := centered_tacticCost n (n - 1) (s.tactic ⟨n - 1, by omega⟩)
    simp only [siteWeight_last, mul_one] at hf
    simp [labelWeight] at hg
    linarith
  · have hj : 1 ≤ i.val := by omega
    have hjn : i.val + 1 < n := by omega
    have hav := average_rawScore_replace_internal hn hj hjn 0 (thresholdCost n) (tacticCost n) s
    have hi : (⟨i.val, by omega⟩ : Fin n) = i := Fin.ext rfl
    rw [hi] at hav
    rw [hav]
    have h := interior_bad_drift (siteWeight n i.val) (siteWeight n (i.val + 1))
      (siteWeight_step hjn) (siteWeight_ge_one n (i.val + 1))
      (value s i.val) (value s (i.val + 1)) (s.tactic i) hbad
    have hf := centered_thresholdCost n i.val (value s i.val)
    have hf' := centered_thresholdCost n (i.val + 1) (value s (i.val + 1))
    have hg := centered_tacticCost n i.val (s.tactic i)
    simp only [labelWeight, hfirst, hlast, false_or, ite_false] at hg
    have hg' : tacticCost n i.val (s.tactic i) - mean4 (tacticCost n i.val) =
        if s.tactic i = 1 then 18 * siteWeight n (i.val + 1)
          else -6 * siteWeight n (i.val + 1) := by
      rw [hg]
      split_ifs <;> ring
    linarith

theorem pointwise_drift {n : ℕ} (hn : 2 ≤ n) :
    PointwiseDrift (n := n) 0 (thresholdCost n) (tacticCost n) 1 := by
  intro s i hi
  have hactive : firstFailure s ≠ none := by rw [hi]; simp
  rw [potential_of_active 0 (thresholdCost n) (tacticCost n) s hactive]
  have hav := drawAverage_mono (fun u => potential_le_rawScore (replace s i u))
  have hd := raw_drift_at_failed hn s i (selected_failed s i hi)
  linarith

noncomputable def certificate (n : ℕ) (hn : 2 ≤ n) : DriftCertificate n where
  offset := 0
  thresholdCosts := thresholdCost n
  tacticCosts := tacticCost n
  delta := 1
  delta_positive := by norm_num
  nonnegative := potential_nonneg
  pointwise_drift := pointwise_drift hn

theorem certificate_exists {n : ℕ} (hn : 2 ≤ n) : Nonempty (DriftCertificate n) :=
  ⟨certificate n hn⟩

theorem certificate_exists_of_four_le {n : ℕ} (hn : 4 ≤ n) :
    Nonempty (DriftCertificate n) := certificate_exists (by omega)


theorem geometric_sum (m : ℕ) :
    8 * (∑ j : Fin m, (9 : ℝ) ^ (m - 1 - j.val)) + 1 = (9 : ℝ) ^ m := by
  induction m with
  | zero => simp
  | succ m ih =>
    rw [Fin.sum_univ_succ]
    simp only [Fin.val_zero, Nat.add_sub_cancel, Nat.sub_zero, Fin.val_succ]
    simp_rw [show ∀ j : Fin m, m - (j.val + 1) = m - 1 - j.val by intro j; omega]
    rw [pow_succ]
    nlinarith

theorem initial_raw_mean (m : ℕ) :
    meanInitial (fun s : ChainState (m + 2) =>
      rawScore 0 (thresholdCost (m + 2)) (tacticCost (m + 2)) s) =
      3 * (9 : ℝ) ^ m + 1 := by
  simp only [rawScore, meanInitial_add, meanInitial_const, meanInitial_sum,
    meanInitial_threshold, meanInitial_tactic, mean_thresholdCost, mean_tacticCost]
  have hthreshold : (∑ j : Fin (m + 2 - 1), 2 * siteWeight (m + 2) (j.val + 1)) =
      2 * (9 : ℝ) ^ m + 2 * ∑ j : Fin m, (9 : ℝ) ^ (m - 1 - j.val) := by
    change (∑ j : Fin (m + 1), 2 * siteWeight (m + 2) (j.val + 1)) = _
    rw [Fin.sum_univ_succ]
    simp only [Fin.val_zero, zero_add, Fin.val_succ, siteWeight]
    simp_rw [show ∀ j : Fin m, m + 2 - 1 - (j.val + 1 + 1) = m - 1 - j.val by
      intro j; omega]
    simp only [show m + 2 - 1 - 1 = m by omega, Finset.mul_sum]
  have hlabels : (∑ i : Fin (m + 2), labelWeight (m + 2) i.val) =
      2 + 6 * ∑ j : Fin m, (9 : ℝ) ^ (m - 1 - j.val) := by
    rw [Fin.sum_univ_succ, Fin.sum_univ_castSucc]
    simp only [Fin.val_zero, Fin.val_succ, Fin.val_castSucc, Fin.val_last]
    have hinner (j : Fin m) : labelWeight (m + 2) (j.val + 1) =
        6 * (9 : ℝ) ^ (m - 1 - j.val) := by
      unfold labelWeight
      rw [ite_eq_right (show ¬(j.val + 1 = 0 ∨ j.val + 1 = m + 2 - 1) by omega)]
      unfold siteWeight
      rw [show m + 2 - 1 - (j.val + 1 + 1) = m - 1 - j.val by omega]
    simp_rw [hinner]
    have hzero : labelWeight (m + 2) 0 = 1 := by simp [labelWeight]
    have hlast : labelWeight (m + 2) (m + 1) = 1 := by
      unfold labelWeight
      rw [ite_eq_left (Or.inr (show m + 1 = m + 2 - 1 by omega))]
    rw [hzero, hlast, ← Finset.mul_sum]
    ring
  rw [hthreshold, hlabels]
  have hgeom := geometric_sum m
  linarith

theorem initial_budget_upper {n : ℕ} (hn : 2 ≤ n) :
    initialBudget n 0 (thresholdCost n) (tacticCost n) ≤
      3 * (9 : ℝ) ^ (n - 2) + 1 := by
  obtain ⟨m, hm⟩ := Nat.exists_eq_add_of_le hn
  have heq : n = m + 2 := by omega
  clear hm
  subst n
  change meanInitial (fun s : ChainState (m + 2) =>
    potential 0 (thresholdCost (m + 2)) (tacticCost (m + 2)) s) ≤ _
  have hle := meanInitial_mono
    (fun s : ChainState (m + 2) => potential 0 (thresholdCost (m + 2)) (tacticCost (m + 2)) s)
    (fun s => rawScore 0 (thresholdCost (m + 2)) (tacticCost (m + 2)) s)
    potential_le_rawScore
  rw [initial_raw_mean] at hle
  simpa using hle

end PotentialSeparation.Construction

#print axioms PotentialSeparation.Construction.pointwise_drift
#print axioms PotentialSeparation.Construction.certificate_exists

#print axioms PotentialSeparation.Construction.initial_budget_upper
