import SeparableBase

set_option autoImplicit false

namespace PotentialSeparation

open MTChainFormal
open scoped BigOperators

/-- An ascending selected pair, a strong valid prefix and a remote final failure. -/
def witness (n j : ℕ) (a b : Fin 3) (r : Fin 4) : ChainState n where
  values k := if k.val + 1 < j then 2 else if k.val + 1 = j then a
    else if k.val + 1 = j + 1 then b else 1
  tactic k := if k.val = n - 1 then 1 else if k.val = j then r else 0

theorem witness_value {n j : ℕ} (hn : 4 ≤ n) (hj : 1 ≤ j)
    (hjn : j + 1 ≤ n - 2) (a b : Fin 3) (r : Fin 4) (k : ℕ) (hk : k < n) :
    value (witness n j a b r) k =
      if k = 0 then 2 else if k < j then 2 else if k = j then a
        else if k = j + 1 then b else 1 := by
  by_cases hzero : k = 0
  · simp [hzero]
  have hlt : k - 1 < n - 1 := by omega
  have heq : k - 1 + 1 = k := by omega
  have hsub : (k - 1 = j) ↔ k = j + 1 := by omega
  simp [value, hzero, hlt, witness, heq, hsub]

theorem witness_remote {n j : ℕ} (hn : 4 ≤ n) (hj : 1 ≤ j)
    (hjn : j + 1 ≤ n - 2) (a b : Fin 3) (r : Fin 4) :
    RemoteFailure (witness n j a b r) := by
  refine ⟨?_, ⟨⟨n - 1, by omega⟩, rfl, ?_⟩⟩
  · rw [witness_value hn hj hjn a b r (n - 1) (by omega)]
    simp only [show n - 1 ≠ 0 by omega, show ¬n - 1 < j by omega,
      show n - 1 ≠ j by omega, show n - 1 ≠ j + 1 by omega,
      ↓reduceIte]
  · simp [witness]

theorem witness_selected {n j : ℕ} (hn : 4 ≤ n) (hj : 1 ≤ j)
    (hjn : j + 1 ≤ n - 2) (a b : Fin 3) (r : Fin 4) (hab : a < b) :
    firstFailure (witness n j a b r) = some ⟨j, by omega⟩ := by
  apply firstFailure_of_failed_prefix
  · have ha := witness_value hn hj hjn a b r j (by omega)
    have hb := witness_value hn hj hjn a b r (j + 1) (by omega)
    simp only [show j ≠ 0 by omega, lt_self_iff_false, ↓reduceIte] at ha
    simp only [show j + 1 ≠ 0 by omega, show ¬j + 1 < j by omega,
      show j + 1 ≠ j by omega, ↓reduceIte] at hb
    have ht : (witness n j a b r).tactic ⟨j, by omega⟩ = r := by
      simp [witness, show j ≠ n - 1 by omega]
    simp only [passes, ha, hb, ht, MTChainProof.bridgePass]
    split_ifs <;> simp_all [ne_of_lt hab, not_le_of_gt hab]
  · intro k hk
    change k.val < j at hk
    have hfirst := witness_value hn hj hjn a b r k.val k.isLt
    have hnext := witness_value hn hj hjn a b r (k.val + 1) (by omega)
    have ht : (witness n j a b r).tactic k = 0 := by
      simp [witness, show k.val ≠ n - 1 by omega, show k.val ≠ j by omega]
    have hin : value (witness n j a b r) k.val = 2 := by
      rw [hfirst]
      split_ifs <;> simp_all
    simp only [passes, hin, ht, MTChainProof.bridgePass]
    simpa using Fin.le_last (value (witness n j a b r) (k.val + 1))

theorem witness_replaced_remote {n j : ℕ} (hn : 4 ≤ n) (hj : 1 ≤ j)
    (hjn : j + 1 ≤ n - 2) (a b : Fin 3) (r : Fin 4) (u : Draw) :
    RemoteFailure (replace (witness n j a b r) ⟨j, by omega⟩ u) := by
  refine ⟨?_, ⟨⟨n - 1, by omega⟩, rfl, ?_⟩⟩
  · rw [replace_value (by omega : 2 ≤ n) _ _ _ (n - 1) (by omega)]
    simp only [show n - 1 ≠ 0 by omega, show n - 1 ≠ n by omega,
      show n - 1 ≠ j by omega, show n - 1 ≠ j + 1 by omega, ↓reduceIte]
    exact (witness_remote hn hj hjn a b r).1
  · simp [replace, witness, show (n - 1 : ℕ) ≠ j by omega]

theorem sum_update_delta {m : ℕ} (h : Fin m → ℝ) (i : Fin m) (a : ℝ) :
    (∑ k, Function.update h i a k) = (∑ k, h k) - h i + a := by
  classical
  have hnew := Finset.sum_update_of_mem (Finset.mem_univ i) h a
  have hold := Finset.sum_update_of_mem (Finset.mem_univ i) h (h i)
  have heq : Function.update h i (h i) = h := Function.update_eq_self_iff.mpr rfl
  rw [heq] at hold
  linarith

theorem rawScore_replace {n j : ℕ} (hn : 4 ≤ n) (hj : 1 ≤ j)
    (hjn : j + 1 ≤ n - 2) (c : ℝ) (f : ThresholdCosts) (g : TacticCosts)
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
      simp [replace, i, right, show j + 1 ≠ j by omega]
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
        have hright : k.val + 1 ≠ j + 1 := by
          intro h
          apply hr
          apply Fin.ext
          simp only [right]
          omega
        have hvalright : k.val ≠ j := by
          intro h
          apply hr
          exact Fin.ext h
        simp [replace, i, costs, hr, hl, hleft, hright, hvalright]
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

theorem drawAverage_fst (a : Fin 3 → ℝ) :
    drawAverage (fun u => a u.1) = mean3 a := by
  norm_num [drawAverage, Fintype.sum_prod_type, Fin.sum_univ_succ, mean3]
  <;> ring

theorem drawAverage_snd (a : Fin 3 → ℝ) :
    drawAverage (fun u => a u.2.1) = mean3 a := by
  norm_num [drawAverage, Fintype.sum_prod_type, Fin.sum_univ_succ, mean3]
  <;> ring

theorem drawAverage_third (a : Fin 4 → ℝ) :
    drawAverage (fun u => a u.2.2) = mean4 a := by
  norm_num [drawAverage, Fintype.sum_prod_type, Fin.sum_univ_succ, mean4]
  <;> ring

theorem average_rawScore_replace {n j : ℕ} (hn : 4 ≤ n) (hj : 1 ≤ j)
    (hjn : j + 1 ≤ n - 2) (c : ℝ) (f : ThresholdCosts) (g : TacticCosts)
    (s : ChainState n) :
    drawAverage (fun u => rawScore c f g (replace s ⟨j, by omega⟩ u)) =
      rawScore c f g s - f j (value s j) + mean3 (f j)
        - f (j + 1) (value s (j + 1)) + mean3 (f (j + 1))
        - g j (s.tactic ⟨j, by omega⟩) + mean4 (g j) := by
  simp_rw [rawScore_replace hn hj hjn c f g]
  simp only [drawAverage_add, drawAverage_sub, drawAverage_const,
    drawAverage_fst, drawAverage_snd, drawAverage_third]

/-- The remote failure keeps every witness redraw active, so terminal resetting
    cannot manufacture the witness drift. -/
theorem witness_drift {n j : ℕ} (hn : 4 ≤ n) (hj : 1 ≤ j)
    (hjn : j + 1 ≤ n - 2) (c : ℝ) (f : ThresholdCosts) (g : TacticCosts)
    (δ : ℝ) (hd : PointwiseDrift (n := n) c f g δ)
    (a b : Fin 3) (hab : a < b) (r : Fin 4) :
    δ ≤ f j a - mean3 (f j) + f (j + 1) b - mean3 (f (j + 1)) +
      g j r - mean4 (g j) := by
  have h := hd (witness n j a b r) ⟨j, by omega⟩
    (witness_selected hn hj hjn a b r hab)
  rw [potential_of_active c f g _ (remote_active (by omega) _
    (witness_remote hn hj hjn a b r))] at h
  have hrep (u : Draw) :
      potential c f g (replace (witness n j a b r) ⟨j, by omega⟩ u) =
        rawScore c f g (replace (witness n j a b r) ⟨j, by omega⟩ u) :=
    potential_of_active c f g _ (remote_active (by omega) _
      (witness_replaced_remote hn hj hjn a b r u))
  simp_rw [hrep] at h
  rw [average_rawScore_replace hn hj hjn c f g] at h
  have ha := witness_value hn hj hjn a b r j (by omega)
  have hb := witness_value hn hj hjn a b r (j + 1) (by omega)
  have ht : (witness n j a b r).tactic ⟨j, by omega⟩ = r := by
    simp [witness, show j ≠ n - 1 by omega]
  simp only [show j ≠ 0 by omega, lt_self_iff_false, ↓reduceIte] at ha
  simp only [show j + 1 ≠ 0 by omega, show ¬j + 1 < j by omega,
    show j + 1 ≠ j by omega, ↓reduceIte] at hb
  rw [ha, hb, ht] at h
  linarith

theorem averaged_label_drift {n j : ℕ} (hn : 4 ≤ n) (hj : 1 ≤ j)
    (hjn : j + 1 ≤ n - 2) (c : ℝ) (f : ThresholdCosts) (g : TacticCosts)
    (δ : ℝ) (hd : PointwiseDrift (n := n) c f g δ)
    (a b : Fin 3) (hab : a < b) :
    δ ≤ f j a - mean3 (f j) + f (j + 1) b - mean3 (f (j + 1)) := by
  have h0 := witness_drift hn hj hjn c f g δ hd a b hab 0
  have h1 := witness_drift hn hj hjn c f g δ hd a b hab 1
  have h2 := witness_drift hn hj hjn c f g δ hd a b hab 2
  have h3 := witness_drift hn hj hjn c f g δ hd a b hab 3
  norm_num [mean4, Fin.sum_univ_succ] at h0 h1 h2 h3
  linarith

/-- Twelve genuine raw-state drift inequalities force this spatial gradient. -/
theorem contrast_gradient {n : ℕ} (hn : 4 ≤ n)
    (c : ℝ) (f : ThresholdCosts) (g : TacticCosts) (δ : ℝ)
    (hd : PointwiseDrift (n := n) c f g δ)
    (j : ℕ) (hj : 1 ≤ j) (hjn : j + 1 ≤ n - 2) :
    3 * δ ≤ contrast f j - contrast f (j + 1) := by
  have h01 := averaged_label_drift hn hj hjn c f g δ hd 0 1 (by decide)
  have h12 := averaged_label_drift hn hj hjn c f g δ hd 1 2 (by decide)
  have h02 := averaged_label_drift hn hj hjn c f g δ hd 0 2 (by decide)
  norm_num [mean3, Fin.sum_univ_succ] at h01 h12 h02
  unfold contrast
  linarith

end PotentialSeparation

#print axioms PotentialSeparation.witness_selected
#print axioms PotentialSeparation.witness_replaced_remote
#print axioms PotentialSeparation.rawScore_replace
#print axioms PotentialSeparation.contrast_gradient
