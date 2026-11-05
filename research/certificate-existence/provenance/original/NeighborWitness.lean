import NeighborDual

set_option autoImplicit false
set_option maxRecDepth 4096
set_option maxHeartbeats 1600000

noncomputable section
namespace NeighborSeparation

open MTChainFormal
open scoped BigOperators

/-- A four - site window behind a strong prefix and before a persistent last failure. -/
def witness (n i : Nat) (a b c d : Fin 3) (l r t : Fin 4) : ChainState n where
  values k := if k.val + 1 < i - 1 then 2 else if k.val + 1 = i - 1 then a
    else if k.val + 1 = i then b else if k.val + 1 = i + 1 then c
    else if k.val + 1 = i + 2 then d else 1
  tactic k := if k.val = n - 1 then 1 else if k.val = i - 1 then l
    else if k.val = i then r else if k.val = i + 1 then t else 0

theorem witness_value {n i : Nat} (hi : 2 <= i) (hin : i + 4 <= n)
    (a b c d : Fin 3) (l r t : Fin 4) (k : Nat) (hk : k < n) :
    value (witness n i a b c d l r t) k =
      if k=0 then 2 else if k < i - 1 then 2 else if k=i - 1 then a
        else if k=i then b else if k=i + 1 then c else if k=i + 2 then d else 1 := by
  by_cases hzero : k=0
  · simp [hzero]
  have hlt : k - 1 < n - 1 := by omega
  have heq : k - 1 + 1 = k := by omega
  have hsub : (k - 1 = i) ↔ k = i + 1 := by omega
  simp [value, hzero, hlt, witness, heq, hsub]

theorem witness_remote {n i : Nat} (hi : 2 <= i) (hin : i + 4 <= n)
    (a b c d : Fin 3) (l r t : Fin 4) : Remote (witness n i a b c d l r t) := by
  refine ⟨?_, ⟨⟨n - 1, by omega⟩, rfl, ?_⟩⟩
  · rw [witness_value hi hin a b c d l r t (n - 1) (by omega)]
    simp only [show n - 1 ≠ 0 by omega, show ¬ n - 1 < i - 1 by omega,
      show n - 1 ≠ i - 1 by omega, show n - 1 ≠ i by omega,
      show n - 1 ≠ i + 1 by omega, show n - 1 ≠ i + 2 by omega, ↓reduceIte]
  · simp [witness]

theorem witness_selected {n i : Nat} (hi : 2 <= i) (hin : i + 4 <= n)
    (a b c d : Fin 3) (l r t : Fin 4)
    (hl : MTChainProof.bridgePass a b l = true)
    (hr : MTChainProof.bridgePass b c r = false) :
    firstFailure (witness n i a b c d l r t) = some ⟨i, by omega⟩ := by
  apply firstFailure_of_failed_prefix
  · have hb := witness_value hi hin a b c d l r t i (by omega)
    have hc := witness_value hi hin a b c d l r t (i + 1) (by omega)
    have ht : (witness n i a b c d l r t).tactic ⟨i, by omega⟩ = r := by
      simp [witness, show i ≠ n - 1 by omega, show i ≠ i - 1 by omega]
    simp only [show i ≠ 0 by omega, show ¬ i < i - 1 by omega,
      show i ≠ i - 1 by omega, ↓reduceIte] at hb
    simp only [show i + 1 ≠ 0 by omega, show ¬ i + 1 < i - 1 by omega,
      show i + 1 ≠ i - 1 by omega, show i + 1 ≠ i by omega, ↓reduceIte] at hc
    simpa [passes, hb, hc, ht] using hr
  · intro k hk
    change k.val < i at hk
    by_cases hlast : k.val = i - 1
    · have ha := witness_value hi hin a b c d l r t k.val k.isLt
      have hb := witness_value hi hin a b c d l r t (k.val + 1) (by omega)
      have ht : (witness n i a b c d l r t).tactic k = l := by
        simp [witness, hlast, show i - 1 ≠ n - 1 by omega]
      have hx : value (witness n i a b c d l r t) k.val = a := by
        rw [ha, hlast]
        simp [show i - 1 ≠ 0 by omega]
      have hy : value (witness n i a b c d l r t) (k.val + 1) = b := by
        rw [hb, show k.val + 1=i by omega]
        simp [show i ≠ 0 by omega, show ¬ i < i - 1 by omega, show i ≠ i - 1 by omega]
      simpa [passes, hx, hy, ht] using hl
    · have hfirst := witness_value hi hin a b c d l r t k.val k.isLt
      have ht : (witness n i a b c d l r t).tactic k = 0 := by
        simp [witness, show k.val ≠ n - 1 by omega, hlast,
          show k.val ≠ i by omega, show k.val ≠ i + 1 by omega]
      have hx : value (witness n i a b c d l r t) k.val = 2 := by
        rw [hfirst]
        split_ifs <;> simp_all
        omega
      simp only [passes, hx, ht, MTChainProof.bridgePass]
      simpa using Fin.le_last (value (witness n i a b c d l r t) (k.val + 1))


theorem replace_value_other {n : Nat} (hn : 2 <= n) (s : ChainState n)
    (i : Fin n) (u : Draw) (k : Nat) (hk : k <= n)
    (hk0 : k ≠ i.val) (hk1 : k ≠ i.val + 1) :
    value (replace s i u) k = value s k := by
  rw [replace_value hn s i u k hk]
  by_cases h0 : k = 0
  · simp [h0]
  by_cases hlast : k = n
  · simp [hlast, show n ≠ 0 by omega, value_right (by omega : 0 < n)]
  simp [h0, hlast, hk0, hk1]

private theorem sum_update_delta {m : Nat} (h : Fin m -> Real) (i : Fin m) (a : Real) :
    (∑ k, Function.update h i a k) = (∑ k, h k) - h i + a := by
  classical
  have hnew := Finset.sum_update_of_mem (Finset.mem_univ i) h a
  have hold := Finset.sum_update_of_mem (Finset.mem_univ i) h (h i)
  have heq : Function.update h i (h i) = h := Function.update_eq_self_iff.mpr rfl
  rw [heq] at hold
  linarith

theorem rawScore_replace {n i : Nat} (hi : 2 <= i) (hin : i + 4 <= n)
    (h : EdgeCosts) (s : ChainState n) (u : Draw) :
    rawScore 0 h (replace s ⟨i, by omega⟩ u) = rawScore 0 h s
      - h (i - 1) (value s (i - 1)) (value s i) (s.tactic ⟨i - 1, by omega⟩)
      + h (i - 1) (value s (i - 1)) u.1 (s.tactic ⟨i - 1, by omega⟩)
      - h i (value s i) (value s (i + 1)) (s.tactic ⟨i, by omega⟩)
      + h i u.1 u.2.1 u.2.2
      - h (i + 1) (value s (i + 1)) (value s (i + 2)) (s.tactic ⟨i + 1, by omega⟩)
      + h (i + 1) u.2.1 (value s (i + 2)) (s.tactic ⟨i + 1, by omega⟩) := by
  classical
  let left : Fin n := ⟨i - 1, by omega⟩
  let mid : Fin n := ⟨i, by omega⟩
  let right : Fin n := ⟨i + 1, by omega⟩
  let old : Fin n -> Real := fun k =>
    h k.val (value s k.val) (value s (k.val + 1)) (s.tactic k)
  let nl := h (i - 1) (value s (i - 1)) u.1 (s.tactic left)
  let nm := h i u.1 u.2.1 u.2.2
  let nr := h (i + 1) u.2.1 (value s (i + 2)) (s.tactic right)
  have hml : mid ≠ left := by intro he; have := congrArg Fin.val he; simp only [mid,left] at this; omega
  have hrl : right ≠ left := by intro he; have := congrArg Fin.val he; simp only [right,left] at this; omega
  have hrm : right ≠ mid := by intro he; have := congrArg Fin.val he; simp only [right,mid] at this; omega
  have hnew : (fun k : Fin n => h k.val (value (replace s mid u) k.val)
      (value (replace s mid u) (k.val + 1)) ((replace s mid u).tactic k)) =
      Function.update (Function.update (Function.update old left nl) mid nm) right nr := by
    funext k
    by_cases hkr : k = right
    · subst k
      have hval : value (replace s mid u) (i + 1) = u.2.1 := by
        rw [replace_value (by omega : 2 <= n) s mid u _ (by omega)]; simp [mid, show i + 1 ≠ n by omega]
      have hnext := replace_value_other (by omega : 2 <= n) s mid u (i + 2)
        (by omega) (by simp only [mid]; omega) (by simp only [mid]; omega)
      simp [right, hval, hnext, replace_tactic_other s mid right u hrm, nr]
    · by_cases hkm : k = mid
      · subst k
        have hv : value (replace s mid u) i = u.1 := by
          rw [replace_value (by omega : 2 <= n) s mid u _ (by omega)]; simp [mid, show i ≠ 0 by omega, show i ≠ n by omega]
        have hnxt : value (replace s mid u) (i + 1) = u.2.1 := by
          rw [replace_value (by omega : 2 <= n) s mid u _ (by omega)]; simp [mid, show i + 1 ≠ n by omega]
        simp [Function.update_of_ne hkr, mid, hv, hnxt, nm]
      · by_cases hkl : k = left
        · subst k
          have hv := replace_value_other (by omega : 2 <= n) s mid u (i - 1)
            (by omega) (by simp only [mid]; omega) (by simp only [mid]; omega)
          have hnxt : value (replace s mid u) i = u.1 := by
            rw [replace_value (by omega : 2 <= n) s mid u _ (by omega)]; simp [mid, show i ≠ 0 by omega, show i ≠ n by omega]
          simp [Function.update_of_ne hkr, Function.update_of_ne hkm, left,
            show i - 1 + 1 = i by omega, hv, hnxt,
            replace_tactic_other s mid left u hml.symm, nl]
        · have h0 : k.val ≠ i := by intro he; apply hkm; exact Fin.ext he
          have h1 : k.val ≠ i + 1 := by intro he; apply hkr; exact Fin.ext he
          have h2 : k.val + 1 ≠ i := by
            intro he; apply hkl; apply Fin.ext; simp only [left]; omega
          have h3 : k.val + 1 ≠ i + 1 := by omega
          have hv := replace_value_other (by omega : 2 <= n) s mid u k.val
            (by omega) h0 h1
          have hnxt := replace_value_other (by omega : 2 <= n) s mid u (k.val + 1)
            (by omega) h2 h3
          simp [hkr,hkm,hkl,old,hv,hnxt,replace_tactic_other s mid k u hkm]
  unfold rawScore
  rw [hnew, sum_update_delta,
    sum_update_delta, sum_update_delta]
  simp only [Function.update_of_ne hrl, Function.update_of_ne hrm,
    Function.update_of_ne hml, old,nl,nm,nr,left,mid,right]
  rw [show i - 1 + 1 = i by omega, show i + 1 + 1 = i + 2 by omega]
  ring


theorem score_drift_local {n i : Nat} (hi : 2 <= i) (hin : i + 4 <= n)
    (h : EdgeCosts) (s : ChainState n) :
    rawScore 0 h s - drawAverage (fun u => rawScore 0 h (replace s ⟨i, by omega⟩ u)) =
      rawLocalDrift (h (i - 1)) (h i) (h (i + 1))
        (value s (i - 1)) (value s i) (value s (i + 1)) (value s (i + 2))
        (s.tactic ⟨i - 1, by omega⟩) (s.tactic ⟨i, by omega⟩)
        (s.tactic ⟨i + 1, by omega⟩) := by
  simp_rw [rawScore_replace hi hin h]
  norm_num [drawAverage, Fintype.sum_prod_type, Fin.sum_univ_succ,
    rawLocalDrift, meanEdge]
  ring

theorem witness_window {n i : Nat} (hi : 2 <= i) (hin : i + 4 <= n)
    (a b c d : Fin 3) (l r t : Fin 4) :
    value (witness n i a b c d l r t) (i - 1) = a ∧
    value (witness n i a b c d l r t) i = b ∧
    value (witness n i a b c d l r t) (i + 1) = c ∧
    value (witness n i a b c d l r t) (i + 2) = d := by
  have ha := witness_value hi hin a b c d l r t (i - 1) (by omega)
  have hb := witness_value hi hin a b c d l r t i (by omega)
  have hc := witness_value hi hin a b c d l r t (i + 1) (by omega)
  have hd := witness_value hi hin a b c d l r t (i + 2) (by omega)
  simp only [show i - 1 ≠ 0 by omega, lt_self_iff_false, ↓reduceIte] at ha
  simp only [show i ≠ 0 by omega, show ¬ i < i - 1 by omega,
    show i ≠ i - 1 by omega, ↓reduceIte] at hb
  simp only [show i + 1 ≠ 0 by omega, show ¬ i + 1 < i - 1 by omega,
    show i + 1 ≠ i - 1 by omega, show i + 1 ≠ i by omega, ↓reduceIte] at hc
  simp only [show i + 2 ≠ 0 by omega, show ¬ i + 2 < i - 1 by omega,
    show i + 2 ≠ i - 1 by omega, show i + 2 ≠ i by omega,
    show i + 2 ≠ i + 1 by omega, ↓reduceIte] at hd
  exact ⟨ha,hb,hc,hd⟩

theorem witness_drift {n i : Nat} (hi : 2 <= i) (hin : i + 4 <= n)
    (h : EdgeCosts) (delta : Real) (hbulk : BulkDrift n h delta)
    (a b c d : Fin 3) (l r t : Fin 4)
    (hl : MTChainProof.bridgePass a b l = true)
    (hr : MTChainProof.bridgePass b c r = false) :
    delta <= rawLocalDrift (h (i - 1)) (h i) (h (i + 1)) a b c d l r t := by
  have hw := hbulk (witness n i a b c d l r t) ⟨i, by omega⟩
    (witness_remote hi hin a b c d l r t)
    (witness_selected hi hin a b c d l r t hl hr) hi hin
  rw [score_drift_local hi hin] at hw
  rcases witness_window hi hin a b c d l r t with ⟨ha,hb,hc,hd⟩
  have htl : (witness n i a b c d l r t).tactic ⟨i - 1, by omega⟩ = l := by
    simp [witness, show i - 1 ≠ n - 1 by omega]
  have htr : (witness n i a b c d l r t).tactic ⟨i, by omega⟩ = r := by
    simp [witness, show i ≠ n - 1 by omega, show i ≠ i - 1 by omega]
  have htt : (witness n i a b c d l r t).tactic ⟨i + 1, by omega⟩ = t := by
    simp [witness, show i + 1 ≠ n - 1 by omega, show i + 1 ≠ i - 1 by omega]
  simpa only [ha,hb,hc,hd,htl,htr,htt] using hw

/-- Fourteen convex combinations of genuine raw-state inequalities. -/
theorem bulk_dual_lower {n i : Nat} (hi : 2 <= i) (hin : i + 4 <= n)
    (h : EdgeCosts) (delta : Real) (hbulk : BulkDrift n h delta) :
    delta <= L (h (i - 1)) + M (h i) + R (h (i + 1)) := by
  apply dual_lower
  intro k
  apply profile_drift_lower
  intro u v w
  apply witness_drift hi hin h delta hbulk
  · exact (lift_pass _ _ _ _).2 (rows_left_pass k)
  · have hf := rows_selected_fail k
    have hiff := lift_pass (rows k).b (rows k).c (rows k).r v
    cases hb : MTChainProof.bridgePass (rows k).b (rows k).c (liftLabel (rows k).r v)
    · rfl
    · exact False.elim (hf (hiff.1 hb))

theorem flux_gradient {n : Nat} (hn : 6 <= n) (h : EdgeCosts) (delta : Real)
    (hbulk : BulkDrift n h delta) (j : Nat) (hj : j + 1 < n - 4) :
    delta <= flux h j - flux h (j + 1) := by
  have hi : 2 <= j + 2 := by omega
  have hin : j + 2 + 4 <= n := by omega
  have hd := bulk_dual_lower hi hin h delta hbulk
  have hid := dual_identity (h (j + 2))
  unfold flux
  rw [show j + 2 - 1 = j + 1 by omega] at hd
  rw [show j + 1 + 1 = j + 2 by omega,
    show j + 1 + 2 = j + 2 + 1 by omega]
  linarith

end NeighborSeparation

#print axioms NeighborSeparation.witness_selected
#print axioms NeighborSeparation.rawScore_replace
#print axioms NeighborSeparation.bulk_dual_lower
#print axioms NeighborSeparation.flux_gradient
