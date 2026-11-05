module

public import RefreshDensity
public import ChainLyapunov

@[expose] public section

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

namespace MTChainFormal.Tightness

open scoped BigOperators
open Filtering ProductFiltering RefreshDensity

theorem fresh_incomingWeight {n : ℕ} (i : Fin n) :
    incomingWeight i freshWeight = freshWeight := by
  classical
  unfold incomingWeight
  split_ifs with h
  · apply Function.update_eq_self_iff.mpr
    rfl
  · rfl

theorem fresh_outgoingWeight {n : ℕ} (i : Fin n) :
    outgoingWeight i freshWeight = freshWeight := by
  classical
  unfold outgoingWeight
  split_ifs with h
  · apply Function.update_eq_self_iff.mpr
    rfl
  · rfl

theorem fresh_tacticWeight {n : ℕ} (i : Fin n) :
    tacticWeight i freshWeight = freshWeight := by
  classical
  unfold tacticWeight
  apply Function.update_eq_self_iff.mpr
  rfl

/-- The original independent product law is invariant under a fixed refresh.
    This is not an assertion that the selected-index chain stays stationary. -/
theorem uniform_fixed_refresh {n : ℕ} (i : Fin n) (f : ChainState n → ℝ) :
    (∑ s, initialFull s * drawAverage (fun u => f (replace s i u))) =
      ∑ s, initialFull s * f s := by
  classical
  let fC := fun x : ∀ c : Coord n, Alphabet c => f (fromCoords x)
  have hreplace (s : ChainState n) (u : Draw) : replace s i u =
      fromCoords (tacticUpdate i (outgoingUpdate i (incomingUpdate i (toCoords s) u.1) u.2.1) u.2.2) := by
    have h := congrArg fromCoords (toCoords_replace s i u)
    simpa only [fromCoords_toCoords] using h
  have hinitial (s : ChainState n) :
      initialFull s = density freshWeight (toCoords s) := (rawInitialDensity_uniform s).symm
  have hc : (∑ x, density freshWeight x *
      ∑ a : Fin 3, (1 / 3 : ℝ) * ∑ b : Fin 3, (1 / 3 : ℝ) *
        ∑ t : Fin 4, (1 / 4 : ℝ) * fC (tacticUpdate i (outgoingUpdate i (incomingUpdate i x a) b) t)) =
      ∑ x, density freshWeight x * fC x := by
    calc
      _ = ∑ x, density freshWeight x *
          ∑ b : Fin 3, (1 / 3 : ℝ) * ∑ t : Fin 4, (1 / 4 : ℝ) *
            fC (tacticUpdate i (outgoingUpdate i x b) t) := by
        simpa only [fresh_incomingWeight] using
          incoming_density_expectation i freshWeight freshWeight_sum
            (fun x => ∑ b : Fin 3, (1 / 3 : ℝ) * ∑ t : Fin 4, (1 / 4 : ℝ) *
              fC (tacticUpdate i (outgoingUpdate i x b) t))
      _ = ∑ x, density freshWeight x * ∑ t : Fin 4, (1 / 4 : ℝ) * fC (tacticUpdate i x t) := by
        simpa only [fresh_outgoingWeight] using
          outgoing_density_expectation i freshWeight freshWeight_sum
            (fun x => ∑ t : Fin 4, (1 / 4 : ℝ) * fC (tacticUpdate i x t))
      _ = _ := by simpa only [fresh_tacticWeight] using
        tactic_density_expectation i freshWeight freshWeight_sum fC
  calc
    _ = ∑ x, density freshWeight x *
        ∑ a : Fin 3, (1 / 3 : ℝ) * ∑ b : Fin 3, (1 / 3 : ℝ) *
          ∑ t : Fin 4, (1 / 4 : ℝ) * fC (tacticUpdate i (outgoingUpdate i (incomingUpdate i x a) b) t) := by
      simp_rw [hinitial, drawAverage_nested, hreplace]
      exact (coordinateEquiv n).sum_comp (fun x => density freshWeight x *
        ∑ a : Fin 3, (1 / 3 : ℝ) * ∑ b : Fin 3, (1 / 3 : ℝ) *
          ∑ t : Fin 4, (1 / 4 : ℝ) * fC (tacticUpdate i (outgoingUpdate i (incomingUpdate i x a) b) t))
    _ = ∑ x, density freshWeight x * fC x := hc
    _ = _ := by
      have h := (coordinateEquiv n).sum_comp (fun x => density freshWeight x * fC x)
      simpa only [fC, coordinateEquiv, Equiv.coe_fn_mk, fromCoords_toCoords, ← hinitial] using h.symm

def failedIndicator {n : ℕ} (s : ChainState n) (i : Fin n) : ℝ :=
  if passes s i then 0 else 1

theorem refreshed_failure_average {n : ℕ} (hn : 2 ≤ n) (s : ChainState n) (i : Fin n) :
    drawAverage (fun u => failedIndicator (replace s i u) i) =
      if i.val = 0 ∨ i.val + 1 = n then 1 / 6 else 5 / 12 := by
  by_cases hfirst : i.val = 0
  · have hinter : i.val + 1 < n := by omega
    have hp (u : Draw) : passes (replace s i u) i = MTChainProof.bridgePass 2 u.2.1 u.2.2 := by
      simp only [passes, hfirst, value_zero, replace_tactic_same]
      simpa only [hfirst] using congrArg
        (fun a => MTChainProof.bridgePass 2 a u.2.2) (replace_outgoing hn s i u hinter)
    simp_rw [failedIndicator, hp]
    norm_num [drawAverage, Fintype.sum_prod_type, Fin.sum_univ_succ, MTChainProof.bridgePass, hfirst]
  · have hip : 0 < i.val := by omega
    by_cases hlast : i.val + 1 = n
    · have hp (u : Draw) : passes (replace s i u) i = MTChainProof.bridgePass u.1 0 u.2.2 := by
        simp only [passes, replace_incoming hn s i u hip, hlast,
          value_right (by omega : 0 < n), replace_tactic_same]
      simp_rw [failedIndicator, hp]
      norm_num [drawAverage, Fintype.sum_prod_type, Fin.sum_univ_succ, MTChainProof.bridgePass, hlast]
    · have hinter : i.val + 1 < n := by omega
      have hp (u : Draw) : passes (replace s i u) i = MTChainProof.bridgePass u.1 u.2.1 u.2.2 := by
        simp only [passes, replace_incoming hn s i u hip,
          replace_outgoing hn s i u hinter, replace_tactic_same]
      simp_rw [failedIndicator, hp]
      norm_num [drawAverage, Fintype.sum_prod_type, Fin.sum_univ_succ,
        MTChainProof.bridgePass, hfirst, hlast]

theorem initial_failure_probability {n : ℕ} (hn : 2 ≤ n) (i : Fin n) :
    (∑ s : ChainState n, initialFull s * failedIndicator s i) =
      if i.val = 0 ∨ i.val + 1 = n then 1 / 6 else 5 / 12 := by
  rw [← uniform_fixed_refresh i (fun s => failedIndicator s i)]
  simp_rw [refreshed_failure_average hn]
  rw [← Finset.sum_mul, initialFull_sum n, one_mul]

theorem bad_card_eq_sum_indicator {n : ℕ} (s : ChainState n) :
    ((badIndices s).card : ℝ) = ∑ i : Fin n, failedIndicator s i := by
  classical
  rw [badIndices, Finset.card_filter]
  simp only [Nat.cast_sum, Nat.cast_ite, Nat.cast_one, Nat.cast_zero, failedIndicator]
  apply Finset.sum_congr rfl
  intro i _
  cases h : passes s i <;> simp

theorem initial_bad_moment {n : ℕ} (hn : 2 ≤ n) :
    (∑ s : ChainState n, initialFull s * ((badIndices s).card : ℝ)) =
      (5 * (n : ℝ) - 6) / 12 := by
  classical
  simp_rw [bad_card_eq_sum_indicator, Finset.mul_sum]
  rw [Finset.sum_comm]
  simp_rw [initial_failure_probability hn]
  have hcount : (Finset.univ.filter (fun i : Fin n => i.val = 0 ∨ i.val + 1 = n)).card = 2 := by
    have heq : Finset.univ.filter (fun i : Fin n => i.val = 0 ∨ i.val + 1 = n) =
        {(⟨0, by omega⟩ : Fin n), ⟨n - 1, by omega⟩} := by
      ext i
      simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_insert,
        Finset.mem_singleton, Fin.ext_iff]
      omega
    rw [heq, Finset.card_pair (by
      intro he
      have hv := congrArg Fin.val he
      change 0 = n - 1 at hv
      omega)]
  have hsum : (∑ i : Fin n,
      if i.val = 0 ∨ i.val + 1 = n then (1 / 6 : ℝ) else 5 / 12) =
      (2 : ℝ) * (1 / 6) + ((n : ℝ) - 2) * (5 / 12) := by
    rw [Finset.sum_ite]
    have hnotcount : (Finset.univ.filter
        (fun i : Fin n => ¬(i.val = 0 ∨ i.val + 1 = n))).card = n - 2 := by
      rw [Finset.filter_not, Finset.card_sdiff_of_subset (Finset.filter_subset _ _), hcount]
      simp
    simp only [Finset.sum_const, nsmul_eq_mul, hcount, hnotcount]
    rw [Nat.cast_sub hn]
    norm_num
  rw [hsum]
  ring

end MTChainFormal.Tightness
