module

public import ActualScan
public import TailLaw

@[expose] public section

set_option autoImplicit false

namespace MTChainFormal.Tightness.UniformScan

open scoped BigOperators
open TailScan ActualScan

/-- Ignore beneficial future barriers and charge a uniform bound at failure. -/
noncomputable def payoff : (m : ℕ) → Fin 3 → ℝ → Word m → Fin 4 → ℝ
  | 0, _, d, _, _ => 35 * d + 33
  | m + 1, incoming, d, word, last =>
      if MTChainProof.bridgePass incoming (word 0).1 (word 0).2 then
        payoff m (word 0).1 (d + 1) (Fin.tail word) last
      else 35 * d + 33

/-- The same envelope can pay for an earlier failure as well as a forward scan. -/
theorem entry_le_payoff (m : ℕ) (incoming : Fin 3) (d : ℝ) (word : Word m) (last : Fin 4) :
    35 * d + 33 ≤ payoff m incoming d word last := by
  induction m generalizing incoming d with
  | zero => exact le_refl _
  | succ m ih =>
      unfold payoff
      split_ifs
      · have hnext := ih (word 0).1 (d + 1) (Fin.tail word)
        linarith
      · exact le_refl _

theorem average_mono {m : ℕ} {f g : Word m → Fin 4 → ℝ}
    (h : ∀ w last, f w last ≤ g w last) : average m f ≤ average m g := by
  unfold average
  apply div_le_div_of_nonneg_right _ (by positivity)
  apply Finset.sum_le_sum
  intro w _
  exact Finset.sum_le_sum (fun last _ => h w last)

/-- Among twelve threshold/profile letters, at most ten pass for any input. -/
theorem passing_letter_count (incoming : Fin 3) :
    (∑ a : Letter, if MTChainProof.bridgePass incoming a.1 a.2 then (1 : ℕ) else 0) ≤ 10 := by
  fin_cases incoming <;> decide

/-- The worst passing probability 5/6 closes a length-independent envelope. -/
theorem head_envelope (incoming : Fin 3) (d : ℝ) :
    (∑ a : Letter, if MTChainProof.bridgePass incoming a.1 a.2
      then 35 * (d + 1) + 208 else 35 * d + 33) / 12 ≤ 35 * d + 208 := by
  fin_cases incoming <;>
    norm_num [Fintype.sum_prod_type, Fin.sum_univ_succ, MTChainProof.bridgePass] <;> linarith

theorem average_payoff_le (m : ℕ) (incoming : Fin 3) (d : ℝ) (hd : 0 ≤ d) :
    average m (payoff m incoming d) ≤ 35 * d + 208 := by
  induction m generalizing incoming d with
  | zero =>
      change average 0 (fun _ _ => 35 * d + 33) ≤ 35 * d + 208
      rw [average_const]
      linarith
  | succ m ih =>
      rw [average_succ]
      calc
        _ ≤ (∑ a : Letter, if MTChainProof.bridgePass incoming a.1 a.2
            then 35 * (d + 1) + 208 else 35 * d + 33) / 12 := by
          apply div_le_div_of_nonneg_right _ (by norm_num)
          apply Finset.sum_le_sum
          intro a _
          by_cases hp : MTChainProof.bridgePass incoming a.1 a.2 = true
          · simpa only [payoff, Fin.cons_zero, hp, Bool.true_eq, ↓reduceIte,
              Fin.tail_cons] using ih a.1 (d + 1) (by linarith)
          · have hf : MTChainProof.bridgePass incoming a.1 a.2 = false :=
              Bool.eq_false_iff.mpr hp
            simp only [payoff, Fin.cons_zero, hf, Bool.false_eq_true, ↓reduceIte]
            exact le_of_eq (average_const m _)
        _ ≤ 35 * d + 208 := head_envelope incoming d

/-- At the first failure, the actual local potential is bounded by its
    one-based index relative to any smaller persistent anchor. -/
theorem localPotential_le_index {n : ℕ} (s : ChainState n) (i : Fin n)
    (hi : firstFailure s = some i) (b : ℕ) (hb : b ≤ barrierHeight s)
    (d : ℝ) (hline : d + (b : ℝ) = ((i.val + 1 : ℕ) : ℝ)) :
    localPotential s ≤ 35 * d + 33 := by
  have hid := retainedDistance_identity s i hi
  rw [failureIndex_of_selected s i hi] at hid
  have heq : (retainedDistance s : ℝ) + (zeroRun s : ℝ) + (barrierHeight s : ℝ) =
      ((i.val + 1 : ℕ) : ℝ) := by exact_mod_cast hid
  have hbcast : (b : ℝ) ≤ (barrierHeight s : ℝ) := by exact_mod_cast hb
  have hr : (0 : ℝ) ≤ (zeroRun s : ℝ) := Nat.cast_nonneg _
  have hz := zeroIndicator_le_one s
  unfold localPotential PotentialAlgebra.localValue
  linarith

/-- A pointwise comparison with the actual finite forward scan, including
    incoming value 2 and the final fixed zero endpoint. -/
theorem actual_scan_le {n : ℕ} (hn : 0 < n) (s : ChainState n)
    (b : ℕ) (hb : b ≤ barrierHeight s) :
    ∀ (m k : ℕ) (h : k + m + 1 = n), PrefixHolds s k →
      ∀ (d : ℝ), 0 ≤ d → d + (b : ℝ) = ((k + 1 : ℕ) : ℝ) →
      localPotential s ≤ payoff m (value s k) d (lettersFrom s k m h) (lastTactic s hn) := by
  intro m
  induction m with
  | zero =>
      intro k h hp d hd hline
      have hk : k + 1 = n := by omega
      have hkn : k < n := by omega
      let i : Fin n := ⟨k, hkn⟩
      by_cases hpcur : passes s i = true
      · have hall : PrefixHolds s n := by
          simpa only [hk] using prefix_extend s k hkn hp hpcur
        have hg := prefix_all_good s hall
        rw [localPotential_of_good s hg]
        change 0 ≤ 35 * d + 33
        linarith
      · have hf : passes s i = false := Bool.eq_false_iff.mpr hpcur
        have hi := firstFailure_of_failed_prefix s i hf hp
        exact localPotential_le_index s i hi b hb d (by simpa only [i] using hline)
  | succ m ih =>
      intro k h hp d hd hline
      have hkn : k < n := by omega
      let i : Fin n := ⟨k, hkn⟩
      have hhead := lettersFrom_head s k m h
      have htail := lettersFrom_tail s k m h
      by_cases hpcur : passes s i = true
      · have hbridge : MTChainProof.bridgePass (value s k) (value s (k + 1))
            (s.tactic ⟨k, hkn⟩) = true := hpcur
        have hpnext := prefix_extend s k hkn hp hpcur
        have hnext := ih (k + 1) (by omega) hpnext (d + 1) (by linarith)
          (by push_cast at hline ⊢; linarith)
        simpa only [payoff, hhead, Prod.fst, Prod.snd, hbridge, Bool.true_eq, ↓reduceIte, htail]
          using hnext
      · have hf : passes s i = false := Bool.eq_false_iff.mpr hpcur
        have hbridge : MTChainProof.bridgePass (value s k) (value s (k + 1))
            (s.tactic ⟨k, hkn⟩) = false := hf
        have hi := firstFailure_of_failed_prefix s i hf hp
        simpa only [payoff, hhead, Prod.fst, Prod.snd, hbridge, Bool.false_eq_true, ↓reduceIte] using
          localPotential_le_index s i hi b hb d (by simpa only [i] using hline)


/-- The uniform envelope holds under the already proved actual completion law. -/
theorem completion_payoff_le {n : ℕ} (q : Filtering.PrefixDatum n) (m : ℕ)
    (hm : q.1.val + 1 + m + 1 = n) (incoming : Fin 3) (d : ℝ) (hd : 0 ≤ d) :
    (∑ s : ChainState n, Filtering.rawCompletion q s *
      payoff m incoming d (lettersFrom s (q.1.val + 1) m hm)
        (lastTactic s (by omega))) ≤ 35 * d + 208 := by
  rw [TailLaw.completion_tail_average]
  exact average_payoff_le m incoming d hd

/-- Replacing the selected footprint leaves this strict suffix unchanged. -/
theorem completion_replaced_payoff_le {n : ℕ} (q : Filtering.PrefixDatum n) (m : ℕ)
    (hm : q.1.val + 1 + m + 1 = n) (u : Draw) (incoming : Fin 3) (d : ℝ) (hd : 0 ≤ d) :
    (∑ s : ChainState n, Filtering.rawCompletion q s *
      payoff m incoming d (lettersFrom (replace s q.1 u) (q.1.val + 1) m hm)
        (lastTactic (replace s q.1 u) (by omega))) ≤ 35 * d + 208 := by
  have hlast (s : ChainState n) := TailLaw.lastTactic_replace s q.1 u m hm
  simp only [TailLaw.lettersFrom_replace, hlast]
  exact completion_payoff_le q m hm incoming d hd

end MTChainFormal.Tightness.UniformScan
