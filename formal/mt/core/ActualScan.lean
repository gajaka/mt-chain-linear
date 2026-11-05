import Features
import TailScan

set_option autoImplicit false

namespace MTChainFormal.ActualScan

open scoped BigOperators
open PotentialAlgebra TailScan

def prefixZeroCount {n : ℕ} (s : ChainState n) (cut : ℕ) : ℕ :=
  ((Finset.range cut).filter (fun j => value s j = 0)).card

theorem prefixZeroCount_succ {n : ℕ} (s : ChainState n) (cut : ℕ) :
    prefixZeroCount s (cut + 1) =
      prefixZeroCount s cut + if value s cut = 0 then 1 else 0 := by
  by_cases hz : value s cut = 0
  · simp [prefixZeroCount, Finset.range_add_one, Finset.filter_insert, hz,
      Finset.card_insert_of_notMem, Nat.add_comm]
  · simp [prefixZeroCount, Finset.range_add_one, Finset.filter_insert, hz]

theorem prefix_extend {n : ℕ} (s : ChainState n) (k : ℕ) (hk : k < n)
    (hp : PrefixHolds s k) (hpass : passes s ⟨k, hk⟩ = true) :
    PrefixHolds s (k + 1) := by
  intro i hi
  by_cases hik : i.val < k
  · exact hp i hik
  · have hiv : i.val = k := by omega
    have heq : i = (⟨k, hk⟩ : Fin n) := Fin.ext hiv
    simpa [heq] using hpass

theorem prefix_all_good {n : ℕ} (s : ChainState n) (hp : PrefixHolds s n) :
    firstFailure s = none := by
  apply (no_failure_iff s).mpr
  intro i
  exact hp i i.isLt

theorem zeroCount_of_incoming_one {n : ℕ} (s : ChainState n) (k : ℕ)
    (hk : k < n) (hp : PrefixHolds s k) (hv : value s k = 1) :
    prefixZeroCount s (k + 1) = 0 := by
  have he : ((Finset.range (k + 1)).filter (fun j => value s j = 0)) = ∅ := by
    apply Finset.eq_empty_iff_forall_notMem.mpr
    intro j hj
    obtain ⟨hjrange, hjzero⟩ := Finset.mem_filter.mp hj
    have hjk : j ≤ k := by have := Finset.mem_range.mp hjrange; omega
    have hmono := prefix_value_antitone s k hp (by omega) j k hjk le_rfl
    rw [hv, hjzero] at hmono
    norm_num at hmono
  simp [prefixZeroCount, he]

theorem retainedDistance_identity {n : ℕ} (s : ChainState n) (i : Fin n)
    (hi : firstFailure s = some i) :
    retainedDistance s + zeroRun s + barrierHeight s = failureIndex s := by
  have hbar := barrierHeight_le_retained_prefix s i hi
  have hzero := zeroRun_le_failureIndex s
  simp only [retainedDistance, hi, Option.some_ne_none, ↓reduceIte]
  omega

theorem zeroRun_of_selected {n : ℕ} (s : ChainState n) (i : Fin n)
    (hi : firstFailure s = some i) : zeroRun s = prefixZeroCount s (i.val + 1) := by
  simp [zeroRun, prefixZeroSites, prefixZeroCount, hi, failureIndex]

theorem distance_le_anchor {n : ℕ} (s : ChainState n) (i : Fin n)
    (hi : firstFailure s = some i) (b r : ℕ) (d : ℝ)
    (hb : b ≤ barrierHeight s) (hr : zeroRun s = r)
    (hd : d + (r : ℝ) + (b : ℝ) = (i.val + 1 : ℕ)) :
    (retainedDistance s : ℝ) ≤ d := by
  have hid := retainedDistance_identity s i hi
  rw [failureIndex_of_selected s i hi, hr] at hid
  have hreal : (retainedDistance s : ℝ) + (r : ℝ) + (barrierHeight s : ℝ) =
      ((i.val + 1 : ℕ) : ℝ) := by exact_mod_cast hid
  have hbcast : (b : ℝ) ≤ (barrierHeight s : ℝ) := by exact_mod_cast hb
  linarith

theorem localPotential_le_zero {n : ℕ} (s : ChainState n) (i : Fin n)
    (hi : firstFailure s = some i) (hz : value s i.val = 0)
    (b r : ℕ) (d : ℝ) (hb : b ≤ barrierHeight s) (hr : zeroRun s = r)
    (hd : d + (r : ℝ) + (b : ℝ) = ((i.val + 1 : ℕ) : ℝ)) :
    localPotential s ≤ localValue d (r : ℝ) 1 := by
  have hdist := distance_le_anchor s i hi b r d hb hr hd
  have hpos : 0 < zeroRun s := (zeroRun_pos_iff s i hi).mpr hz
  have hne : zeroRun s ≠ 0 := by omega
  simp only [localPotential, zeroIndicator, hne, ↓reduceIte, localValue]
  rw [hr]
  linarith

theorem localPotential_le_one {n : ℕ} (s : ChainState n) (i : Fin n)
    (hi : firstFailure s = some i) (hz : value s i.val = 1)
    (b : ℕ) (d : ℝ) (hb : b ≤ barrierHeight s)
    (hd : d + (b : ℝ) = ((i.val + 1 : ℕ) : ℝ)) :
    localPotential s ≤ localValue d 0 0 := by
  have hzero : zeroRun s = 0 := by
    have hiff := zeroRun_pos_iff s i hi
    by_contra hne
    have hpos : 0 < zeroRun s := by omega
    have h0 := hiff.mp hpos
    rw [hz] at h0
    cases h0
  have hdist := distance_le_anchor s i hi b 0 d hb hzero (by simpa using hd)
  simp only [localPotential, zeroIndicator, hzero, ↓reduceIte, localValue]
  norm_num
  linarith

def lettersFrom {n : ℕ} (s : ChainState n) (k m : ℕ) (h : k + m + 1 = n) : Word m :=
  fun j => (value s (k + j.val + 1), s.tactic ⟨k + j.val, by omega⟩)

def lastTactic {n : ℕ} (s : ChainState n) (hn : 0 < n) : Fin 4 :=
  s.tactic ⟨n - 1, by omega⟩

theorem lettersFrom_head {n : ℕ} (s : ChainState n) (k m : ℕ)
    (h : k + (m + 1) + 1 = n) :
    lettersFrom s k (m + 1) h 0 =
      (value s (k + 1), s.tactic ⟨k, by omega⟩) := by
  simp [lettersFrom]

theorem lettersFrom_tail {n : ℕ} (s : ChainState n) (k m : ℕ)
    (h : k + (m + 1) + 1 = n) :
    Fin.tail (lettersFrom s k (m + 1) h) =
      lettersFrom s (k + 1) m (by omega) := by
  funext j
  simp only [Fin.tail, lettersFrom, Fin.val_succ]
  have heq' : k + (j.val + 1) = k + 1 + j.val := by omega
  simp only [heq']

theorem bridge_zero_table : ∀ (v : Fin 3) (t : Fin 4),
    MTChainProof.bridgePass 0 v t = decide (v = 0) := by decide

theorem bridge_equal_table : ∀ (v : Fin 3) (t : Fin 4),
    MTChainProof.bridgePass v v t = true := by decide

theorem bridge_one_zero_table : ∀ (t : Fin 4),
    MTChainProof.bridgePass 1 0 t = (if t = 1 then false else true) := by decide

theorem bridge_one_two_table : ∀ (t : Fin 4),
    MTChainProof.bridgePass 1 2 t = false := by decide

theorem lastTactic_at {n : ℕ} (s : ChainState n) (hn : 0 < n) (k : ℕ)
    (hk : k + 1 = n) : lastTactic s hn = s.tactic ⟨k, by omega⟩ := by
  unfold lastTactic
  congr 1
  apply Fin.ext
  change n - 1 = k
  omega

theorem actual_zero_scan_le {n : ℕ} (hn : 0 < n) (s : ChainState n)
    (b : ℕ) (hb : b ≤ barrierHeight s) :
    ∀ (m k : ℕ) (h : k + m + 1 = n),
      PrefixHolds s k → value s k = 0 →
      ∀ (r : ℕ), prefixZeroCount s (k + 1) = r →
      ∀ (d : ℝ), 0 ≤ d → d + (r : ℝ) + (b : ℝ) = ((k + 1 : ℕ) : ℝ) →
      localPotential s ≤ zeroPayoff m d (r : ℝ) (lettersFrom s k m h) (lastTactic s hn) := by
  intro m
  induction m with
  | zero =>
      intro k h hp hv r hr d hd hlin
      have hk : k + 1 = n := by omega
      have hkn : k < n := by omega
      have hout : value s (k + 1) = 0 := by rw [hk]; exact value_right hn s
      have hpass : passes s ⟨k, hkn⟩ = true := by
        simp only [passes, hv, hout]
        exact bridge_equal_table _ _
      have hall : PrefixHolds s n := by
        simpa [hk] using prefix_extend s k hkn hp hpass
      have hg := prefix_all_good s hall
      simp [localPotential_of_good s hg, zeroPayoff]
  | succ m ih =>
      intro k h hp hv r hr d hd hlin
      have hkn : k < n := by omega
      let i : Fin n := ⟨k, hkn⟩
      have hhead := lettersFrom_head s k m h
      have htail := lettersFrom_tail s k m h
      by_cases hout : value s (k + 1) = 0
      · have hpass : passes s i = true := by
          simp only [passes, i, hv, hout]
          exact bridge_equal_table _ _
        have hpnext := prefix_extend s k hkn hp hpass
        have hrnext : prefixZeroCount s (k + 1 + 1) = r + 1 := by
          rw [prefixZeroCount_succ, hout, hr]
          simp
        have hnext := ih (k + 1) (by omega) hpnext hout (r + 1) hrnext d hd
          (by push_cast at hlin ⊢; linarith)
        simpa only [zeroPayoff, hhead, Prod.fst, hout, ↓reduceIte, htail,
          Nat.cast_add, Nat.cast_one] using hnext
      · have hfail : passes s i = false := by
          simp only [passes, i, hv, bridge_zero_table]
          simp [hout]
        have hi := firstFailure_of_failed_prefix s i hfail hp
        have hrun : zeroRun s = r := by
          rw [zeroRun_of_selected s i hi]
          simpa [i] using hr
        have hcost := localPotential_le_zero s i hi (by simpa [i] using hv)
          b r d hb hrun (by simpa [i] using hlin)
        simpa only [zeroPayoff, hhead, Prod.fst, hout, ↓reduceIte] using hcost

theorem actual_one_scan_le {n : ℕ} (hn : 0 < n) (s : ChainState n)
    (b : ℕ) (hb : b ≤ barrierHeight s) :
    ∀ (m k : ℕ) (h : k + m + 1 = n),
      PrefixHolds s k → value s k = 1 →
      ∀ (d : ℝ), 0 ≤ d → d + (b : ℝ) = ((k + 1 : ℕ) : ℝ) →
      localPotential s ≤ onePayoff m d (lettersFrom s k m h) (lastTactic s hn) := by
  intro m
  induction m with
  | zero =>
      intro k h hp hv d hd hlin
      have hk : k + 1 = n := by omega
      have hkn : k < n := by omega
      let i : Fin n := ⟨k, hkn⟩
      have hout : value s (k + 1) = 0 := by rw [hk]; exact value_right hn s
      have hlast := lastTactic_at s hn k hk
      by_cases hw : lastTactic s hn = 1
      · have hweak : s.tactic i = 1 := by simpa [i, hlast] using hw
        have hfail : passes s i = false := by
          simp [passes, i, hv, hout, bridge_one_zero_table, hweak]
        have hi := firstFailure_of_failed_prefix s i hfail hp
        have hcost := localPotential_le_one s i hi (by simpa [i] using hv)
          b d hb (by simpa [i] using hlin)
        simpa [onePayoff, hw] using hcost
      · have hweak : s.tactic i ≠ 1 := by simpa [i, hlast] using hw
        have hpass : passes s i = true := by
          simp [passes, i, hv, hout, bridge_one_zero_table, hweak]
        have hall : PrefixHolds s n := by
          simpa [hk] using prefix_extend s k hkn hp hpass
        have hg := prefix_all_good s hall
        simp [localPotential_of_good s hg, onePayoff, hw]
  | succ m ih =>
      intro k h hp hv d hd hlin
      have hkn : k < n := by omega
      let i : Fin n := ⟨k, hkn⟩
      have hhead := lettersFrom_head s k m h
      have htail := lettersFrom_tail s k m h
      by_cases hout0 : value s (k + 1) = 0
      · by_cases hw : s.tactic i = 1
        · have hwraw : s.tactic ⟨k, hkn⟩ = 1 := hw
          have hfail : passes s i = false := by
            simp [passes, i, hv, hout0, bridge_one_zero_table, hw]
          have hi := firstFailure_of_failed_prefix s i hfail hp
          have hcost := localPotential_le_one s i hi (by simpa [i] using hv)
            b d hb (by simpa [i] using hlin)
          simpa only [onePayoff, hhead, Prod.fst, Prod.snd, hout0, hwraw,
            ↓reduceIte] using hcost
        · have hwraw : s.tactic ⟨k, hkn⟩ ≠ 1 := hw
          have hpass : passes s i = true := by
            simp [passes, i, hv, hout0, bridge_one_zero_table, hw]
          have hpnext := prefix_extend s k hkn hp hpass
          have hrnext : prefixZeroCount s (k + 1 + 1) = 1 := by
            rw [prefixZeroCount_succ, hout0, zeroCount_of_incoming_one s k hkn hp hv]
            simp
          have hnext := actual_zero_scan_le hn s b hb m (k + 1) (by omega)
            hpnext hout0 1 hrnext d hd (by push_cast at hlin ⊢; linarith)
          simpa only [onePayoff, hhead, Prod.fst, Prod.snd, hout0, hwraw,
            ↓reduceIte, htail, Nat.cast_one] using hnext
      · by_cases hout1 : value s (k + 1) = 1
        · have hpass : passes s i = true := by
            simp only [passes, i, hv, hout1]
            exact bridge_equal_table _ _
          have hpnext := prefix_extend s k hkn hp hpass
          have hnext := ih (k + 1) (by omega) hpnext hout1 (d + 1) (by linarith)
            (by push_cast at hlin ⊢; linarith)
          simpa [onePayoff, hhead, hout0, hout1, htail] using hnext
        · have hcases : ∀ v : Fin 3, v = 0 ∨ v = 1 ∨ v = 2 := by decide
          have hout2 : value s (k + 1) = 2 := by
            rcases hcases (value s (k + 1)) with h0 | h1 | h2
            · exact False.elim (hout0 h0)
            · exact False.elim (hout1 h1)
            · exact h2
          have hfail : passes s i = false := by
            simp only [passes, i, hv, hout2]
            exact bridge_one_two_table _
          have hi := firstFailure_of_failed_prefix s i hfail hp
          have hcost := localPotential_le_one s i hi (by simpa [i] using hv)
            b d hb (by simpa [i] using hlin)
          simpa only [onePayoff, hhead, Prod.fst, hout0, hout1, ↓reduceIte] using hcost

end MTChainFormal.ActualScan
