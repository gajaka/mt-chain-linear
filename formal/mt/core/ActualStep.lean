module

public import ActualScan
public import ScanBounds

@[expose] public section

set_option autoImplicit false

namespace MTChainFormal.ActualStep

open scoped BigOperators
open PotentialAlgebra TailScan ActualScan

noncomputable def deepZeroPayoff (m : ℕ) (d r : ℝ) (w : Word m) (last : Fin 4)
    (u v : Fin 3) (_t : Fin 4) : ℝ :=
  if u = 0 then
    if v = 0 then zeroPayoff m d (r + 1) w last else localValue d r 1
  else localValue d (r - 1) 1

noncomputable def middlePayoff (m : ℕ) (d : ℝ) (w : Word m) (last : Fin 4)
    (v : Fin 3) (t : Fin 4) : ℝ :=
  if v = 0 then
    if t = 1 then localValue d 0 0 else zeroPayoff m d 1 w last
  else if v = 1 then onePayoff m (d + 1) w last else localValue d 0 0

noncomputable def strongPayoff (m : ℕ) (d : ℝ) (w : Word m) (last : Fin 4)
    (u v : Fin 3) (t : Fin 4) : ℝ :=
  if u = 0 then
    if v = 0 then zeroPayoff m (d - 1) 2 w last else localValue (d - 1) 1 1
  else if u = 1 then middlePayoff m d w last v t else localValue (d - 1) 0 0

noncomputable def weakPayoff (m : ℕ) (d : ℝ) (w : Word m) (last : Fin 4)
    (u v : Fin 3) (t : Fin 4) : ℝ :=
  if u = 1 then middlePayoff m d w last v t else localValue (d - 1) 0 0

theorem zeroCount_replace_before {n : ℕ} (hn : 2 ≤ n) (s : ChainState n)
    (i : Fin n) (u : Draw) (cut : ℕ) (hcut : cut ≤ i.val) :
    prefixZeroCount (replace s i u) cut = prefixZeroCount s cut := by
  unfold prefixZeroCount
  congr 1
  ext j
  by_cases hj : j < cut
  · simp only [Finset.mem_filter, Finset.mem_range, hj, true_and]
    rw [replace_value_strict_before hn s i u j (by omega)]
  · simp [Finset.mem_filter, Finset.mem_range, hj]

theorem zeroCount_replace_incoming {n : ℕ} (hn : 2 ≤ n) (s : ChainState n)
    (i : Fin n) (u : Draw) (hip : 0 < i.val) :
    prefixZeroCount (replace s i u) (i.val + 1) =
      prefixZeroCount s i.val + if u.1 = 0 then 1 else 0 := by
  rw [prefixZeroCount_succ, zeroCount_replace_before hn s i u i.val le_rfl,
    replace_incoming hn s i u hip]

theorem zeroCount_replace_pair {n : ℕ} (hn : 2 ≤ n) (s : ChainState n)
    (i : Fin n) (u : Draw) (hip : 0 < i.val) (hinter : i.val + 1 < n) :
    prefixZeroCount (replace s i u) (i.val + 1 + 1) =
      prefixZeroCount s i.val + (if u.1 = 0 then 1 else 0) +
        if u.2.1 = 0 then 1 else 0 := by
  rw [prefixZeroCount_succ, zeroCount_replace_incoming hn s i u hip,
    replace_outgoing hn s i u hinter]

theorem prefix_replace_before_left {n : ℕ} (hn : 2 ≤ n) (s : ChainState n)
    (i : Fin n) (u : Draw) (hi : firstFailure s = some i) :
    PrefixHolds (replace s i u) (i.val - 1) := by
  intro j hj
  rw [replace_pass_unchanged hn s i j u (Or.inl (by omega))]
  exact selected_prefix s i hi j (by omega)

theorem prefix_replace_before_selected {n : ℕ} (hn : 2 ≤ n) (s : ChainState n)
    (i : Fin n) (u : Draw) (hi : firstFailure s = some i) (hip : 0 < i.val)
    (hprev : passes (replace s i u) ⟨i.val - 1, by omega⟩ = true) :
    PrefixHolds (replace s i u) i.val := by
  intro j hj
  by_cases hadj : j.val + 1 = i.val
  · have hval : j.val = i.val - 1 := by omega
    have heq : j = (⟨i.val - 1, by omega⟩ : Fin n) := Fin.ext hval
    simpa [heq] using hprev
  · rw [replace_pass_unchanged hn s i j u (Or.inl (by omega))]
    exact selected_prefix s i hi j hj

theorem firstFailure_replace_left {n : ℕ} (hn : 2 ≤ n) (s : ChainState n)
    (i : Fin n) (u : Draw) (hi : firstFailure s = some i) (hip : 0 < i.val)
    (hprev : passes (replace s i u) ⟨i.val - 1, by omega⟩ = false) :
    firstFailure (replace s i u) = some ⟨i.val - 1, by omega⟩ := by
  apply firstFailure_of_failed_prefix _ _ hprev
  exact prefix_replace_before_left hn s i u hi

theorem firstFailure_replace_same {n : ℕ} (hn : 2 ≤ n) (s : ChainState n)
    (i : Fin n) (u : Draw) (hi : firstFailure s = some i) (hip : 0 < i.val)
    (hprev : passes (replace s i u) ⟨i.val - 1, by omega⟩ = true)
    (hnow : passes (replace s i u) i = false) :
    firstFailure (replace s i u) = some i := by
  apply firstFailure_of_failed_prefix _ _ hnow
  exact prefix_replace_before_selected hn s i u hi hip hprev

theorem prefix_after_replace {n : ℕ} (hn : 2 ≤ n) (s : ChainState n)
    (i : Fin n) (u : Draw) (hi : firstFailure s = some i) (hip : 0 < i.val)
    (hprev : passes (replace s i u) ⟨i.val - 1, by omega⟩ = true)
    (hnow : passes (replace s i u) i = true) :
    PrefixHolds (replace s i u) (i.val + 1) := by
  apply prefix_extend _ i.val i.isLt
  · exact prefix_replace_before_selected hn s i u hi hip hprev
  · exact hnow

theorem replace_previous_pass {n : ℕ} (hn : 2 ≤ n) (s : ChainState n)
    (i : Fin n) (u : Draw) (hip : 0 < i.val) :
    passes (replace s i u) ⟨i.val - 1, by omega⟩ =
      MTChainProof.bridgePass (value s (i.val - 1)) u.1
        (s.tactic ⟨i.val - 1, by omega⟩) := by
  have heq : i.val - 1 + 1 = i.val := by omega
  have hne : (⟨i.val - 1, by omega⟩ : Fin n) ≠ i := by
    intro h
    have := congrArg Fin.val h
    change i.val - 1 = i.val at this
    omega
  simp only [passes, heq]
  rw [replace_value_strict_before hn s i u (i.val - 1) (by omega),
    replace_incoming hn s i u hip, replace_tactic_other s i _ u hne]

theorem replace_current_pass {n : ℕ} (hn : 2 ≤ n) (s : ChainState n)
    (i : Fin n) (u : Draw) (hip : 0 < i.val) (hinter : i.val + 1 < n) :
    passes (replace s i u) i = MTChainProof.bridgePass u.1 u.2.1 u.2.2 := by
  simp only [passes]
  rw [replace_incoming hn s i u hip, replace_outgoing hn s i u hinter,
    replace_tactic_same]

theorem replace_value_strict_after {n : ℕ} (hn : 2 ≤ n) (s : ChainState n)
    (i : Fin n) (u : Draw) (k : ℕ) (hk : i.val + 1 < k) (hkn : k ≤ n) :
    value (replace s i u) k = value s k := by
  rw [replace_value hn s i u k hkn]
  have h0 : k ≠ 0 := by omega
  by_cases hlast : k = n
  · have hn0 : n ≠ 0 := by omega
    simp [hlast, hn0, value_right (by omega : 0 < n)]
  · have hi0 : k ≠ i.val := by omega
    have hi1 : k ≠ i.val + 1 := by omega
    simp [h0, hlast, hi0, hi1]

theorem lettersFrom_replace {n : ℕ} (hn : 2 ≤ n) (s : ChainState n)
    (i : Fin n) (u : Draw) (m : ℕ) (h : i.val + 1 + m + 1 = n) :
    lettersFrom (replace s i u) (i.val + 1) m h = lettersFrom s (i.val + 1) m h := by
  funext j
  dsimp only [lettersFrom]
  apply Prod.ext
  · exact replace_value_strict_after hn s i u (i.val + 1 + j.val + 1) (by omega) (by omega)
  · apply replace_tactic_other
    intro heq
    have hv := congrArg Fin.val heq
    change i.val + 1 + j.val = i.val at hv
    omega

theorem lastTactic_replace {n : ℕ} (hn : 2 ≤ n) (s : ChainState n)
    (i : Fin n) (u : Draw) (hinter : i.val + 1 < n) :
    lastTactic (replace s i u) (by omega) = lastTactic s (by omega) := by
  unfold lastTactic
  apply replace_tactic_other
  intro heq
  have hv := congrArg Fin.val heq
  change n - 1 = i.val at hv
  omega

theorem after_forward_zero_bound {n : ℕ} (hn : 2 ≤ n) (s : ChainState n)
    (i : Fin n) (u : Draw) (hi : firstFailure s = some i) (hip : 0 < i.val)
    (m : ℕ) (hm : i.val + 1 + m + 1 = n)
    (hprev : passes (replace s i u) ⟨i.val - 1, by omega⟩ = true)
    (hnow : passes (replace s i u) i = true) (hout : u.2.1 = 0)
    (b r : ℕ) (d : ℝ) (hb : b ≤ barrierHeight s)
    (hr : prefixZeroCount (replace s i u) (i.val + 1 + 1) = r)
    (hd : 0 ≤ d) (hlin : d + (r : ℝ) + (b : ℝ) = ((i.val + 1 + 1 : ℕ) : ℝ)) :
    localPotential (replace s i u) ≤ zeroPayoff m d (r : ℝ)
      (lettersFrom s (i.val + 1) m hm) (lastTactic s (by omega)) := by
  have hinter : i.val + 1 < n := by omega
  have hp := prefix_after_replace hn s i u hi hip hprev hnow
  have hv : value (replace s i u) (i.val + 1) = 0 := by
    rw [replace_outgoing hn s i u hinter, hout]
  have hbnew := le_trans hb (barrierHeight_mono_replace hn s i u hi)
  have hscan := actual_zero_scan_le (by omega : 0 < n) (replace s i u) b hbnew
    m (i.val + 1) hm hp hv r hr d hd hlin
  rw [lettersFrom_replace hn s i u m hm, lastTactic_replace hn s i u hinter] at hscan
  exact hscan

theorem after_forward_one_bound {n : ℕ} (hn : 2 ≤ n) (s : ChainState n)
    (i : Fin n) (u : Draw) (hi : firstFailure s = some i) (hip : 0 < i.val)
    (m : ℕ) (hm : i.val + 1 + m + 1 = n)
    (hprev : passes (replace s i u) ⟨i.val - 1, by omega⟩ = true)
    (hnow : passes (replace s i u) i = true) (hout : u.2.1 = 1)
    (b : ℕ) (d : ℝ) (hb : b ≤ barrierHeight s)
    (hd : 0 ≤ d) (hlin : d + (b : ℝ) = ((i.val + 1 + 1 : ℕ) : ℝ)) :
    localPotential (replace s i u) ≤ onePayoff m d
      (lettersFrom s (i.val + 1) m hm) (lastTactic s (by omega)) := by
  have hinter : i.val + 1 < n := by omega
  have hp := prefix_after_replace hn s i u hi hip hprev hnow
  have hv : value (replace s i u) (i.val + 1) = 1 := by
    rw [replace_outgoing hn s i u hinter, hout]
  have hbnew := le_trans hb (barrierHeight_mono_replace hn s i u hi)
  have hscan := actual_one_scan_le (by omega : 0 < n) (replace s i u) b hbnew
    m (i.val + 1) hm hp hv d hd hlin
  rw [lettersFrom_replace hn s i u m hm, lastTactic_replace hn s i u hinter] at hscan
  exact hscan

theorem after_stay_zero_bound {n : ℕ} (hn : 2 ≤ n) (s : ChainState n)
    (i : Fin n) (u : Draw) (hi : firstFailure s = some i) (hip : 0 < i.val)
    (hprev : passes (replace s i u) ⟨i.val - 1, by omega⟩ = true)
    (hnow : passes (replace s i u) i = false) (hin : u.1 = 0)
    (b r : ℕ) (d : ℝ) (hb : b ≤ barrierHeight s)
    (hr : prefixZeroCount (replace s i u) (i.val + 1) = r)
    (hlin : d + (r : ℝ) + (b : ℝ) = ((i.val + 1 : ℕ) : ℝ)) :
    localPotential (replace s i u) ≤ localValue d (r : ℝ) 1 := by
  have hfirst := firstFailure_replace_same hn s i u hi hip hprev hnow
  have hz : value (replace s i u) i.val = 0 := by rw [replace_incoming hn s i u hip, hin]
  have hrun : zeroRun (replace s i u) = r := by
    rw [zeroRun_of_selected _ i hfirst]
    exact hr
  exact localPotential_le_zero _ i hfirst hz b r d
    (le_trans hb (barrierHeight_mono_replace hn s i u hi)) hrun hlin

theorem after_stay_one_bound {n : ℕ} (hn : 2 ≤ n) (s : ChainState n)
    (i : Fin n) (u : Draw) (hi : firstFailure s = some i) (hip : 0 < i.val)
    (hprev : passes (replace s i u) ⟨i.val - 1, by omega⟩ = true)
    (hnow : passes (replace s i u) i = false) (hin : u.1 = 1)
    (b : ℕ) (d : ℝ) (hb : b ≤ barrierHeight s)
    (hlin : d + (b : ℝ) = ((i.val + 1 : ℕ) : ℝ)) :
    localPotential (replace s i u) ≤ localValue d 0 0 := by
  have hfirst := firstFailure_replace_same hn s i u hi hip hprev hnow
  have hz : value (replace s i u) i.val = 1 := by rw [replace_incoming hn s i u hip, hin]
  exact localPotential_le_one _ i hfirst hz b d
    (le_trans hb (barrierHeight_mono_replace hn s i u hi)) hlin

theorem after_back_one_bound {n : ℕ} (hn : 2 ≤ n) (s : ChainState n)
    (i : Fin n) (u : Draw) (hi : firstFailure s = some i) (hip : 0 < i.val)
    (hprev : passes (replace s i u) ⟨i.val - 1, by omega⟩ = false)
    (hv : value s (i.val - 1) = 1)
    (b : ℕ) (d : ℝ) (hb : b ≤ barrierHeight s)
    (hlin : d + (b : ℝ) = (i.val : ℝ)) :
    localPotential (replace s i u) ≤ localValue d 0 0 := by
  let j : Fin n := ⟨i.val - 1, by omega⟩
  have hfirst := firstFailure_replace_left hn s i u hi hip hprev
  have hz : value (replace s i u) j.val = 1 := by
    rw [replace_value_strict_before hn s i u j.val (by dsimp [j]; omega)]
    exact hv
  have hj : j.val + 1 = i.val := by dsimp [j]; omega
  exact localPotential_le_one _ j hfirst hz b d
    (le_trans hb (barrierHeight_mono_replace hn s i u hi)) (by rw [hj]; exact hlin)

theorem after_back_zero_bound {n : ℕ} (hn : 2 ≤ n) (s : ChainState n)
    (i : Fin n) (u : Draw) (hi : firstFailure s = some i) (hip : 0 < i.val)
    (hprev : passes (replace s i u) ⟨i.val - 1, by omega⟩ = false)
    (hv : value s (i.val - 1) = 0)
    (b r : ℕ) (d : ℝ) (hb : b ≤ barrierHeight s)
    (hr : prefixZeroCount (replace s i u) i.val = r)
    (hlin : d + (r : ℝ) + (b : ℝ) = (i.val : ℝ)) :
    localPotential (replace s i u) ≤ localValue d (r : ℝ) 1 := by
  let j : Fin n := ⟨i.val - 1, by omega⟩
  have hfirst := firstFailure_replace_left hn s i u hi hip hprev
  have hz : value (replace s i u) j.val = 0 := by
    rw [replace_value_strict_before hn s i u j.val (by dsimp [j]; omega)]
    exact hv
  have hj : j.val + 1 = i.val := by dsimp [j]; omega
  have hrun : zeroRun (replace s i u) = r := by
    rw [zeroRun_of_selected _ j hfirst, hj]
    exact hr
  exact localPotential_le_zero _ j hfirst hz b r d
    (le_trans hb (barrierHeight_mono_replace hn s i u hi)) hrun (by rw [hj]; exact hlin)

theorem zeroCount_before_previous_one {n : ℕ} (s : ChainState n) (i : Fin n)
    (hi : firstFailure s = some i) (hip : 0 < i.val)
    (hv : value s (i.val - 1) = 1) : prefixZeroCount s i.val = 0 := by
  have hp : PrefixHolds s (i.val - 1) := by
    intro j hj
    exact selected_prefix s i hi j (by omega)
  have hz := zeroCount_of_incoming_one s (i.val - 1) (by omega) hp hv
  have heq : i.val - 1 + 1 = i.val := by omega
  simpa [heq] using hz

theorem actual_middle_bound {n : ℕ} (hn : 2 ≤ n) (s : ChainState n)
    (i : Fin n) (hi : firstFailure s = some i) (hip : 0 < i.val)
    (hv : value s (i.val - 1) = 1)
    (m : ℕ) (hm : i.val + 1 + m + 1 = n)
    (b : ℕ) (d : ℝ) (hb : b ≤ barrierHeight s) (hd : 0 ≤ d)
    (hlin : d + (b : ℝ) = ((i.val + 1 : ℕ) : ℝ)) (v : Fin 3) (t : Fin 4) :
    localPotential (replace s i (1, v, t)) ≤ middlePayoff m d
      (lettersFrom s (i.val + 1) m hm) (lastTactic s (by omega)) v t := by
  have hinter : i.val + 1 < n := by omega
  have hzero := zeroCount_before_previous_one s i hi hip hv
  have hp : passes (replace s i (1, v, t)) ⟨i.val - 1, by omega⟩ = true := by
    rw [replace_previous_pass hn s i (1, v, t) hip, hv]
    exact bridge_equal_table _ _
  by_cases hv0 : v = 0
  · subst v
    by_cases ht : t = 1
    · have hnow : passes (replace s i (1, 0, t)) i = false := by
        rw [replace_current_pass hn s i (1, 0, t) hip hinter]
        simp [bridge_one_zero_table, ht]
      have hcost := after_stay_one_bound hn s i (1, 0, t) hi hip hp hnow rfl b d hb hlin
      simpa [middlePayoff, ht] using hcost
    · have hnow : passes (replace s i (1, 0, t)) i = true := by
        rw [replace_current_pass hn s i (1, 0, t) hip hinter]
        simp [bridge_one_zero_table, ht]
      have hcount : prefixZeroCount (replace s i (1, 0, t)) (i.val + 1 + 1) = 1 := by
        rw [zeroCount_replace_pair hn s i (1, 0, t) hip hinter, hzero]
        norm_num
      have hcost := after_forward_zero_bound hn s i (1, 0, t) hi hip m hm hp hnow rfl
        b 1 d hb hcount hd (by push_cast at hlin ⊢; linarith)
      simpa [middlePayoff, ht] using hcost
  · by_cases hv1 : v = 1
    · subst v
      have hnow : passes (replace s i (1, 1, t)) i = true := by
        rw [replace_current_pass hn s i (1, 1, t) hip hinter]
        exact bridge_equal_table _ _
      have hcost := after_forward_one_bound hn s i (1, 1, t) hi hip m hm hp hnow rfl
        b (d + 1) hb (by linarith) (by push_cast at hlin ⊢; linarith)
      simpa [middlePayoff] using hcost
    · have hcases : ∀ x : Fin 3, x = 0 ∨ x = 1 ∨ x = 2 := by decide
      have hv2 : v = 2 := by
        rcases hcases v with h0 | h1 | h2
        · exact False.elim (hv0 h0)
        · exact False.elim (hv1 h1)
        · exact h2
      subst v
      have hnow : passes (replace s i (1, 2, t)) i = false := by
        rw [replace_current_pass hn s i (1, 2, t) hip hinter]
        exact bridge_one_two_table _
      have hcost := after_stay_one_bound hn s i (1, 2, t) hi hip hp hnow rfl b d hb hlin
      simpa [middlePayoff] using hcost

theorem actual_strong_step_bound {n : ℕ} (hn : 2 ≤ n) (s : ChainState n)
    (i : Fin n) (hi : firstFailure s = some i) (hip : 0 < i.val)
    (hv : value s (i.val - 1) = 1)
    (htprev : s.tactic ⟨i.val - 1, by omega⟩ ≠ 1)
    (m : ℕ) (hm : i.val + 1 + m + 1 = n)
    (b : ℕ) (d : ℝ) (hb : b ≤ barrierHeight s) (hd : 1 ≤ d)
    (hlin : d + (b : ℝ) = ((i.val + 1 : ℕ) : ℝ)) (u v : Fin 3) (t : Fin 4) :
    localPotential (replace s i (u, v, t)) ≤ strongPayoff m d
      (lettersFrom s (i.val + 1) m hm) (lastTactic s (by omega)) u v t := by
  have hinter : i.val + 1 < n := by omega
  have hzero := zeroCount_before_previous_one s i hi hip hv
  by_cases hu0 : u = 0
  · subst u
    have hp : passes (replace s i (0, v, t)) ⟨i.val - 1, by omega⟩ = true := by
      rw [replace_previous_pass hn s i (0, v, t) hip, hv]
      simp [MTChainProof.bridgePass, htprev]
    by_cases hv0 : v = 0
    · subst v
      have hnow : passes (replace s i (0, 0, t)) i = true := by
        rw [replace_current_pass hn s i (0, 0, t) hip hinter]
        exact bridge_equal_table _ _
      have hcount : prefixZeroCount (replace s i (0, 0, t)) (i.val + 1 + 1) = 2 := by
        rw [zeroCount_replace_pair hn s i (0, 0, t) hip hinter, hzero]
        norm_num
      have hcost := after_forward_zero_bound hn s i (0, 0, t) hi hip m hm hp hnow rfl
        b 2 (d - 1) hb hcount (by linarith) (by push_cast at hlin ⊢; linarith)
      simpa [strongPayoff] using hcost
    · have hnow : passes (replace s i (0, v, t)) i = false := by
        rw [replace_current_pass hn s i (0, v, t) hip hinter, bridge_zero_table]
        simp [hv0]
      have hcount : prefixZeroCount (replace s i (0, v, t)) (i.val + 1) = 1 := by
        rw [zeroCount_replace_incoming hn s i (0, v, t) hip, hzero]
        norm_num
      have hcost := after_stay_zero_bound hn s i (0, v, t) hi hip hp hnow rfl
        b 1 (d - 1) hb hcount (by push_cast at hlin ⊢; linarith)
      simpa [strongPayoff, hv0] using hcost
  · by_cases hu1 : u = 1
    · subst u
      have hcost := actual_middle_bound hn s i hi hip hv m hm b d hb (by linarith) hlin v t
      simpa [strongPayoff] using hcost
    · have hcases : ∀ x : Fin 3, x = 0 ∨ x = 1 ∨ x = 2 := by decide
      have hu2 : u = 2 := by
        rcases hcases u with h0 | h1 | h2
        · exact False.elim (hu0 h0)
        · exact False.elim (hu1 h1)
        · exact h2
      subst u
      have hp : passes (replace s i (2, v, t)) ⟨i.val - 1, by omega⟩ = false := by
        rw [replace_previous_pass hn s i (2, v, t) hip, hv]
        exact bridge_one_two_table _
      have hcost := after_back_one_bound hn s i (2, v, t) hi hip hp hv b (d - 1) hb
        (by push_cast at hlin ⊢; linarith)
      simpa [strongPayoff] using hcost

theorem actual_weak_step_bound {n : ℕ} (hn : 2 ≤ n) (s : ChainState n)
    (i : Fin n) (hi : firstFailure s = some i) (hip : 0 < i.val)
    (hv : value s (i.val - 1) = 1)
    (htprev : s.tactic ⟨i.val - 1, by omega⟩ = 1)
    (m : ℕ) (hm : i.val + 1 + m + 1 = n)
    (b : ℕ) (d : ℝ) (hb : b ≤ barrierHeight s) (hd : 1 ≤ d)
    (hlin : d + (b : ℝ) = ((i.val + 1 : ℕ) : ℝ)) (u v : Fin 3) (t : Fin 4) :
    localPotential (replace s i (u, v, t)) ≤ weakPayoff m d
      (lettersFrom s (i.val + 1) m hm) (lastTactic s (by omega)) u v t := by
  by_cases hu1 : u = 1
  · subst u
    have hcost := actual_middle_bound hn s i hi hip hv m hm b d hb (by linarith) hlin v t
    simpa [weakPayoff] using hcost
  · have hp : passes (replace s i (u, v, t)) ⟨i.val - 1, by omega⟩ = false := by
      rw [replace_previous_pass hn s i (u, v, t) hip, hv]
      simp [MTChainProof.bridgePass, htprev, Ne.symm hu1]
    have hcost := after_back_one_bound hn s i (u, v, t) hi hip hp hv b (d - 1) hb
      (by push_cast at hlin ⊢; linarith)
    simpa [weakPayoff, hu1] using hcost

theorem actual_deepZero_step_bound {n : ℕ} (hn : 2 ≤ n) (s : ChainState n)
    (i : Fin n) (hi : firstFailure s = some i) (hip : 0 < i.val)
    (hv : value s (i.val - 1) = 0)
    (m : ℕ) (hm : i.val + 1 + m + 1 = n)
    (b r : ℕ) (d : ℝ) (hb : b ≤ barrierHeight s) (hd : 0 ≤ d)
    (hr : zeroRun s = r)
    (hlin : d + (r : ℝ) + (b : ℝ) = ((i.val + 1 : ℕ) : ℝ))
    (u v : Fin 3) (t : Fin 4) :
    localPotential (replace s i (u, v, t)) ≤ deepZeroPayoff m d (r : ℝ)
      (lettersFrom s (i.val + 1) m hm) (lastTactic s (by omega)) u v t := by
  have hinter : i.val + 1 < n := by omega
  have hle := selected_incoming_le_previous s i hi hip
  rw [hv] at hle
  have hin : value s i.val = 0 := Fin.le_zero_iff.mp hle
  have hcountold : prefixZeroCount s (i.val + 1) = r := by
    rw [← zeroRun_of_selected s i hi, hr]
  have hq : prefixZeroCount s i.val + 1 = r := by
    rw [prefixZeroCount_succ, hin] at hcountold
    simpa using hcountold
  have hqReal : (prefixZeroCount s i.val : ℝ) + 1 = (r : ℝ) := by exact_mod_cast hq
  by_cases hu0 : u = 0
  · subst u
    have hp : passes (replace s i (0, v, t)) ⟨i.val - 1, by omega⟩ = true := by
      rw [replace_previous_pass hn s i (0, v, t) hip, hv]
      exact bridge_equal_table _ _
    by_cases hv0 : v = 0
    · subst v
      have hnow : passes (replace s i (0, 0, t)) i = true := by
        rw [replace_current_pass hn s i (0, 0, t) hip hinter]
        exact bridge_equal_table _ _
      have hcount : prefixZeroCount (replace s i (0, 0, t)) (i.val + 1 + 1) = r + 1 := by
        rw [zeroCount_replace_pair hn s i (0, 0, t) hip hinter]
        norm_num
        omega
      have hcost := after_forward_zero_bound hn s i (0, 0, t) hi hip m hm hp hnow rfl
        b (r + 1) d hb hcount hd (by push_cast at hlin ⊢; linarith)
      simpa [deepZeroPayoff, Nat.cast_add] using hcost
    · have hnow : passes (replace s i (0, v, t)) i = false := by
        rw [replace_current_pass hn s i (0, v, t) hip hinter, bridge_zero_table]
        simp [hv0]
      have hcount : prefixZeroCount (replace s i (0, v, t)) (i.val + 1) = r := by
        rw [zeroCount_replace_incoming hn s i (0, v, t) hip]
        simpa using hq
      have hcost := after_stay_zero_bound hn s i (0, v, t) hi hip hp hnow rfl
        b r d hb hcount hlin
      simpa [deepZeroPayoff, hv0] using hcost
  · have hp : passes (replace s i (u, v, t)) ⟨i.val - 1, by omega⟩ = false := by
      rw [replace_previous_pass hn s i (u, v, t) hip, hv, bridge_zero_table]
      simp [hu0]
    have hcount : prefixZeroCount (replace s i (u, v, t)) i.val = prefixZeroCount s i.val :=
      zeroCount_replace_before hn s i (u, v, t) i.val le_rfl
    have hcost := after_back_zero_bound hn s i (u, v, t) hi hip hp hv
      b (prefixZeroCount s i.val) d hb hcount (by push_cast at hlin ⊢; linarith)
    simp only [deepZeroPayoff, hu0, ↓reduceIte]
    dsimp [localValue] at hcost ⊢
    linarith

theorem actual_zeroBoundary_step_bound {n : ℕ} (hn : 2 ≤ n) (s : ChainState n)
    (i : Fin n) (hi : firstFailure s = some i) (hip : 0 < i.val)
    (hv : value s (i.val - 1) = 1) (hin : value s i.val = 0)
    (m : ℕ) (hm : i.val + 1 + m + 1 = n)
    (b : ℕ) (d : ℝ) (hb : b ≤ barrierHeight s) (hd : 0 ≤ d)
    (hlin : d + 1 + (b : ℝ) = ((i.val + 1 : ℕ) : ℝ)) (u v : Fin 3) (t : Fin 4) :
    localPotential (replace s i (u, v, t)) ≤ strongPayoff m (d + 1)
      (lettersFrom s (i.val + 1) m hm) (lastTactic s (by omega)) u v t := by
  have htprev := previous_strong_of_descent s i hi hip (by simp [hv, hin])
  exact actual_strong_step_bound hn s i hi hip hv htprev m hm b (d + 1) hb
    (by linarith) hlin u v t

theorem average_deepZeroPayoff (m : ℕ) (d r : ℝ) (u v : Fin 3) (t : Fin 4) :
    average m (fun w last => deepZeroPayoff m d r w last u v t) =
      ScanBounds.deepZeroStep m d r u v t := by
  fin_cases u <;> fin_cases v <;>
    simp [deepZeroPayoff, ScanBounds.deepZeroStep, average_const, average_zeroPayoff]

theorem average_strongPayoff (m : ℕ) (d : ℝ) (u v : Fin 3) (t : Fin 4) :
    average m (fun w last => strongPayoff m d w last u v t) =
      ScanBounds.strongStep m d u v t := by
  fin_cases u <;> fin_cases v <;> fin_cases t <;>
    simp [strongPayoff, middlePayoff, ScanBounds.strongStep, ScanBounds.middleStep,
      average_const, average_zeroPayoff, average_onePayoff]

theorem average_weakPayoff (m : ℕ) (d : ℝ) (u v : Fin 3) (t : Fin 4) :
    average m (fun w last => weakPayoff m d w last u v t) =
      ScanBounds.weakStep m d u v t := by
  fin_cases u <;> fin_cases v <;> fin_cases t <;>
    simp [weakPayoff, middlePayoff, ScanBounds.weakStep, ScanBounds.middleStep,
      average_const, average_zeroPayoff, average_onePayoff]

theorem replace_last_pass {n : ℕ} (hn : 2 ≤ n) (s : ChainState n)
    (i : Fin n) (u : Draw) (hip : 0 < i.val) (hlast : i.val + 1 = n) :
    passes (replace s i u) i = MTChainProof.bridgePass u.1 0 u.2.2 := by
  simp only [passes]
  rw [replace_incoming hn s i u hip, hlast, value_right (by omega), replace_tactic_same]

theorem after_last_good {n : ℕ} (hn : 2 ≤ n) (s : ChainState n)
    (i : Fin n) (u : Draw) (hi : firstFailure s = some i) (hip : 0 < i.val)
    (hlast : i.val + 1 = n)
    (hprev : passes (replace s i u) ⟨i.val - 1, by omega⟩ = true)
    (hnow : passes (replace s i u) i = true) : localPotential (replace s i u) = 0 := by
  have hp := prefix_after_replace hn s i u hi hip hprev hnow
  rw [hlast] at hp
  exact localPotential_of_good _ (prefix_all_good _ hp)

theorem actual_last_middle_bound {n : ℕ} (hn : 2 ≤ n) (s : ChainState n)
    (i : Fin n) (hi : firstFailure s = some i) (hip : 0 < i.val)
    (hv : value s (i.val - 1) = 1) (hlast : i.val + 1 = n)
    (b : ℕ) (d : ℝ) (hb : b ≤ barrierHeight s)
    (hlin : d + (b : ℝ) = ((i.val + 1 : ℕ) : ℝ)) (v : Fin 3) (t : Fin 4) :
    localPotential (replace s i (1, v, t)) ≤ if t = 1 then localValue d 0 0 else 0 := by
  have hp : passes (replace s i (1, v, t)) ⟨i.val - 1, by omega⟩ = true := by
    rw [replace_previous_pass hn s i (1, v, t) hip, hv]
    exact bridge_equal_table _ _
  by_cases ht : t = 1
  · have hnow : passes (replace s i (1, v, t)) i = false := by
      rw [replace_last_pass hn s i (1, v, t) hip hlast]
      simp [bridge_one_zero_table, ht]
    have hcost := after_stay_one_bound hn s i (1, v, t) hi hip hp hnow rfl b d hb hlin
    simpa [ht] using hcost
  · have hnow : passes (replace s i (1, v, t)) i = true := by
      rw [replace_last_pass hn s i (1, v, t) hip hlast]
      simp [bridge_one_zero_table, ht]
    rw [after_last_good hn s i (1, v, t) hi hip hlast hp hnow]
    simp [ht]

theorem actual_last_strong_step_bound {n : ℕ} (hn : 2 ≤ n) (s : ChainState n)
    (i : Fin n) (hi : firstFailure s = some i) (hip : 0 < i.val)
    (hv : value s (i.val - 1) = 1)
    (htprev : s.tactic ⟨i.val - 1, by omega⟩ ≠ 1) (hlast : i.val + 1 = n)
    (b : ℕ) (d : ℝ) (hb : b ≤ barrierHeight s)
    (hlin : d + (b : ℝ) = ((i.val + 1 : ℕ) : ℝ)) (u v : Fin 3) (t : Fin 4) :
    localPotential (replace s i (u, v, t)) ≤
      ScanBounds.lastStrongStep (localValue d 0 0) u v t := by
  by_cases hu0 : u = 0
  · subst u
    have hp : passes (replace s i (0, v, t)) ⟨i.val - 1, by omega⟩ = true := by
      rw [replace_previous_pass hn s i (0, v, t) hip, hv]
      simp [MTChainProof.bridgePass, htprev]
    have hnow : passes (replace s i (0, v, t)) i = true := by
      rw [replace_last_pass hn s i (0, v, t) hip hlast]
      exact bridge_equal_table _ _
    rw [after_last_good hn s i (0, v, t) hi hip hlast hp hnow]
    simp [ScanBounds.lastStrongStep]
  · by_cases hu1 : u = 1
    · subst u
      simpa [ScanBounds.lastStrongStep] using
        actual_last_middle_bound hn s i hi hip hv hlast b d hb hlin v t
    · have hcases : ∀ x : Fin 3, x = 0 ∨ x = 1 ∨ x = 2 := by decide
      have hu2 : u = 2 := by
        rcases hcases u with h0 | h1 | h2
        · exact False.elim (hu0 h0)
        · exact False.elim (hu1 h1)
        · exact h2
      subst u
      have hp : passes (replace s i (2, v, t)) ⟨i.val - 1, by omega⟩ = false := by
        rw [replace_previous_pass hn s i (2, v, t) hip, hv]
        exact bridge_one_two_table _
      have hcost := after_back_one_bound hn s i (2, v, t) hi hip hp hv b (d - 1) hb
        (by push_cast at hlin ⊢; linarith)
      dsimp [ScanBounds.lastStrongStep, localValue] at hcost ⊢
      linarith

theorem actual_last_weak_step_bound {n : ℕ} (hn : 2 ≤ n) (s : ChainState n)
    (i : Fin n) (hi : firstFailure s = some i) (hip : 0 < i.val)
    (hv : value s (i.val - 1) = 1)
    (htprev : s.tactic ⟨i.val - 1, by omega⟩ = 1) (hlast : i.val + 1 = n)
    (b : ℕ) (d : ℝ) (hb : b ≤ barrierHeight s)
    (hlin : d + (b : ℝ) = ((i.val + 1 : ℕ) : ℝ)) (u v : Fin 3) (t : Fin 4) :
    localPotential (replace s i (u, v, t)) ≤
      ScanBounds.lastWeakStep (localValue d 0 0) u v t := by
  by_cases hu1 : u = 1
  · subst u
    simpa [ScanBounds.lastWeakStep] using
      actual_last_middle_bound hn s i hi hip hv hlast b d hb hlin v t
  · have hp : passes (replace s i (u, v, t)) ⟨i.val - 1, by omega⟩ = false := by
      rw [replace_previous_pass hn s i (u, v, t) hip, hv]
      simp [MTChainProof.bridgePass, htprev, Ne.symm hu1]
    have hcost := after_back_one_bound hn s i (u, v, t) hi hip hp hv b (d - 1) hb
      (by push_cast at hlin ⊢; linarith)
    simp only [ScanBounds.lastWeakStep, hu1, ↓reduceIte]
    dsimp [localValue] at hcost ⊢
    linarith

end MTChainFormal.ActualStep
