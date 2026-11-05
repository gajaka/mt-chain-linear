import Chain
import PotentialAlgebra

set_option autoImplicit false

namespace MTChainFormal

open scoped BigOperators

def IsBarrier {n : ℕ} (s : ChainState n) (i : Fin n) : Prop :=
  PrefixHolds s (i.val + 1) ∧ value s i.val = 2 ∧ s.tactic i ≠ 1

noncomputable def barrierCandidates {n : ℕ} (s : ChainState n) : Finset (Fin n) := by
  classical
  exact Finset.univ.filter (IsBarrier s)

@[simp] theorem mem_barrierCandidates {n : ℕ} (s : ChainState n) (i : Fin n) :
    i ∈ barrierCandidates s ↔ IsBarrier s i := by
  classical
  simp [barrierCandidates]

/-- One-based least failure; n+1 is used only for the terminal index. -/
noncomputable def failureIndex {n : ℕ} (s : ChainState n) : ℕ :=
  match firstFailure s with
  | none => n + 1
  | some i => i.val + 1

/-- Good is assigned height n, irrespective of its individual earlier barriers. -/
noncomputable def barrierHeight {n : ℕ} (s : ChainState n) : ℕ :=
  if firstFailure s = none then n else (barrierCandidates s).sup (fun i => i.val + 1)

noncomputable def prefixZeroSites {n : ℕ} (s : ChainState n) : Finset ℕ :=
  (Finset.range (failureIndex s)).filter (fun j => value s j = 0)

/-- In a passing nonincreasing prefix all its zero sites form the trailing run. -/
noncomputable def zeroRun {n : ℕ} (s : ChainState n) : ℕ :=
  if firstFailure s = none then 0 else (prefixZeroSites s).card

noncomputable def retainedDistance {n : ℕ} (s : ChainState n) : ℕ :=
  if firstFailure s = none then 0 else failureIndex s - zeroRun s - barrierHeight s

noncomputable def zeroIndicator {n : ℕ} (s : ChainState n) : ℝ :=
  if zeroRun s = 0 then 0 else 1

noncomputable def localPotential {n : ℕ} (s : ChainState n) : ℝ :=
  PotentialAlgebra.localValue (retainedDistance s : ℝ) (zeroRun s : ℝ)
    (zeroIndicator s)

noncomputable def chainPotential {n : ℕ} (s : ChainState n) : ℝ :=
  PotentialAlgebra.totalValue (n : ℝ) (barrierHeight s : ℝ) (localPotential s)

@[simp] theorem failureIndex_of_selected {n : ℕ} (s : ChainState n) (i : Fin n)
    (hi : firstFailure s = some i) : failureIndex s = i.val + 1 := by
  simp [failureIndex, hi]

@[simp] theorem failureIndex_of_good {n : ℕ} (s : ChainState n)
    (hg : firstFailure s = none) : failureIndex s = n + 1 := by
  simp [failureIndex, hg]

theorem failureIndex_le_of_selected {n : ℕ} (s : ChainState n) (i : Fin n)
    (hi : firstFailure s = some i) : failureIndex s ≤ n := by
  rw [failureIndex_of_selected s i hi]
  omega

theorem barrierHeight_le {n : ℕ} (s : ChainState n) : barrierHeight s ≤ n := by
  classical
  unfold barrierHeight
  split
  · exact le_rfl
  · apply Finset.sup_le
    intro i _
    omega

theorem zeroRun_le_failureIndex {n : ℕ} (s : ChainState n) :
    zeroRun s ≤ failureIndex s := by
  unfold zeroRun
  split
  · exact Nat.zero_le _
  · calc
      (prefixZeroSites s).card ≤ (Finset.range (failureIndex s)).card :=
        Finset.card_le_card (Finset.filter_subset _ _)
      _ = failureIndex s := Finset.card_range _

theorem zeroRun_le {n : ℕ} (s : ChainState n) : zeroRun s ≤ n := by
  cases hs : firstFailure s with
  | none => simp [zeroRun, hs]
  | some i =>
      exact le_trans (zeroRun_le_failureIndex s) (failureIndex_le_of_selected s i hs)

theorem retainedDistance_le {n : ℕ} (s : ChainState n) : retainedDistance s ≤ n := by
  cases hs : firstFailure s with
  | none => simp [retainedDistance, hs]
  | some i =>
      have h := failureIndex_le_of_selected s i hs
      simp only [retainedDistance, hs, Option.some_ne_none, ↓reduceIte]
      omega

theorem zeroIndicator_nonneg {n : ℕ} (s : ChainState n) : 0 ≤ zeroIndicator s := by
  unfold zeroIndicator
  split <;> norm_num

theorem zeroIndicator_le_one {n : ℕ} (s : ChainState n) : zeroIndicator s ≤ 1 := by
  unfold zeroIndicator
  split <;> norm_num

theorem localPotential_nonneg {n : ℕ} (s : ChainState n) : 0 ≤ localPotential s := by
  exact PotentialAlgebra.localValue_nonneg _ _ _
    (Nat.cast_nonneg _) (Nat.cast_nonneg _) (zeroIndicator_nonneg s)

theorem localPotential_le {n : ℕ} (hn : 2 ≤ n) (s : ChainState n) :
    localPotential s ≤ 54 * (n : ℝ) := by
  apply PotentialAlgebra.localValue_le
  · exact_mod_cast hn
  · exact_mod_cast retainedDistance_le s
  · exact_mod_cast zeroRun_le s
  · exact zeroIndicator_le_one s

theorem chainPotential_nonneg {n : ℕ} (s : ChainState n) : 0 ≤ chainPotential s := by
  apply PotentialAlgebra.totalValue_nonneg
  · exact Nat.cast_nonneg _
  · exact_mod_cast barrierHeight_le s
  · exact localPotential_nonneg s

theorem chainPotential_le {n : ℕ} (hn : 2 ≤ n) (s : ChainState n) :
    chainPotential s ≤ 283 * (n : ℝ)^2 := by
  apply PotentialAlgebra.totalValue_le_quadratic
  · exact_mod_cast hn
  · exact Nat.cast_nonneg _
  · exact localPotential_le hn s

@[simp] theorem zeroRun_of_good {n : ℕ} (s : ChainState n)
    (hg : firstFailure s = none) : zeroRun s = 0 := by simp [zeroRun, hg]

@[simp] theorem barrierHeight_of_good {n : ℕ} (s : ChainState n)
    (hg : firstFailure s = none) : barrierHeight s = n := by simp [barrierHeight, hg]

@[simp] theorem localPotential_of_good {n : ℕ} (s : ChainState n)
    (hg : firstFailure s = none) : localPotential s = 0 := by
  simp [localPotential, retainedDistance, zeroIndicator, zeroRun, hg,
    PotentialAlgebra.localValue]

@[simp] theorem chainPotential_of_good {n : ℕ} (s : ChainState n)
    (hg : firstFailure s = none) : chainPotential s = 0 := by
  simp [chainPotential, barrierHeight_of_good s hg, localPotential_of_good s hg,
    PotentialAlgebra.totalValue]

theorem passes_imp_le {n : ℕ} (s : ChainState n) (i : Fin n)
    (hp : passes s i = true) : value s (i.val + 1) ≤ value s i.val := by
  by_cases hw : s.tactic i = 1
  · have heq : value s i.val = value s (i.val + 1) := by
      simpa [passes, MTChainProof.bridgePass, hw] using hp
    exact le_of_eq heq.symm
  · simpa [passes, MTChainProof.bridgePass, hw] using hp

theorem prefix_value_antitone {n : ℕ} (s : ChainState n) (cut : ℕ)
    (hp : PrefixHolds s cut) (hc : cut ≤ n) (j k : ℕ)
    (hjk : j ≤ k) (hk : k ≤ cut) : value s k ≤ value s j := by
  induction k generalizing j with
  | zero =>
      have hj : j = 0 := by omega
      simp [hj]
  | succ k ih =>
      by_cases heq : j = k + 1
      · simp [heq]
      · have hj : j ≤ k := by omega
        have hkn : k < n := by omega
        have hpass := hp (⟨k, hkn⟩ : Fin n) (by change k < cut; omega)
        exact le_trans (passes_imp_le s ⟨k, hkn⟩ hpass)
          (ih j hj (by omega))

theorem barrier_before_selected {n : ℕ} (s : ChainState n) (i j : Fin n)
    (hb : IsBarrier s i) (hj : firstFailure s = some j) : i.val < j.val := by
  by_contra h
  have hp := hb.1 j (by omega)
  have hf := selected_failed s j hj
  rw [hf] at hp
  cases hp

theorem barrierHeight_le_selected {n : ℕ} (s : ChainState n) (i : Fin n)
    (hi : firstFailure s = some i) : barrierHeight s ≤ i.val := by
  classical
  simp only [barrierHeight, hi, Option.some_ne_none, ↓reduceIte]
  apply Finset.sup_le
  intro j hj
  have h := barrier_before_selected s j i ((mem_barrierCandidates s j).mp hj) hi
  omega

theorem zeroRun_le_after_barrier {n : ℕ} (s : ChainState n) (i j : Fin n)
    (hi : firstFailure s = some i) (hb : IsBarrier s j) :
    zeroRun s ≤ failureIndex s - (j.val + 1) := by
  have hsub : prefixZeroSites s ⊆ Finset.Ico (j.val + 1) (failureIndex s) := by
    intro k hk
    obtain ⟨hkrange, hkzero⟩ := Finset.mem_filter.mp hk
    have hkup : k < failureIndex s := Finset.mem_range.mp hkrange
    refine Finset.mem_Ico.mpr ⟨?_, hkup⟩
    by_contra h
    have hkj : k ≤ j.val := by omega
    have hmono := prefix_value_antitone s (j.val + 1) hb.1
      (by omega) k j.val hkj (by omega)
    rw [hb.2.1, hkzero] at hmono
    norm_num at hmono
  have hc := Finset.card_le_card hsub
  simpa [zeroRun, hi, Nat.card_Ico] using hc

theorem barrierHeight_le_retained_prefix {n : ℕ} (s : ChainState n) (i : Fin n)
    (hi : firstFailure s = some i) : barrierHeight s ≤ failureIndex s - zeroRun s := by
  classical
  simp only [barrierHeight, hi, Option.some_ne_none, ↓reduceIte]
  apply Finset.sup_le
  intro j hj
  have hb := (mem_barrierCandidates s j).mp hj
  have hzero := zeroRun_le_after_barrier s i j hi hb
  have hbefore := barrier_before_selected s j i hb hi
  have hindex := failureIndex_of_selected s i hi
  omega

theorem zeroRun_pos_iff {n : ℕ} (s : ChainState n) (i : Fin n)
    (hi : firstFailure s = some i) : 0 < zeroRun s ↔ value s i.val = 0 := by
  classical
  have hindex := failureIndex_of_selected s i hi
  have hr : zeroRun s = (prefixZeroSites s).card := by simp [zeroRun, hi]
  rw [hr, Finset.card_pos]
  constructor
  · rintro ⟨k, hk⟩
    obtain ⟨hkrange, hkzero⟩ := Finset.mem_filter.mp hk
    have hkup : k < failureIndex s := Finset.mem_range.mp hkrange
    have hki : k ≤ i.val := by omega
    have hmono := prefix_value_antitone s i.val (selected_prefix s i hi)
      (by omega) k i.val hki (by omega)
    rw [hkzero] at hmono
    exact Fin.le_zero_iff.mp hmono
  · intro hz
    refine ⟨i.val, ?_⟩
    apply Finset.mem_filter.mpr
    refine ⟨?_, hz⟩
    exact Finset.mem_range.mpr (by omega)

theorem selected_incoming_le_previous {n : ℕ} (s : ChainState n) (i : Fin n)
    (hi : firstFailure s = some i) (hip : 0 < i.val) :
    value s i.val ≤ value s (i.val - 1) := by
  have hp := (selected_prefix s i hi) (⟨i.val - 1, by omega⟩ : Fin n)
    (by change i.val - 1 < i.val; omega)
  have hh := passes_imp_le s ⟨i.val - 1, by omega⟩ hp
  have heq : i.val - 1 + 1 = i.val := by omega
  simpa [heq] using hh

theorem zeroRun_two_le_of_previous_zero {n : ℕ} (s : ChainState n) (i : Fin n)
    (hi : firstFailure s = some i) (hip : 0 < i.val)
    (hprev : value s (i.val - 1) = 0) : 2 ≤ zeroRun s := by
  classical
  have hle := selected_incoming_le_previous s i hi hip
  rw [hprev] at hle
  have hin : value s i.val = 0 := Fin.le_zero_iff.mp hle
  have hindex := failureIndex_of_selected s i hi
  have hsub : ({i.val - 1, i.val} : Finset ℕ) ⊆ prefixZeroSites s := by
    intro k hk
    simp only [Finset.mem_insert, Finset.mem_singleton] at hk
    apply Finset.mem_filter.mpr
    rcases hk with hk | hk
    · subst k
      exact ⟨Finset.mem_range.mpr (by omega), hprev⟩
    · subst k
      exact ⟨Finset.mem_range.mpr (by omega), hin⟩
  have hc := Finset.card_le_card hsub
  have hne : i.val - 1 ≠ i.val := by omega
  simpa [zeroRun, hi, hne] using hc

theorem replace_value_strict_before {n : ℕ} (hn : 2 ≤ n) (s : ChainState n)
    (i : Fin n) (u : Draw) (k : ℕ) (hk : k < i.val) :
    value (replace s i u) k = value s k := by
  rw [replace_value hn s i u k (by omega)]
  by_cases h0 : k = 0
  · simp [h0]
  have hkn : k ≠ n := by omega
  have hki : k ≠ i.val := by omega
  have hki1 : k ≠ i.val + 1 := by omega
  simp [h0, hkn, hki, hki1]

theorem IsBarrier_preserved {n : ℕ} (hn : 2 ≤ n) (s : ChainState n)
    (i j : Fin n) (u : Draw) (hb : IsBarrier s j) (hji : j.val < i.val) :
    IsBarrier (replace s i u) j := by
  have hne : j ≠ i := by intro heq; subst j; omega
  have hv : value (replace s i u) j.val = 2 := by
    rw [replace_value_strict_before hn s i u j.val hji]
    exact hb.2.1
  have ht : (replace s i u).tactic j ≠ 1 := by
    rw [replace_tactic_other s i j u hne]
    exact hb.2.2
  refine ⟨?_, hv, ht⟩
  intro k hk
  by_cases hkj : k = j
  · subst k
    have hmax : value (replace s i u) (j.val + 1) ≤ (2 : Fin 3) := Fin.le_last _
    simp [passes, MTChainProof.bridgePass, ht, hv, hmax]
  · have hfar : k.val + 1 < i.val := by
      have : k.val ≠ j.val := by intro h; exact hkj (Fin.ext h)
      omega
    rw [replace_pass_unchanged hn s i k u (Or.inl hfar)]
    exact hb.1 k hk

theorem barrierHeight_mono_replace {n : ℕ} (hn : 2 ≤ n) (s : ChainState n)
    (i : Fin n) (u : Draw) (hi : firstFailure s = some i) :
    barrierHeight s ≤ barrierHeight (replace s i u) := by
  classical
  by_cases hg : firstFailure (replace s i u) = none
  · rw [barrierHeight_of_good _ hg]
    exact barrierHeight_le s
  · simp only [barrierHeight, hi, Option.some_ne_none, hg, ↓reduceIte]
    apply Finset.sup_le
    intro j hj
    have hb := (mem_barrierCandidates s j).mp hj
    have hbnew := IsBarrier_preserved hn s i j u hb (barrier_before_selected s j i hb hi)
    exact Finset.le_sup (f := fun k : Fin n => k.val + 1)
      ((mem_barrierCandidates _ j).mpr hbnew)

theorem install_selected_barrier {n : ℕ} (hn : 2 ≤ n) (s : ChainState n)
    (i : Fin n) (u : Draw) (hi : firstFailure s = some i)
    (he : i.val = 0 ∨ value s (i.val - 1) = 2)
    (hu : u.1 = 2) (ht : u.2.2 ≠ 1) : IsBarrier (replace s i u) i := by
  have hvin : value (replace s i u) i.val = 2 := by
    by_cases hi0 : i.val = 0
    · simp [hi0]
    · rw [replace_incoming hn s i u (by omega)]
      exact hu
  have hnewt : (replace s i u).tactic i ≠ 1 := by simpa using ht
  refine ⟨?_, hvin, hnewt⟩
  intro k hk
  by_cases hki : k = i
  · subst k
    have hmax : value (replace s i u) (i.val + 1) ≤ (2 : Fin 3) := Fin.le_last _
    simp [passes, MTChainProof.bridgePass, ht, hvin, hmax]
  · have hklt : k.val < i.val := by
      have : k.val ≠ i.val := by intro h; exact hki (Fin.ext h)
      omega
    by_cases hadj : k.val + 1 = i.val
    · have hprev : value s (i.val - 1) = 2 := by
        rcases he with he | he
        · omega
        · exact he
      have hkprev : k.val = i.val - 1 := by omega
      have hleft : value (replace s i u) k.val = 2 := by
        rw [replace_value_strict_before hn s i u k.val hklt, hkprev, hprev]
      have hright : value (replace s i u) (k.val + 1) = 2 := by
        rw [hadj, hvin]
      simp [passes, MTChainProof.bridgePass, hleft, hright]
    · have hfar : k.val + 1 < i.val := by omega
      rw [replace_pass_unchanged hn s i k u (Or.inl hfar)]
      exact selected_prefix s i hi k hklt

theorem barrierHeight_advance_replace {n : ℕ} (hn : 2 ≤ n) (s : ChainState n)
    (i : Fin n) (u : Draw) (hi : firstFailure s = some i)
    (he : i.val = 0 ∨ value s (i.val - 1) = 2)
    (hu : u.1 = 2) (ht : u.2.2 ≠ 1) :
    barrierHeight s + 1 ≤ barrierHeight (replace s i u) := by
  classical
  have hbnew := install_selected_barrier hn s i u hi he hu ht
  have hold := barrierHeight_le_selected s i hi
  have hnew : i.val + 1 ≤ barrierHeight (replace s i u) := by
    by_cases hg : firstFailure (replace s i u) = none
    · rw [barrierHeight_of_good _ hg]
      omega
    · simp only [barrierHeight, hg, ↓reduceIte]
      exact Finset.le_sup (f := fun k : Fin n => k.val + 1)
        ((mem_barrierCandidates _ i).mpr hbnew)
  omega

theorem zeroRun_eq_one_of_previous_nonzero {n : ℕ} (s : ChainState n) (i : Fin n)
    (hi : firstFailure s = some i) (hip : 0 < i.val)
    (hin : value s i.val = 0) (hprev : value s (i.val - 1) ≠ 0) : zeroRun s = 1 := by
  classical
  have hindex := failureIndex_of_selected s i hi
  have hset : prefixZeroSites s = {i.val} := by
    ext k
    constructor
    · intro hk
      obtain ⟨hkrange, hkzero⟩ := Finset.mem_filter.mp hk
      have hkup : k < failureIndex s := Finset.mem_range.mp hkrange
      have hki : k ≤ i.val := by omega
      have heq : k = i.val := by
        by_contra hne
        have hkprev : k ≤ i.val - 1 := by omega
        have hmono := prefix_value_antitone s i.val (selected_prefix s i hi)
          (by omega) k (i.val - 1) hkprev (by omega)
        rw [hkzero] at hmono
        exact hprev (Fin.le_zero_iff.mp hmono)
      simp [heq]
    · intro hk
      have hkval : k = i.val := Finset.mem_singleton.mp hk
      subst k
      exact Finset.mem_filter.mpr ⟨Finset.mem_range.mpr (by omega), hin⟩
  simp [zeroRun, hi, hset]

theorem previous_strong_of_descent {n : ℕ} (s : ChainState n) (i : Fin n)
    (hi : firstFailure s = some i) (hip : 0 < i.val)
    (hneq : value s (i.val - 1) ≠ value s i.val) :
    s.tactic ⟨i.val - 1, by omega⟩ ≠ 1 := by
  intro hw
  have hp := (selected_prefix s i hi) (⟨i.val - 1, by omega⟩ : Fin n)
    (by change i.val - 1 < i.val; omega)
  have heq : i.val - 1 + 1 = i.val := by omega
  simp [passes, MTChainProof.bridgePass, hw, heq] at hp
  exact hneq hp

theorem regular_classification {n : ℕ} (s : ChainState n) (i : Fin n)
    (hi : firstFailure s = some i)
    (he : ¬ (i.val = 0 ∨ value s (i.val - 1) = 2)) :
    (value s (i.val - 1) = 0 ∧ value s i.val = 0 ∧ 2 ≤ zeroRun s) ∨
    (value s (i.val - 1) = 1 ∧ value s i.val = 0 ∧ zeroRun s = 1) ∨
    (value s (i.val - 1) = 1 ∧ value s i.val = 1) := by
  have hip : 0 < i.val := by omega
  have hprev2 : value s (i.val - 1) ≠ 2 := by tauto
  have hle := selected_incoming_le_previous s i hi hip
  have hc : ∀ v : Fin 3, v = 0 ∨ v = 1 ∨ v = 2 := by decide
  rcases hc (value s (i.val - 1)) with h0 | h1 | h2
  · left
    have hin : value s i.val = 0 := by
      rw [h0] at hle
      exact Fin.le_zero_iff.mp hle
    exact ⟨h0, hin, zeroRun_two_le_of_previous_zero s i hi hip h0⟩
  · right
    have hone : ∀ v : Fin 3, v ≤ 1 → v = 0 ∨ v = 1 := by decide
    have hin := hone (value s i.val) (by simpa [h1] using hle)
    rcases hin with hz | ho
    · left
      refine ⟨h1, hz, zeroRun_eq_one_of_previous_nonzero s i hi hip hz ?_⟩
      simp [h1]
    · exact Or.inr ⟨h1, ho⟩
  · exact False.elim (hprev2 h2)

theorem maximal_strong_draw_count :
    (∑ u : Draw, if u.1 = 2 ∧ u.2.2 ≠ 1 then (1 : ℕ) else 0) = 9 := by decide

theorem barrierHeight_sum_advance {n : ℕ} (hn : 2 ≤ n) (s : ChainState n)
    (i : Fin n) (hi : firstFailure s = some i)
    (he : i.val = 0 ∨ value s (i.val - 1) = 2) :
    36 * barrierHeight s + 9 ≤ ∑ u : Draw, barrierHeight (replace s i u) := by
  classical
  have hpoint (u : Draw) :
      barrierHeight s + (if u.1 = 2 ∧ u.2.2 ≠ 1 then 1 else 0) ≤
        barrierHeight (replace s i u) := by
    by_cases h : u.1 = 2 ∧ u.2.2 ≠ 1
    · simpa [h] using barrierHeight_advance_replace hn s i u hi he h.1 h.2
    · simpa [h] using barrierHeight_mono_replace hn s i u hi
  have hs := Finset.sum_le_sum (fun u (_ : u ∈ (Finset.univ : Finset Draw)) => hpoint u)
  have hc : Fintype.card Draw = 36 := by decide
  have hsuccess : (Finset.univ.filter (fun u : Draw => u.1 = 2 ∧ u.2.2 ≠ 1)).card = 9 :=
    by decide
  simpa [Finset.sum_add_distrib, hc, hsuccess] using hs

theorem barrierHeight_average_advance {n : ℕ} (hn : 2 ≤ n) (s : ChainState n)
    (i : Fin n) (hi : firstFailure s = some i)
    (he : i.val = 0 ∨ value s (i.val - 1) = 2) :
    (barrierHeight s : ℝ) + 1 / 4 ≤
      (∑ u : Draw, (barrierHeight (replace s i u) : ℝ)) / 36 := by
  have hnat := barrierHeight_sum_advance hn s i hi he
  have hreal : (36 : ℝ) * (barrierHeight s : ℝ) + 9 ≤
      ∑ u : Draw, (barrierHeight (replace s i u) : ℝ) := by exact_mod_cast hnat
  linarith

end MTChainFormal
