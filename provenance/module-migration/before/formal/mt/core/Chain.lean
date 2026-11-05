import FreshDraws
import Mathlib.Data.Finset.Max
import Mathlib.Tactic

set_option autoImplicit false

namespace MTChainFormal

open scoped BigOperators

/-- The original finite catalog: n-1 mutable thresholds and n raw tactic
    labels. The endpoint values are supplied by `value`, not extra variables. -/
structure ChainState (n : ℕ) where
  values : Fin (n - 1) → Fin 3
  tactic : Fin n → Fin 4
  deriving DecidableEq, Fintype

def value {n : ℕ} (s : ChainState n) (j : ℕ) : Fin 3 :=
  if j = 0 then 2
  else if h : j - 1 < n - 1 then s.values ⟨j - 1, h⟩ else 0

@[simp] theorem value_zero {n : ℕ} (s : ChainState n) : value s 0 = 2 := by
  simp [value]

@[simp] theorem value_internal {n : ℕ} (s : ChainState n) (j : Fin (n - 1)) :
    value s (j.val + 1) = s.values j := by
  simp [value, j.isLt]

theorem value_right {n : ℕ} (hn : 0 < n) (s : ChainState n) : value s n = 0 := by
  have h0 : n ≠ 0 := by omega
  simp [value, h0]

def passes {n : ℕ} (s : ChainState n) (i : Fin n) : Bool :=
  MTChainProof.bridgePass (value s i.val) (value s (i.val + 1)) (s.tactic i)

def PrefixHolds {n : ℕ} (s : ChainState n) (cut : ℕ) : Prop :=
  ∀ i : Fin n, i.val < cut → passes s i = true

def badIndices {n : ℕ} (s : ChainState n) : Finset (Fin n) :=
  Finset.univ.filter (fun i => passes s i = false)

@[simp] theorem mem_badIndices {n : ℕ} (s : ChainState n) (i : Fin n) :
    i ∈ badIndices s ↔ passes s i = false := by simp [badIndices]

noncomputable def firstFailure {n : ℕ} (s : ChainState n) : Option (Fin n) :=
  if h : (badIndices s).Nonempty then some ((badIndices s).min' h) else none

theorem firstFailure_eq_some {n : ℕ} (s : ChainState n)
    (h : (badIndices s).Nonempty) :
    firstFailure s = some ((badIndices s).min' h) := by simp [firstFailure, h]

theorem selected_failed {n : ℕ} (s : ChainState n) (i : Fin n)
    (hi : firstFailure s = some i) : passes s i = false := by
  classical
  unfold firstFailure at hi
  split at hi
  next h =>
    have heq : (badIndices s).min' h = i := Option.some.inj hi
    exact (mem_badIndices s i).mp (heq ▸ Finset.min'_mem _ h)
  next h => simp at hi

theorem selected_prefix {n : ℕ} (s : ChainState n) (i : Fin n)
    (hi : firstFailure s = some i) : PrefixHolds s i.val := by
  classical
  intro j hj
  cases hp : passes s j with
  | true => rfl
  | false =>
    have hjbad : j ∈ badIndices s := (mem_badIndices s j).mpr hp
    unfold firstFailure at hi
    split at hi
    next h =>
      have heq : (badIndices s).min' h = i := Option.some.inj hi
      have hle : i ≤ j := heq ▸ Finset.min'_le _ j hjbad
      have : i.val ≤ j.val := hle
      omega
    next h => simp at hi

theorem no_failure_iff {n : ℕ} (s : ChainState n) :
    firstFailure s = none ↔ ∀ i, passes s i = true := by
  classical
  constructor
  · intro hnone i
    cases hp : passes s i with
    | true => rfl
    | false =>
      have hb : (badIndices s).Nonempty := ⟨i, (mem_badIndices s i).mpr hp⟩
      simp [firstFailure, hb] at hnone
  · intro hall
    have hb : ¬ (badIndices s).Nonempty := by
      intro h
      obtain ⟨i, hi⟩ := h
      have hfalse := (mem_badIndices s i).mp hi
      simp [hall i] at hfalse
    simp [firstFailure, hb]

theorem firstFailure_of_failed_prefix {n : ℕ} (s : ChainState n) (i : Fin n)
    (hf : passes s i = false) (hp : PrefixHolds s i.val) :
    firstFailure s = some i := by
  classical
  have hb : (badIndices s).Nonempty := ⟨i, (mem_badIndices s i).mpr hf⟩
  have hmin := Finset.min'_mem (badIndices s) hb
  have hle : (badIndices s).min' hb ≤ i :=
    Finset.min'_le (badIndices s) i ((mem_badIndices s i).mpr hf)
  have hge : i ≤ (badIndices s).min' hb := by
    by_contra h
    have hv : ((badIndices s).min' hb).val < i.val := by
      exact not_le.mp h
    have ht := hp _ hv
    have hfalse := (mem_badIndices s _).mp hmin
    simp [ht] at hfalse
  have heq := le_antisymm hle hge
  simp [firstFailure, hb, heq]

abbrev Draw := Fin 3 × Fin 3 × Fin 4

/-- Both endpoint draws are harmless dummy draws. The induced transition
    law is exactly the registered law omitting fixed endpoint coordinates. -/
def replace {n : ℕ} (s : ChainState n) (i : Fin n) (u : Draw) : ChainState n where
  values j := if j.val + 1 = i.val then u.1
    else if j.val + 1 = i.val + 1 then u.2.1 else s.values j
  tactic j := if j = i then u.2.2 else s.tactic j

@[simp] theorem replace_tactic_same {n : ℕ} (s : ChainState n) (i : Fin n) (u : Draw) :
    (replace s i u).tactic i = u.2.2 := by simp [replace]

theorem replace_tactic_other {n : ℕ} (s : ChainState n) (i j : Fin n)
    (u : Draw) (hji : j ≠ i) :
    (replace s i u).tactic j = s.tactic j := by simp [replace, hji]

theorem replace_value {n : ℕ} (hn : 2 ≤ n) (s : ChainState n)
    (i : Fin n) (u : Draw) (j : ℕ) (hj : j ≤ n) :
    value (replace s i u) j =
      if j = 0 then 2 else if j = n then 0
      else if j = i.val then u.1
      else if j = i.val + 1 then u.2.1 else value s j := by
  by_cases h0 : j = 0
  · simp [h0]
  by_cases hlast : j = n
  · subst j
    simp [value_right (by omega : 0 < n), h0]
  have hjint : j - 1 < n - 1 := by omega
  have hj1 : j - 1 + 1 = j := by omega
  have hsub : (j - 1 = i.val) ↔ j = i.val + 1 := by omega
  simp [value, h0, hlast, hjint, replace, hj1, hsub]

theorem replace_pass_unchanged {n : ℕ} (hn : 2 ≤ n)
    (s : ChainState n) (i j : Fin n) (u : Draw)
    (hfar : j.val + 1 < i.val ∨ i.val + 1 < j.val) :
    passes (replace s i u) j = passes s j := by
  have hne : j ≠ i := by intro h; subst j; omega
  have hvals : value (replace s i u) j.val = value s j.val := by
    rw [replace_value hn s i u j.val (by omega)]
    by_cases h0 : j.val = 0
    · simp [h0]
    have hn0 : j.val ≠ n := by omega
    have hi0 : j.val ≠ i.val := by omega
    have hi1 : j.val ≠ i.val + 1 := by omega
    simp [h0, hn0, hi0, hi1]
  have hnext : value (replace s i u) (j.val + 1) = value s (j.val + 1) := by
    rw [replace_value hn s i u (j.val + 1) (by omega)]
    have hi0 : j.val + 1 ≠ i.val := by omega
    have hij : j.val ≠ i.val := by omega
    by_cases hl : j.val + 1 = n
    · rw [hl, ite_eq_right (by omega : n ≠ 0), ite_eq_left rfl]
      exact (value_right (by omega : 0 < n) s).symm
    · simp [hl, hi0, hij]
  simp only [passes, hvals, hnext, replace_tactic_other s i j u hne]

theorem replacement_cut_lower_bound {n : ℕ} (hn : 2 ≤ n)
    (s : ChainState n) (i j : Fin n) (u : Draw)
    (hi : firstFailure s = some i)
    (hj : firstFailure (replace s i u) = some j) : i.val ≤ j.val + 1 := by
  by_contra h
  have hfar : j.val + 1 < i.val := by omega
  have hp := selected_prefix s i hi j (by omega)
  have hf := selected_failed (replace s i u) j hj
  rw [replace_pass_unchanged hn s i j u (Or.inl hfar), hp] at hf
  cases hf

theorem replace_incoming {n : ℕ} (hn : 2 ≤ n) (s : ChainState n)
    (i : Fin n) (u : Draw) (hi : 0 < i.val) :
    value (replace s i u) i.val = u.1 := by
  rw [replace_value hn s i u i.val (by omega)]
  rw [ite_eq_right (Nat.ne_of_gt hi), ite_eq_right (by omega : i.val ≠ n),
    ite_eq_left rfl]

theorem replace_outgoing {n : ℕ} (hn : 2 ≤ n) (s : ChainState n)
    (i : Fin n) (u : Draw) (hi : i.val + 1 < n) :
    value (replace s i u) (i.val + 1) = u.2.1 := by
  rw [replace_value hn s i u (i.val + 1) (by omega)]
  rw [ite_eq_right (by omega : i.val + 1 ≠ 0),
    ite_eq_right (by omega : i.val + 1 ≠ n),
    ite_eq_right (by omega : i.val + 1 ≠ i.val), ite_eq_left rfl]

theorem replace_value_before {n : ℕ} (hn : 2 ≤ n) (s : ChainState n)
    (i : Fin n) (u : Draw) (j : ℕ) (hj : j < i.val) :
    value (replace s i u) j = value s j := by
  by_cases h0 : j = 0
  · simp [h0]
  rw [replace_value hn s i u j (by omega), ite_eq_right h0,
    ite_eq_right (by omega : j ≠ n), ite_eq_right (by omega : j ≠ i.val),
    ite_eq_right (by omega : j ≠ i.val + 1)]

theorem replacement_prefix_before_left {n : ℕ} (hn : 2 ≤ n)
    (s : ChainState n) (i : Fin n) (u : Draw)
    (hi : firstFailure s = some i) :
    PrefixHolds (replace s i u) (i.val - 1) := by
  intro j hj
  rw [replace_pass_unchanged hn s i j u (Or.inl (by omega))]
  exact selected_prefix s i hi j (by omega)

theorem replacement_backstep {n : ℕ} (hn : 2 ≤ n)
    (s : ChainState n) (i : Fin n) (u : Draw)
    (hi : firstFailure s = some i) (hpos : 0 < i.val)
    (hleft : passes (replace s i u) ⟨i.val - 1, by omega⟩ = false) :
    firstFailure (replace s i u) = some ⟨i.val - 1, by omega⟩ := by
  apply firstFailure_of_failed_prefix
  · exact hleft
  · exact replacement_prefix_before_left hn s i u hi

theorem replacement_prefix_at_selected {n : ℕ} (hn : 2 ≤ n)
    (s : ChainState n) (i : Fin n) (u : Draw)
    (hi : firstFailure s = some i)
    (hleft : ∀ j : Fin n, j.val + 1 = i.val → passes (replace s i u) j = true) :
    PrefixHolds (replace s i u) i.val := by
  intro j hj
  by_cases heq : j.val + 1 = i.val
  · exact hleft j heq
  · rw [replace_pass_unchanged hn s i j u (Or.inl (by omega))]
    exact selected_prefix s i hi j hj

theorem replacement_stays {n : ℕ} (hn : 2 ≤ n)
    (s : ChainState n) (i : Fin n) (u : Draw)
    (hi : firstFailure s = some i)
    (hleft : ∀ j : Fin n, j.val + 1 = i.val → passes (replace s i u) j = true)
    (hself : passes (replace s i u) i = false) :
    firstFailure (replace s i u) = some i := by
  exact firstFailure_of_failed_prefix _ i hself
    (replacement_prefix_at_selected hn s i u hi hleft)

theorem replacement_prefix_through_selected {n : ℕ} (hn : 2 ≤ n)
    (s : ChainState n) (i : Fin n) (u : Draw)
    (hi : firstFailure s = some i)
    (hleft : ∀ j : Fin n, j.val + 1 = i.val → passes (replace s i u) j = true)
    (hself : passes (replace s i u) i = true) :
    PrefixHolds (replace s i u) (i.val + 1) := by
  intro j hj
  by_cases heq : j = i
  · simpa [heq] using hself
  · exact replacement_prefix_at_selected hn s i u hi hleft j (by
      have hne : j.val ≠ i.val := fun h => heq (Fin.ext h)
      omega)

end MTChainFormal
