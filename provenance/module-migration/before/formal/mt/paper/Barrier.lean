import Mathlib.Tactic

set_option autoImplicit false

namespace MTChainProof.Barriers

/-- Infinite indexing avoids endpoint arithmetic in the local invariant.
    Every finite chain embeds by retaining its fixed endpoint coordinates. -/
structure State where
  threshold : ℕ → Fin 3
  weak : ℕ → Bool

def Pass (s : State) (j : ℕ) : Prop :=
  if s.weak j then s.threshold j = s.threshold (j + 1)
  else s.threshold (j + 1) ≤ s.threshold j

def Prefix (s : State) (length : ℕ) : Prop :=
  ∀ j < length, Pass s j

/-- A simultaneous full-footprint replacement. The barrier theorem only uses
    updates to its right, so its protected incoming coordinate is unchanged. -/
def update (s : State) (i : ℕ) (x y : Fin 3) (weak : Bool) : State where
  threshold j := if j = i then x else if j = i + 1 then y else s.threshold j
  weak j := if j = i then weak else s.weak j

def Barrier (s : State) (j : ℕ) : Prop :=
  Prefix s (j + 1) ∧ s.weak j = false ∧ s.threshold j = 2

theorem update_preserves_strictly_before (s : State) (i j : ℕ)
    (x y : Fin 3) (weak : Bool) (h : j + 1 < i) :
    Pass (update s i x y weak) j ↔ Pass s j := by
  have hji : j ≠ i := by omega
  have hji1 : j ≠ i + 1 := by omega
  have hj1i : j + 1 ≠ i := by omega
  simp [Pass, update, hji, hji1, hj1i]

/-- A strong bridge with maximal incoming threshold remains true under every
    update to its right, including changes to its outgoing threshold. -/
theorem barrier_preserved (s : State) (i j : ℕ)
    (x y : Fin 3) (weak : Bool) (hb : Barrier s j) (hji : j < i) :
    Barrier (update s i x y weak) j := by
  have hne : j ≠ i := by omega
  have hne1 : j ≠ i + 1 := by omega
  have hw : (update s i x y weak).weak j = false := by
    simpa [update, hne] using hb.2.1
  have ht : (update s i x y weak).threshold j = 2 := by
    simpa [update, hne, hne1] using hb.2.2
  refine ⟨?_, hw, ht⟩
  intro k hk
  by_cases hkj : k = j
  · subst k
    simp only [Pass, hw, Bool.false_eq_true, ↓reduceIte, ht]
    exact Fin.le_last _
  · have hki : k + 1 < i := by omega
    exact (update_preserves_strictly_before s i k x y weak hki).mpr
      (hb.1 k hk)

theorem failed_index_after_barrier (s : State) (i j : ℕ)
    (hb : Barrier s j) (hf : ¬ Pass s i) : j < i := by
  by_contra h
  exact hf (hb.1 i (by omega))

/-- Redrawing a maximal incoming threshold and a strong profile installs a
    barrier when every preceding bridge passes. The old incoming value is
    already maximal, so this redraw leaves the old prefix unchanged. -/
theorem install_barrier (s : State) (i : ℕ) (y : Fin 3)
    (hp : Prefix s i) (ht : s.threshold i = 2) :
    Barrier (update s i 2 y false) i := by
  refine ⟨?_, by simp [update], by simp [update]⟩
  intro j hj
  by_cases hji : j = i
  · subst j
    simp only [Pass, update, ↓reduceIte, Bool.false_eq_true]
    exact Fin.le_last _
  · have hji1 : j ≠ i + 1 := by omega
    have ha : (update s i 2 y false).threshold j = s.threshold j := by
      simp [update, hji, hji1]
    have hb : (update s i 2 y false).threshold (j + 1) =
        s.threshold (j + 1) := by
      by_cases heq : j + 1 = i
      · simp [update, heq, ht]
      · simp [update, heq, hji]
    have hw : (update s i 2 y false).weak j = s.weak j := by
      simp [update, hji]
    simpa only [Pass, ha, hb, hw] using hp j (by omega)

/-- Permanent-prefix protection holds for every failed-event schedule, not
    only the least-failed schedule. Stopped steps are represented by equality. -/
theorem barrier_invariant (states : ℕ → State) (j : ℕ)
    (hstep : ∀ t, states (t + 1) = states t ∨
      ∃ i x y weak, ¬ Pass (states t) i ∧
        states (t + 1) = update (states t) i x y weak)
    (hzero : Barrier (states 0) j) :
    ∀ t, Barrier (states t) j := by
  intro t
  induction t with
  | zero => exact hzero
  | succ t ih =>
    rcases hstep t with heq | ⟨i, x, y, weak, hf, heq⟩
    · simpa only [heq] using ih
    · rw [heq]
      exact barrier_preserved (states t) i j x y weak ih
        (failed_index_after_barrier (states t) i j ih hf)

end MTChainProof.Barriers

#print axioms MTChainProof.Barriers.barrier_preserved
#print axioms MTChainProof.Barriers.install_barrier
#print axioms MTChainProof.Barriers.barrier_invariant
