module

public import PotentialAlgebra

@[expose] public section

set_option autoImplicit false

namespace MTChainFormal.ScanBounds

open scoped BigOperators
open PotentialAlgebra

/-- The actual 36 uniform primitive outcomes, including the three strong labels. -/
noncomputable def average36 (f : Fin 3 → Fin 3 → Fin 4 → ℝ) : ℝ :=
  (∑ u, ∑ v, ∑ t, f u v t) / 36

theorem average36_mono (f g : Fin 3 → Fin 3 → Fin 4 → ℝ)
    (h : ∀ u v t, f u v t ≤ g u v t) : average36 f ≤ average36 g := by
  unfold average36
  apply div_le_div_of_nonneg_right _ (by norm_num)
  exact Finset.sum_le_sum fun u _ => Finset.sum_le_sum fun v _ =>
    Finset.sum_le_sum fun t _ => h u v t

def zeroIncomingRow (b : ℝ) (v : Fin 3) : ℝ := if v = 0 then b + 3 else b

def middleRow (b : ℝ) (v : Fin 3) (t : Fin 4) : ℝ :=
  if v = 0 then (if t = 1 then b else b + 36)
  else if v = 1 then b + 66 else b

def deepZeroRow (b : ℝ) (u v : Fin 3) (_t : Fin 4) : ℝ :=
  if u = 0 then zeroIncomingRow b v else b - 2

def strongRow (b : ℝ) (u v : Fin 3) (t : Fin 4) : ℝ :=
  if u = 0 then zeroIncomingRow b v
  else if u = 1 then middleRow b v t else b - 35

def weakRow (b : ℝ) (u v : Fin 3) (t : Fin 4) : ℝ :=
  if u = 1 then middleRow b v t else b - 35

theorem average_deepZeroRow (b : ℝ) : average36 (deepZeroRow b) = b - 1 := by
  unfold average36
  norm_num [Fin.sum_univ_succ, deepZeroRow, zeroIncomingRow]
  ring

theorem average_strongRow (b : ℝ) : average36 (strongRow b) = b - 1 := by
  unfold average36
  norm_num [Fin.sum_univ_succ, strongRow, zeroIncomingRow, middleRow]
  ring

theorem average_weakRow (b : ℝ) : average36 (weakRow b) = b - 13 := by
  unfold average36
  norm_num [Fin.sum_univ_succ, weakRow, middleRow]
  ring

/-- A real local value after an interior deep-zero redraw and finite fresh scan. -/
noncomputable def deepZeroStep (m : ℕ) (d r : ℝ)
    (u v : Fin 3) (_t : Fin 4) : ℝ :=
  if u = 0 then
    if v = 0 then zeroScanValue m d (r + 1) else localValue d r 1
  else localValue d (r - 1) 1

/-- The U=1 branch of either one-mode row, before the remaining finite scan. -/
noncomputable def middleStep (m : ℕ) (d : ℝ) (v : Fin 3) (t : Fin 4) : ℝ :=
  if v = 0 then
    if t = 1 then localValue d 0 0 else zeroScanValue m d 1
  else if v = 1 then oneScanValue m (d + 1) else localValue d 0 0

noncomputable def strongStep (m : ℕ) (d : ℝ)
    (u v : Fin 3) (t : Fin 4) : ℝ :=
  if u = 0 then
    if v = 0 then zeroScanValue m (d - 1) 2 else localValue (d - 1) 1 1
  else if u = 1 then middleStep m d v t else localValue (d - 1) 0 0

noncomputable def weakStep (m : ℕ) (d : ℝ)
    (u v : Fin 3) (t : Fin 4) : ℝ :=
  if u = 1 then middleStep m d v t else localValue (d - 1) 0 0

theorem deepZeroStep_le_row (m : ℕ) (d r : ℝ)
    (hd : 0 ≤ d) (hr : 2 ≤ r) (u v : Fin 3) (t : Fin 4) :
    deepZeroStep m d r u v t ≤ deepZeroRow (localValue d r 1) u v t := by
  have h := zeroScanValue_le m d (r + 1) hd (by linarith)
  dsimp [zeroScanBound] at h
  fin_cases u <;> fin_cases v <;>
    norm_num [deepZeroStep, deepZeroRow, zeroIncomingRow, localValue] <;> linarith

theorem middleStep_le_row (m : ℕ) (d : ℝ)
    (hd : 0 ≤ d) (v : Fin 3) (t : Fin 4) :
    middleStep m d v t ≤ middleRow (localValue d 0 0) v t := by
  have hz := zeroScanValue_le m d 1 hd (by norm_num)
  have ho := oneScanValue_le m (d + 1) (by linarith)
  dsimp [zeroScanBound, oneScanBound] at hz ho
  fin_cases v <;> fin_cases t <;>
    norm_num [middleStep, middleRow, localValue] <;> linarith

theorem strongStep_le_row (m : ℕ) (d : ℝ)
    (hd : 1 ≤ d) (u v : Fin 3) (t : Fin 4) :
    strongStep m d u v t ≤ strongRow (localValue d 0 0) u v t := by
  by_cases hu0 : u = 0
  · subst u
    have h := zeroScanValue_le m (d - 1) 2 (by linarith) (by norm_num)
    dsimp [zeroScanBound] at h
    fin_cases v <;>
      norm_num [strongStep, strongRow, zeroIncomingRow, localValue] <;> linarith
  · by_cases hu1 : u = 1
    · simp only [strongStep, strongRow, hu1, ↓reduceIte]
      exact middleStep_le_row m d (by linarith) v t
    · simp [strongStep, strongRow, hu0, hu1, localValue]
      linarith

theorem weakStep_le_row (m : ℕ) (d : ℝ)
    (hd : 1 ≤ d) (u v : Fin 3) (t : Fin 4) :
    weakStep m d u v t ≤ weakRow (localValue d 0 0) u v t := by
  by_cases hu1 : u = 1
  · simp only [weakStep, weakRow, hu1, ↓reduceIte]
    exact middleStep_le_row m d (by linarith) v t
  · simp [weakStep, weakRow, hu1, localValue]
    linarith

theorem average_deepZeroStep_le (m : ℕ) (d r : ℝ) (hd : 0 ≤ d) (hr : 2 ≤ r) :
    average36 (deepZeroStep m d r) ≤ localValue d r 1 - 1 := by
  calc
    _ ≤ average36 (deepZeroRow (localValue d r 1)) :=
      average36_mono _ _ (deepZeroStep_le_row m d r hd hr)
    _ = _ := average_deepZeroRow _

theorem average_strongStep_le (m : ℕ) (d : ℝ) (hd : 1 ≤ d) :
    average36 (strongStep m d) ≤ localValue d 0 0 - 1 := by
  calc
    _ ≤ average36 (strongRow (localValue d 0 0)) :=
      average36_mono _ _ (strongStep_le_row m d hd)
    _ = _ := average_strongRow _

theorem average_weakStep_le (m : ℕ) (d : ℝ) (hd : 1 ≤ d) :
    average36 (weakStep m d) ≤ localValue d 0 0 - 13 := by
  calc
    _ ≤ average36 (weakRow (localValue d 0 0)) :=
      average36_mono _ _ (weakStep_le_row m d hd)
    _ = _ := average_weakRow _

/-- At a zero boundary, shifting d by one gives exactly the same local model. -/
theorem average_zeroBoundaryStep_le (m : ℕ) (d : ℝ) (hd : 0 ≤ d) :
    average36 (strongStep m (d + 1)) ≤ localValue d 1 1 - 1 := by
  have h := average_strongStep_le m (d + 1) (by linarith)
  dsimp [localValue] at h ⊢
  linarith

def lastStrongStep (b : ℝ) (u : Fin 3) (_v : Fin 3) (t : Fin 4) : ℝ :=
  if u = 0 then 0 else if u = 1 then (if t = 1 then b else 0) else b - 35

def lastWeakStep (b : ℝ) (u : Fin 3) (_v : Fin 3) (t : Fin 4) : ℝ :=
  if u = 1 then (if t = 1 then b else 0) else b - 35

theorem average_lastStrongStep (b : ℝ) :
    average36 (lastStrongStep b) = (0 + b / 4 + (b - 35)) / 3 := by
  unfold average36
  norm_num [Fin.sum_univ_succ, lastStrongStep]
  ring

theorem average_lastWeakStep (b : ℝ) :
    average36 (lastWeakStep b) = ((b - 35) + b / 4 + (b - 35)) / 3 := by
  unfold average36
  norm_num [Fin.sum_univ_succ, lastWeakStep]
  ring

theorem average_lastStrongStep_le (b : ℝ) (hb : 0 ≤ b) :
    average36 (lastStrongStep b) ≤ b - 1 := by
  rw [average_lastStrongStep]
  exact last_regular_strong_drift b hb

theorem average_lastWeakStep_le (b : ℝ) (hb : 0 ≤ b) :
    average36 (lastWeakStep b) ≤ b - 1 := by
  rw [average_lastWeakStep]
  exact last_regular_weak_drift b hb

end MTChainFormal.ScanBounds
