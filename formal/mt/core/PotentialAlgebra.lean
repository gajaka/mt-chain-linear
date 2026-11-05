module

public import Mathlib.Tactic

@[expose] public section

set_option autoImplicit false

namespace MTChainFormal.PotentialAlgebra

/-- The zero-mode correction is part of the value, not an episode assumption. -/
def localValue (d r z : ℝ) : ℝ := 35 * d + 2 * r + 33 * z

def zeroScanBound (d r : ℝ) : ℝ := 35 * d + 2 * r + 34

def oneScanBound (d : ℝ) : ℝ := 35 * d + 31

def totalValue (n f b : ℝ) : ℝ := 256 * n * (n - f) + b

/-- The affine bound is closed under one more fresh zero-tail test. -/
theorem zeroScan_recurrence (d r : ℝ) :
    (2 / 3 : ℝ) * localValue d r 1 +
        (1 / 3 : ℝ) * zeroScanBound d (r + 1) = zeroScanBound d r := by
  unfold localValue zeroScanBound
  ring

/-- The descending zero branch and equal-one branch close the second bound. -/
theorem oneScan_recurrence (d : ℝ) :
    (5 / 12 : ℝ) * localValue d 0 0 +
        (1 / 4 : ℝ) * zeroScanBound d 1 +
        (1 / 3 : ℝ) * oneScanBound (d + 1) = oneScanBound d := by
  unfold localValue zeroScanBound oneScanBound
  ring

theorem zeroScan_nonneg (d r : ℝ) (hd : 0 ≤ d) (hr : 0 ≤ r) :
    0 ≤ zeroScanBound d r := by
  unfold zeroScanBound
  positivity

theorem last_oneScan_bound (d : ℝ) (hd : 0 ≤ d) :
    (1 / 4 : ℝ) * localValue d 0 0 ≤ oneScanBound d := by
  unfold localValue oneScanBound
  linarith

/-- There are m fresh outgoing thresholds before the final fixed outgoing 0. -/
noncomputable def zeroScanValue : ℕ → ℝ → ℝ → ℝ
  | 0, _, _ => 0
  | m + 1, d, r =>
      (2 / 3 : ℝ) * localValue d r 1 +
      (1 / 3 : ℝ) * zeroScanValue m d (r + 1)

/-- The zero descent and equal-one continuations use the remaining finite tail. -/
noncomputable def oneScanValue : ℕ → ℝ → ℝ
  | 0, d => (1 / 4 : ℝ) * localValue d 0 0
  | m + 1, d =>
      (5 / 12 : ℝ) * localValue d 0 0 +
      (1 / 4 : ℝ) * zeroScanValue m d 1 +
      (1 / 3 : ℝ) * oneScanValue m (d + 1)

theorem zeroScanValue_le (m : ℕ) (d r : ℝ) (hd : 0 ≤ d) (hr : 0 ≤ r) :
    zeroScanValue m d r ≤ zeroScanBound d r := by
  induction m generalizing r with
  | zero =>
      simpa only [zeroScanValue] using zeroScan_nonneg d r hd hr
  | succ m ih =>
      have h := ih (r + 1) (by linarith)
      have heq := zeroScan_recurrence d r
      simp only [zeroScanValue]
      nlinarith

theorem oneScanValue_le (m : ℕ) (d : ℝ) (hd : 0 ≤ d) :
    oneScanValue m d ≤ oneScanBound d := by
  induction m generalizing d with
  | zero =>
      exact last_oneScan_bound d hd
  | succ m ih =>
      have hz := zeroScanValue_le m d 1 hd (by norm_num)
      have ho := ih (d + 1) (by linarith)
      have heq := oneScan_recurrence d
      simp only [oneScanValue]
      nlinarith

/-- Given U=0, V=0 is the one forward-scan branch. -/
theorem zero_incoming_row (b : ℝ) :
    ((b + 3) + b + b) / 3 = b + 1 := by ring

/-- The V=0 branch mixes a strong continuation and a weak failure. -/
theorem mixed_zero_outgoing_row (b : ℝ) :
    (3 / 4 : ℝ) * (b + 36) + (1 / 4 : ℝ) * b = b + 27 := by ring

/-- Given U=1, the three V branches have these continuation bounds. -/
theorem one_incoming_row (b : ℝ) :
    ((b + 27) + (b + 66) + b) / 3 = b + 31 := by ring

/-- A zero mode with at least two retained zeros has unit negative drift. -/
theorem zero_deep_drift (b : ℝ) :
    ((b + 1) + (b - 2) + (b - 2)) / 3 = b - 1 := by ring

/-- This row applies to the zero boundary at incoming 1 and strong-one mode. -/
theorem regular_strong_drift (b : ℝ) :
    ((b + 1) + (b + 31) + (b - 35)) / 3 = b - 1 := by ring

/-- A preceding weak equality gives more negative drift, not a missing case. -/
theorem regular_weak_drift (b : ℝ) :
    ((b - 35) + (b + 31) + (b - 35)) / 3 = b - 13 := by ring

theorem last_regular_strong_drift (b : ℝ) (hb : 0 ≤ b) :
    (0 + b / 4 + (b - 35)) / 3 ≤ b - 1 := by
  linarith

theorem last_regular_weak_drift (b : ℝ) (hb : 0 ≤ b) :
    ((b - 35) + b / 4 + (b - 35)) / 3 ≤ b - 1 := by
  linarith

theorem localValue_nonneg (d r z : ℝ)
    (hd : 0 ≤ d) (hr : 0 ≤ r) (hz : 0 ≤ z) :
    0 ≤ localValue d r z := by
  unfold localValue
  positivity

theorem localValue_le (n d r z : ℝ) (hn : 2 ≤ n)
    (hd : d ≤ n) (hr : r ≤ n) (hz : z ≤ 1) :
    localValue d r z ≤ 54 * n := by
  unfold localValue
  linarith

theorem totalValue_nonneg (n f b : ℝ) (hn : 0 ≤ n)
    (hf : f ≤ n) (hb : 0 ≤ b) : 0 ≤ totalValue n f b := by
  unfold totalValue
  have h : 0 ≤ n - f := sub_nonneg.mpr hf
  positivity

theorem totalValue_le_quadratic (n f b : ℝ) (hn : 2 ≤ n)
    (hf : 0 ≤ f) (hb : b ≤ 54 * n) :
    totalValue n f b ≤ 283 * n ^ 2 := by
  unfold totalValue
  have hn0 : 0 ≤ n := by linarith
  have hnf : 0 ≤ n * f := mul_nonneg hn0 hf
  nlinarith

/-- Scalar assembly after the actual chain proves its regular-row estimates. -/
theorem regular_supersolution (n f b nextF nextB : ℝ)
    (hn : 0 ≤ n) (hf : f ≤ nextF) (hb : nextB ≤ b - 1) :
    1 + totalValue n nextF nextB ≤ totalValue n f b := by
  unfold totalValue
  have h := mul_le_mul_of_nonneg_left hf hn
  nlinarith

/-- A probability at least 1/4 of a strict barrier advance pays every other row. -/
theorem exceptional_drift (n f b nextF nextB : ℝ)
    (hn : 2 ≤ n) (hb : 0 ≤ b)
    (hf : f + 1 / 4 ≤ nextF) (hnextB : nextB ≤ 54 * n) :
    totalValue n nextF nextB ≤ totalValue n f b - 10 * n := by
  unfold totalValue
  have hn0 : 0 ≤ n := by linarith
  have h := mul_le_mul_of_nonneg_left hf hn0
  nlinarith

theorem exceptional_supersolution (n f b nextF nextB : ℝ)
    (hn : 2 ≤ n) (hb : 0 ≤ b)
    (hf : f + 1 / 4 ≤ nextF) (hnextB : nextB ≤ 54 * n) :
    1 + totalValue n nextF nextB ≤ totalValue n f b := by
  have h := exceptional_drift n f b nextF nextB hn hb hf hnextB
  linarith

end MTChainFormal.PotentialAlgebra
