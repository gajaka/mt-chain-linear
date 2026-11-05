module

public import PotentialAlgebra
public import Mathlib.Data.Fin.Tuple.Basic
public import Mathlib.Data.Fintype.BigOperators
public import Mathlib.Tactic

@[expose] public section

set_option autoImplicit false

namespace MTChainFormal.TailScan

open scoped BigOperators
open PotentialAlgebra

abbrev Letter := Fin 3 × Fin 4
abbrev Word (m : ℕ) := Fin m → Letter

/-- A deterministic forward reveal of a finite suffix. The last outgoing
    threshold is fixed at zero, while its tactic remains a fresh label. -/
noncomputable def zeroPayoff : (m : ℕ) → ℝ → ℝ → Word m → Fin 4 → ℝ
  | 0, _, _, _, _ => 0
  | m + 1, d, r, w, last =>
      if (w 0).1 = 0 then zeroPayoff m d (r + 1) (Fin.tail w) last
      else localValue d r 1

noncomputable def onePayoff : (m : ℕ) → ℝ → Word m → Fin 4 → ℝ
  | 0, d, _, last => if last = 1 then localValue d 0 0 else 0
  | m + 1, d, w, last =>
      if (w 0).1 = 0 then
        if (w 0).2 = 1 then localValue d 0 0
        else zeroPayoff m d 1 (Fin.tail w) last
      else if (w 0).1 = 1 then onePayoff m (d + 1) (Fin.tail w) last
      else localValue d 0 0

noncomputable def average (m : ℕ) (f : Word m → Fin 4 → ℝ) : ℝ :=
  (∑ w, ∑ last, f w last) / ((12 : ℝ) ^ m * 4)

theorem sum_word_succ (m : ℕ) (f : Word (m + 1) → ℝ) :
    (∑ w, f w) = ∑ a : Letter, ∑ w : Word m, f (Fin.cons a w) := by
  classical
  rw [← (Fin.consEquiv (fun _ : Fin (m + 1) => Letter)).sum_comp]
  rw [Fintype.sum_prod_type]
  rfl

theorem average_const (m : ℕ) (b : ℝ) : average m (fun _ _ => b) = b := by
  simp [average, Fintype.card_prod]
  field_simp

theorem average_succ (m : ℕ) (f : Word (m + 1) → Fin 4 → ℝ) :
    average (m + 1) f =
      (∑ a : Letter, average m (fun w last => f (Fin.cons a w) last)) / 12 := by
  unfold average
  rw [sum_word_succ]
  rw [← Finset.sum_div, pow_succ]
  ring

theorem average_zeroPayoff (m : ℕ) (d r : ℝ) :
    average m (zeroPayoff m d r) = zeroScanValue m d r := by
  induction m generalizing d r with
  | zero => simp [average, zeroPayoff, zeroScanValue]
  | succ m ih =>
      rw [average_succ]
      have hpoint (a : Letter) :
          average m (fun w last => zeroPayoff (m + 1) d r (Fin.cons a w) last) =
            if a.1 = 0 then zeroScanValue m d (r + 1) else localValue d r 1 := by
        by_cases ha : a.1 = 0
        · simpa [zeroPayoff, ha] using ih d (r + 1)
        · simp [zeroPayoff, ha, average_const]
      simp_rw [hpoint]
      norm_num [Fintype.sum_prod_type, Fin.sum_univ_succ, zeroScanValue]
      ring

theorem average_onePayoff (m : ℕ) (d : ℝ) :
    average m (onePayoff m d) = oneScanValue m d := by
  induction m generalizing d with
  | zero =>
      simp [average, onePayoff, oneScanValue, localValue]
      ring
  | succ m ih =>
      rw [average_succ]
      have hpoint (a : Letter) :
          average m (fun w last => onePayoff (m + 1) d (Fin.cons a w) last) =
            if a.1 = 0 then
              if a.2 = 1 then localValue d 0 0 else zeroScanValue m d 1
            else if a.1 = 1 then oneScanValue m (d + 1)
            else localValue d 0 0 := by
        by_cases h0 : a.1 = 0
        · by_cases ht : a.2 = 1
          · simp [onePayoff, h0, ht, average_const]
          · simpa [onePayoff, h0, ht] using average_zeroPayoff m d 1
        · by_cases h1 : a.1 = 1
          · simpa [onePayoff, h0, h1] using ih (d + 1)
          · simp [onePayoff, h0, h1, average_const]
      simp_rw [hpoint]
      norm_num [Fintype.sum_prod_type, Fin.sum_univ_succ, oneScanValue]
      ring

theorem average_zeroPayoff_le (m : ℕ) (d r : ℝ) (hd : 0 ≤ d) (hr : 0 ≤ r) :
    average m (zeroPayoff m d r) ≤ zeroScanBound d r := by
  rw [average_zeroPayoff]
  exact zeroScanValue_le m d r hd hr

theorem average_onePayoff_le (m : ℕ) (d : ℝ) (hd : 0 ≤ d) :
    average m (onePayoff m d) ≤ oneScanBound d := by
  rw [average_onePayoff]
  exact oneScanValue_le m d hd

end MTChainFormal.TailScan
