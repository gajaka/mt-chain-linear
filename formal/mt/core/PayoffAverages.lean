module

public import ActualStep
public import CompletionExpect

@[expose] public section

set_option autoImplicit false

namespace MTChainFormal

open scoped BigOperators
open Filtering ProductFiltering ActualScan TailScan ActualStep PotentialAlgebra ScanBounds

@[simp] theorem average_deepZeroPayoff (m : ℕ) (d r : ℝ)
    (u v : Fin 3) (t : Fin 4) :
    average m (fun w last => deepZeroPayoff m d r w last u v t) = deepZeroStep m d r u v t := by
  by_cases hu : u = 0
  · by_cases hv : v = 0
    · simp [deepZeroPayoff, deepZeroStep, hu, hv, average_zeroPayoff]
    · simp [deepZeroPayoff, deepZeroStep, hu, hv, average_const]
  · simp [deepZeroPayoff, deepZeroStep, hu, average_const]

@[simp] theorem average_middlePayoff (m : ℕ) (d : ℝ) (v : Fin 3) (t : Fin 4) :
    average m (fun w last => middlePayoff m d w last v t) = middleStep m d v t := by
  by_cases hv : v = 0
  · by_cases ht : t = 1
    · simp [middlePayoff, middleStep, hv, ht, average_const]
    · simp [middlePayoff, middleStep, hv, ht, average_zeroPayoff]
  · by_cases hv1 : v = 1
    · simp [middlePayoff, middleStep, hv1, average_onePayoff]
    · simp [middlePayoff, middleStep, hv, hv1, average_const]

@[simp] theorem average_strongPayoff (m : ℕ) (d : ℝ)
    (u v : Fin 3) (t : Fin 4) :
    average m (fun w last => strongPayoff m d w last u v t) = strongStep m d u v t := by
  by_cases hu : u = 0
  · by_cases hv : v = 0
    · simp [strongPayoff, strongStep, hu, hv, average_zeroPayoff]
    · simp [strongPayoff, strongStep, hu, hv, average_const]
  · by_cases hu1 : u = 1
    · simp [strongPayoff, strongStep, hu1]
    · simp [strongPayoff, strongStep, hu, hu1, average_const]

@[simp] theorem average_weakPayoff (m : ℕ) (d : ℝ)
    (u v : Fin 3) (t : Fin 4) :
    average m (fun w last => weakPayoff m d w last u v t) = weakStep m d u v t := by
  by_cases hu : u = 1
  · simp only [weakPayoff, weakStep, hu, ite_true]
    exact average_middlePayoff m d v t
  · simp [weakPayoff, weakStep, hu, average_const]

theorem drawAverage_eq_average36 (f : Fin 3 → Fin 3 → Fin 4 → ℝ) :
    drawAverage (fun u => f u.1 u.2.1 u.2.2) = average36 f := by
  simp only [drawAverage, average36, Fintype.sum_prod_type, Finset.sum_div]
  apply Finset.sum_congr rfl
  intro u _
  apply Finset.sum_congr rfl
  intro v _
  apply Finset.sum_congr rfl
  intro t _
  ring

/-- The actual completion law, not an assumed fresh-tail law, pays for the scan. -/
theorem completed_step_le_payoff {n : ℕ} (q : PrefixDatum n) (hq : ValidDatum q)
    (m : ℕ) (hm : q.1.val + 1 + m + 1 = n)
    (f : Word m → Fin 4 → Fin 3 → Fin 3 → Fin 4 → ℝ)
    (hpoint : ∀ s, Agrees (readCoords (q.1.val + 1)) (toCoords q.2) (toCoords s) →
      ∀ u : Draw, localPotential (replace s q.1 u) ≤
        f (lettersFrom s (q.1.val + 1) m hm) (lastTactic s (by omega)) u.1 u.2.1 u.2.2) :
    completionMean q (fun s => drawAverage (fun u => localPotential (replace s q.1 u))) ≤
      average36 (fun u v t => average m (fun w last => f w last u v t)) := by
  rw [completionMean_drawAverage]
  calc
    _ ≤ drawAverage (fun u => completionMean q (fun s =>
      f (lettersFrom s (q.1.val + 1) m hm) (lastTactic s (by omega)) u.1 u.2.1 u.2.2)) := by
      apply drawAverage_mono
      intro u
      exact completionMean_mono q hq _ _ fun s hs => hpoint s hs u
    _ = _ := by
      have ht (u : Draw) : completionMean q (fun s =>
          f (lettersFrom s (q.1.val + 1) m hm) (lastTactic s (by omega)) u.1 u.2.1 u.2.2) =
          average m (fun w last => f w last u.1 u.2.1 u.2.2) :=
        TailLaw.completion_tail_average q m hm (fun w last => f w last u.1 u.2.1 u.2.2)
      simp_rw [ht]
      exact drawAverage_eq_average36 (fun u v t => average m (fun w last => f w last u v t))

end MTChainFormal
