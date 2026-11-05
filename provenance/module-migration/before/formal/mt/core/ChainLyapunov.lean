import ChainKernel
import Features

set_option autoImplicit false

namespace MTChainFormal

open scoped BigOperators

@[simp] theorem drawAverage_add (f g : Draw → ℝ) :
    drawAverage (fun u => f u + g u) = drawAverage f + drawAverage g := by
  simp [drawAverage, mul_add, Finset.sum_add_distrib]

@[simp] theorem drawAverage_sub (f g : Draw → ℝ) :
    drawAverage (fun u => f u - g u) = drawAverage f - drawAverage g := by
  simp [drawAverage, mul_sub, Finset.sum_sub_distrib]

@[simp] theorem drawAverage_mul (c : ℝ) (f : Draw → ℝ) :
    drawAverage (fun u => c * f u) = c * drawAverage f := by
  simp only [drawAverage, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro u _
  ring

theorem drawAverage_eq_sum_div (f : Draw → ℝ) :
    drawAverage f = (∑ u, f u) / 36 := by
  simp only [drawAverage, Finset.sum_div]
  apply Finset.sum_congr rfl
  intro u _
  ring

theorem expected_potential_decomposition {n : ℕ} (s : ChainState n) (i : Fin n) :
    drawAverage (fun u => chainPotential (replace s i u)) =
      256 * (n : ℝ) * ((n : ℝ) - drawAverage
        (fun u => (barrierHeight (replace s i u) : ℝ))) +
      drawAverage (fun u => localPotential (replace s i u)) := by
  simp only [chainPotential, PotentialAlgebra.totalValue, drawAverage_add,
    drawAverage_mul, drawAverage_sub, drawAverage_const]

theorem exceptional_potential_drift {n : ℕ} (hn : 2 ≤ n)
    (s : ChainState n) (i : Fin n) (hi : firstFailure s = some i)
    (he : i.val = 0 ∨ value s (i.val - 1) = 2) :
    drawAverage (fun u => chainPotential (replace s i u)) ≤ chainPotential s - 1 := by
  have hbar := barrierHeight_average_advance hn s i hi he
  rw [← drawAverage_eq_sum_div] at hbar
  have hlocal : drawAverage (fun u => localPotential (replace s i u)) ≤ 54 * (n : ℝ) := by
    calc
      _ ≤ drawAverage (fun _ => 54 * (n : ℝ)) :=
        drawAverage_mono (fun u => localPotential_le hn (replace s i u))
      _ = _ := drawAverage_const _
  have hnonneg := localPotential_nonneg s
  have hnreal : (2 : ℝ) ≤ n := by exact_mod_cast hn
  rw [expected_potential_decomposition]
  dsimp only [chainPotential, PotentialAlgebra.totalValue]
  nlinarith

theorem potential_drift_of_local_drift {n : ℕ} (hn : 2 ≤ n)
    (s : ChainState n) (i : Fin n) (hi : firstFailure s = some i)
    (hlocal : drawAverage (fun u => localPotential (replace s i u)) ≤ localPotential s - 1) :
    drawAverage (fun u => chainPotential (replace s i u)) ≤ chainPotential s - 1 := by
  have hbar : (barrierHeight s : ℝ) ≤
      drawAverage (fun u => (barrierHeight (replace s i u) : ℝ)) := by
    calc
      _ = drawAverage (fun _ => (barrierHeight s : ℝ)) := (drawAverage_const _).symm
      _ ≤ _ := drawAverage_mono fun u => by
        exact_mod_cast barrierHeight_mono_replace hn s i u hi
  rw [expected_potential_decomposition]
  dsimp only [chainPotential, PotentialAlgebra.totalValue]
  have hnreal : (0 : ℝ) ≤ n := Nat.cast_nonneg _
  nlinarith

end MTChainFormal
