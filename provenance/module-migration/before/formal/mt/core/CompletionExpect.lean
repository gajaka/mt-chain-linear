import TailLaw
import ObservedFeatures
import ChainLyapunov

set_option autoImplicit false

namespace MTChainFormal

open scoped BigOperators
open Filtering ProductFiltering ObservedFeatures

noncomputable def completionMean {n : ℕ} (q : PrefixDatum n) (f : ChainState n → ℝ) : ℝ :=
  ∑ s, rawCompletion q s * f s

theorem completionMean_const {n : ℕ} (q : PrefixDatum n) (a : ℝ) :
    completionMean q (fun _ => a) = a := by
  simp only [completionMean, ← Finset.sum_mul, rawCompletion_sum, one_mul]

theorem completionMean_mono {n : ℕ} (q : PrefixDatum n) (hq : ValidDatum q)
    (f g : ChainState n → ℝ)
    (h : ∀ s, Agrees (readCoords (q.1.val + 1)) (toCoords q.2) (toCoords s) → f s ≤ g s) :
    completionMean q f ≤ completionMean q g := by
  apply Finset.sum_le_sum
  intro s _
  by_cases hs : rawCompletion q s = 0
  · simp [hs]
  · have ho := rawCompletion_support q hq s hs
    exact mul_le_mul_of_nonneg_left (h s ((observeRaw_fiber q hq s).mp ho))
      (rawCompletion_nonneg q s)

theorem completionMean_congr {n : ℕ} (q : PrefixDatum n) (hq : ValidDatum q)
    (f g : ChainState n → ℝ)
    (h : ∀ s, Agrees (readCoords (q.1.val + 1)) (toCoords q.2) (toCoords s) → f s = g s) :
    completionMean q f = completionMean q g := by
  apply le_antisymm
  · exact completionMean_mono q hq f g (fun s hs => (h s hs).le)
  · exact completionMean_mono q hq g f (fun s hs => (h s hs).ge)

theorem completionMean_add {n : ℕ} (q : PrefixDatum n) (f g : ChainState n → ℝ) :
    completionMean q (fun s => f s + g s) = completionMean q f + completionMean q g := by
  simp [completionMean, mul_add, Finset.sum_add_distrib]

theorem completionMean_sub {n : ℕ} (q : PrefixDatum n) (f g : ChainState n → ℝ) :
    completionMean q (fun s => f s - g s) = completionMean q f - completionMean q g := by
  simp [completionMean, mul_sub, Finset.sum_sub_distrib]

theorem completionMean_mul {n : ℕ} (q : PrefixDatum n) (c : ℝ) (f : ChainState n → ℝ) :
    completionMean q (fun s => c * f s) = c * completionMean q f := by
  simp only [completionMean, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro s _
  ring

theorem completionMean_drawAverage {n : ℕ} (q : PrefixDatum n)
    (f : ChainState n → Draw → ℝ) :
    completionMean q (fun s => drawAverage (f s)) =
      drawAverage (fun u => completionMean q (fun s => f s u)) := by
  unfold completionMean drawAverage
  simp only [Finset.mul_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro u _
  apply Finset.sum_congr rfl
  intro s _
  ring

theorem completionMean_barrierHeight {n : ℕ} (q : PrefixDatum n) (hq : ValidDatum q) :
    completionMean q (fun s => (barrierHeight s : ℝ)) = (barrierHeight q.2 : ℝ) := by
  calc
    _ = completionMean q (fun _ => (barrierHeight q.2 : ℝ)) :=
      completionMean_congr q hq _ _ fun s hs => by
        rw [barrierHeight_congr q.2 s q.1 hq.1 hs]
    _ = _ := completionMean_const _ _

theorem completionMean_localPotential {n : ℕ} (q : PrefixDatum n) (hq : ValidDatum q) :
    completionMean q localPotential = localPotential q.2 := by
  calc
    _ = completionMean q (fun _ => localPotential q.2) :=
      completionMean_congr q hq _ _ fun s hs => localPotential_congr q.2 s q.1 hq.1 hs
    _ = _ := completionMean_const _ _

theorem completionMean_chainPotential {n : ℕ} (q : PrefixDatum n) (hq : ValidDatum q) :
    completionMean q chainPotential = chainPotential q.2 := by
  calc
    _ = completionMean q (fun _ => chainPotential q.2) :=
      completionMean_congr q hq _ _ fun s hs => chainPotential_congr q.2 s q.1 hq.1 hs
    _ = _ := completionMean_const _ _

theorem completed_potential_drift_of_local_drift {n : ℕ} (hn : 2 ≤ n)
    (q : PrefixDatum n) (hq : ValidDatum q)
    (hlocal : completionMean q (fun s => drawAverage
      (fun u => localPotential (replace s q.1 u))) ≤ localPotential q.2 - 1) :
    completionMean q (fun s => drawAverage
      (fun u => chainPotential (replace s q.1 u))) ≤ chainPotential q.2 - 1 := by
  have hbar : (barrierHeight q.2 : ℝ) ≤ completionMean q (fun s => drawAverage
      (fun u => (barrierHeight (replace s q.1 u) : ℝ))) := by
    calc
      _ = completionMean q (fun _ => (barrierHeight q.2 : ℝ)) := (completionMean_const _ _).symm
      _ ≤ _ := completionMean_mono q hq _ _ fun s hs => by
        have hi := firstFailure_eq_of_agrees q.2 s q.1 hq.1 _ le_rfl hs
        have heq := barrierHeight_congr q.2 s q.1 hq.1 hs
        calc
          _ = drawAverage (fun _ => (barrierHeight q.2 : ℝ)) := (drawAverage_const _).symm
          _ ≤ _ := drawAverage_mono fun u => by
            have hm := barrierHeight_mono_replace hn s q.1 u hi
            rw [heq] at hm
            exact_mod_cast hm
  simp_rw [expected_potential_decomposition]
  rw [completionMean_add, completionMean_mul, completionMean_sub, completionMean_const]
  dsimp only [chainPotential, PotentialAlgebra.totalValue]
  have hnreal : (0 : ℝ) ≤ n := Nat.cast_nonneg _
  nlinarith

theorem completed_exceptional_potential_drift {n : ℕ} (hn : 2 ≤ n)
    (q : PrefixDatum n) (hq : ValidDatum q)
    (he : q.1.val = 0 ∨ value q.2 (q.1.val - 1) = 2) :
    completionMean q (fun s => drawAverage
      (fun u => chainPotential (replace s q.1 u))) ≤ chainPotential q.2 - 1 := by
  calc
    _ ≤ completionMean q (fun s => chainPotential s - 1) :=
      completionMean_mono q hq _ _ fun s hs => by
        apply exceptional_potential_drift hn s q.1
          (firstFailure_eq_of_agrees q.2 s q.1 hq.1 _ le_rfl hs)
        rcases he with hfirst | hprev
        · exact Or.inl hfirst
        · right
          rw [value_eq_of_agrees q.2 s _ hs _ (by omega)]
          exact hprev
    _ = _ := by rw [completionMean_sub, completionMean_chainPotential q hq, completionMean_const]

end MTChainFormal
