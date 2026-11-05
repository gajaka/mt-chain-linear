module

public import NeighborWitness
public import SeparableSequence

@[expose] public section

set_option autoImplicit false

namespace NeighborSeparation

open scoped BigOperators

theorem flux_absolute_upper (m : ℕ) (h : EdgeCosts) (hh : Nonnegative h) :
    (∑ j : Fin m, |flux h j.val|) ≤
      (13 / 2 : ℝ) * ∑ j : Fin (m + 1), meanEdge (h (j.val + 1)) := by
  have hlocal (j : ℕ) : |flux h j| ≤
      (15 / 4 : ℝ) * meanEdge (h (j + 1)) +
      (11 / 4 : ℝ) * meanEdge (h (j + 2)) := by
    exact (abs_sub _ _).trans (add_le_add
      (L_abs_le_mean _ (hh _)) (R_abs_le_mean _ (hh _)))
  have hsum := Finset.sum_le_sum
    (fun j (_ : j ∈ (Finset.univ : Finset (Fin m))) => hlocal j.val)
  simp only [Finset.sum_add_distrib, ← Finset.mul_sum] at hsum
  have hleft : (∑ j : Fin m, meanEdge (h (j.val + 1))) ≤
      ∑ j : Fin (m + 1), meanEdge (h (j.val + 1)) := by
    rw [Fin.sum_univ_castSucc]
    simp only [Fin.val_castSucc, Fin.val_last]
    exact le_add_of_nonneg_right (meanEdge_nonneg _ (hh _))
  have hright : (∑ j : Fin m, meanEdge (h (j.val + 2))) ≤
      ∑ j : Fin (m + 1), meanEdge (h (j.val + 1)) := by
    rw [Fin.sum_univ_succ]
    simp only [Fin.val_zero, Fin.val_succ]
    have heq : (fun j : Fin m => meanEdge (h (j.val + 1 + 1))) =
        (fun j : Fin m => meanEdge (h (j.val + 2))) := by
      funext j
      congr 2
    rw [heq]
    exact le_add_of_nonneg_left (meanEdge_nonneg _ (hh _))
  linarith

theorem flux_budget_bound {n : ℕ} (hn : 6 ≤ n) (h : EdgeCosts) (δ : ℝ)
    (hh : Nonnegative h) (hd : BulkDrift n h δ) :
    δ * ((((n - 4) ^ 2 / 4 : ℕ) : ℝ)) ≤
      (13 / 2 : ℝ) * ∑ j : Fin (n - 3), meanEdge (h (j.val + 1)) := by
  have hlower := PotentialSeparation.sequence_absolute_budget (n - 4)
    (flux h) (fun j => |flux h j|) δ (by intro j _; exact le_rfl)
    (by intro j hj; exact flux_gradient hn h δ hd j hj)
  have hupp := flux_absolute_upper (n - 4) h hh
  rw [Fin.sum_univ_eq_sum_range (fun j => |flux h j|) (n - 4)] at hupp
  have heq : n - 4 + 1 = n - 3 := by omega
  rw [heq] at hupp
  exact hlower.trans hupp

end NeighborSeparation

#print axioms NeighborSeparation.flux_budget_bound
