module

public import KernelWork

@[expose] public section

set_option autoImplicit false

namespace MTChainFormal

open scoped BigOperators ENNReal

variable {S : Type*} [Fintype S]

/-- Stop at the first visit to a chosen set. Stopped states retain their state
    but accrue no subsequent cost, so no finiteness assumption is needed. -/
noncomputable def stoppedKernel (K : FiniteKernel S) (stop : S → Bool) : FiniteKernel S := by
  classical
  exact {
    weight := fun s t => if stop s then (if t = s then 1 else 0) else K.weight s t
    nonneg := by intro s t; split_ifs; norm_num; norm_num; exact K.nonneg s t
    sum_eq_one := by intro s; cases hs : stop s <;> simp [K.sum_eq_one]
  }

def stoppedCost (stop : S → Bool) (c : S → ℝ) (s : S) : ℝ :=
  if stop s then 0 else c s

theorem expect_stoppedKernel (K : FiniteKernel S) (stop : S → Bool)
    (f : S → ℝ) (s : S) :
    expect (stoppedKernel K stop) f s = if stop s then f s else expect K f s := by
  classical
  unfold expect stoppedKernel
  cases hs : stop s <;> simp [hs]

theorem stopped_supersolution (K : FiniteKernel S) (stop : S → Bool) (c V : S → ℝ)
    (hstep : ∀ s, c s + expect K V s ≤ V s) :
    ∀ s, stoppedCost stop c s + expect (stoppedKernel K stop) V s ≤ V s := by
  intro s
  rw [expect_stoppedKernel]
  cases hs : stop s <;> simp only [stoppedCost, hs, Bool.false_eq_true,
    ite_false, ite_true, zero_add]
  · exact hstep s
  · exact le_rfl

theorem stopped_work_le (K : FiniteKernel S) (stop : S → Bool) (c V : S → ℝ)
    (hV : ∀ s, 0 ≤ V s) (hstep : ∀ s, c s + expect K V s ≤ V s)
    (m : ℕ) (s : S) : work (stoppedKernel K stop) (stoppedCost stop c) m s ≤ V s := by
  exact work_le_supersolution (stoppedKernel K stop) (stoppedCost stop c) V hV
    (stopped_supersolution K stop c V hstep) m s

theorem stopped_infinite_work_le (K : FiniteKernel S) (stop : S → Bool) (c V : S → ℝ)
    (hV : ∀ s, 0 ≤ V s) (hstep : ∀ s, c s + expect K V s ≤ V s) (s : S) :
    totalWork (stoppedKernel K stop) (stoppedCost stop c) s ≤ ENNReal.ofReal (V s) := by
  exact totalWork_le_supersolution (stoppedKernel K stop) (stoppedCost stop c) V hV
    (stopped_supersolution K stop c V hstep) s

omit [Fintype S] in
theorem stopped_cost_nonneg (stop : S → Bool) (c : S → ℝ) (hc : ∀ s, 0 ≤ c s) :
    ∀ s, 0 ≤ stoppedCost stop c s := by
  intro s
  unfold stoppedCost
  split_ifs
  · exact le_rfl
  · exact hc s

end MTChainFormal
