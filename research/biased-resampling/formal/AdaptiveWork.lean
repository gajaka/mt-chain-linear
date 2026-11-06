module

public import BiasedDrift

@[expose] public section

set_option autoImplicit false

namespace MTChainFormal.BiasedResampling

open scoped BigOperators ENNReal

/-- The current full state is supplied separately. The list contains every
    previous full state, most recent first. No finite-memory restriction is
    imposed on either decision. -/
structure HistoryPolicy (n : ℕ) where
  bias : List (ChainState n) → ActiveState n → AdmissibleBias
  choose : (history : List (ChainState n)) → (s : ActiveState n) →
    {i : Fin n // passes s.val i = false}

/-- The original least-failed selection, with a fixed admissible redraw law. -/
noncomputable def staticPolicy {n : ℕ} (p : AdmissibleBias) : HistoryPolicy n where
  bias := fun _ _ => p
  choose := fun _ s => ⟨activeSelected s, activeSelected_failed s⟩

/-- Expected number of actual redraws in the first `m` opportunities. A good
    state stops immediately and earns no further cost. The selected law is
    applied after both decisions have read the full finite history. -/
noncomputable def adaptiveWork {n : ℕ} (policy : HistoryPolicy n) :
    ℕ → List (ChainState n) → ChainState n → ℝ
  | 0, _, _ => 0
  | m + 1, history, s =>
      if hbad : (badIndices s).Nonempty then
        let a : ActiveState n := ⟨s, hbad⟩
        1 + average (policy.bias history a).val (fun u =>
          adaptiveWork policy m (s :: history)
            (replace s (policy.choose history a).val u))
      else 0

@[simp] theorem adaptiveWork_zero {n : ℕ} (policy : HistoryPolicy n)
    (history : List (ChainState n)) (s : ChainState n) :
    adaptiveWork policy 0 history s = 0 := rfl

theorem adaptiveWork_of_good {n : ℕ} (policy : HistoryPolicy n)
    (m : ℕ) (history : List (ChainState n)) (s : ChainState n)
    (hg : firstFailure s = none) : adaptiveWork policy m history s = 0 := by
  have hn : ¬ (badIndices s).Nonempty := by
    intro hb
    have hf := firstFailure_eq_some s hb
    rw [hg] at hf
    cases hf
  cases m <;> simp [adaptiveWork, hn]

theorem adaptiveWork_nonneg {n : ℕ} (policy : HistoryPolicy n)
    (m : ℕ) (history : List (ChainState n)) (s : ChainState n) :
    0 ≤ adaptiveWork policy m history s := by
  induction m generalizing history s with
  | zero => exact le_rfl
  | succ m ih =>
      simp only [adaptiveWork]
      split_ifs with hb
      · apply add_nonneg (by norm_num)
        apply average_nonneg
        · exact le_trans (by norm_num) (policy.bias history ⟨s, hb⟩).property.1
        · exact (policy.bias history ⟨s, hb⟩).property.2
        · intro u
          exact ih _ _
      · exact le_rfl

theorem adaptiveWork_mono {n : ℕ} (policy : HistoryPolicy n)
    (m : ℕ) (history : List (ChainState n)) (s : ChainState n) :
    adaptiveWork policy m history s ≤ adaptiveWork policy (m + 1) history s := by
  induction m generalizing history s with
  | zero => exact adaptiveWork_nonneg policy 1 history s
  | succ m ih =>
      simp only [adaptiveWork]
      split_ifs with hb
      · apply add_le_add (le_refl (1 : ℝ))
        apply average_mono
        · exact le_trans (by norm_num) (policy.bias history ⟨s, hb⟩).property.1
        · exact (policy.bias history ⟨s, hb⟩).property.2
        · intro u
          exact ih _ _
      · exact le_rfl

theorem adaptiveWork_monotone {n : ℕ} (policy : HistoryPolicy n)
    (history : List (ChainState n)) (s : ChainState n) :
    Monotone (fun m => adaptiveWork policy m history s) :=
  monotone_nat_of_le_succ (fun m => adaptiveWork_mono policy m history s)

/-- One common certificate bounds every full-history adaptive controller.
    Neither a Markov controller nor a fixed bias is assumed. -/
theorem adaptiveWork_le_potential {n : ℕ} (hn : 2 ≤ n)
    (policy : HistoryPolicy n) (m : ℕ)
    (history : List (ChainState n)) (s : ChainState n) :
    adaptiveWork policy m history s ≤ potential s := by
  induction m generalizing history s with
  | zero => exact potential_nonneg s
  | succ m ih =>
      simp only [adaptiveWork]
      split_ifs with hb
      · apply le_trans (add_le_add (le_refl (1 : ℝ)) (average_mono _
            (le_trans (by norm_num) (policy.bias history ⟨s, hb⟩).property.1)
            (policy.bias history ⟨s, hb⟩).property.2 (fun _ => ih _ _)))
        exact pointwise_drift hn _ (policy.bias history ⟨s, hb⟩).property.1
          (policy.bias history ⟨s, hb⟩).property.2 s
          (policy.choose history ⟨s, hb⟩).val
          (policy.choose history ⟨s, hb⟩).property
      · exact potential_nonneg s

/-- Infinite expected redraw cost is the supremum of actual finite-horizon
    costs. Finiteness is proved below, not assumed in this definition. -/
noncomputable def adaptiveTotalWork {n : ℕ} (policy : HistoryPolicy n)
    (history : List (ChainState n)) (s : ChainState n) : ℝ≥0∞ :=
  ⨆ m : ℕ, ENNReal.ofReal (adaptiveWork policy m history s)

theorem adaptiveTotalWork_le_potential {n : ℕ} (hn : 2 ≤ n)
    (policy : HistoryPolicy n) (history : List (ChainState n)) (s : ChainState n) :
    adaptiveTotalWork policy history s ≤ ENNReal.ofReal (potential s) := by
  apply iSup_le
  intro m
  exact ENNReal.ofReal_le_ofReal (adaptiveWork_le_potential hn policy m history s)

theorem adaptiveTotalWork_le_linear {n : ℕ} (hn : 2 ≤ n)
    (policy : HistoryPolicy n) (history : List (ChainState n)) (s : ChainState n) :
    adaptiveTotalWork policy history s ≤ ENNReal.ofReal (10 * (n : ℝ) - 6) := by
  exact (adaptiveTotalWork_le_potential hn policy history s).trans
    (ENNReal.ofReal_le_ofReal (potential_le hn s))

theorem adaptiveTotalWork_lt_top {n : ℕ} (hn : 2 ≤ n)
    (policy : HistoryPolicy n) (history : List (ChainState n)) (s : ChainState n) :
    adaptiveTotalWork policy history s < ∞ := by
  exact lt_of_le_of_lt (adaptiveTotalWork_le_potential hn policy history s)
    ENNReal.ofReal_lt_top

/-- The fixed-law raw step keeps a good configuration unchanged. -/
noncomputable def staticStep {n : ℕ} (s : ChainState n) (u : Draw) : ChainState n :=
  match firstFailure s with
  | none => s
  | some i => replace s i u

theorem staticStep_of_bad {n : ℕ} (s : ActiveState n) (u : Draw) :
    staticStep s.val u = replace s.val (activeSelected s) u := by
  simp [staticStep, activeSelected_firstFailure s]

theorem staticStep_of_good {n : ℕ} (s : ChainState n) (u : Draw)
    (hg : firstFailure s = none) : staticStep s u = s := by
  simp [staticStep, hg]

noncomputable def staticWeight {n : ℕ} (p : AdmissibleBias)
    (s t : ChainState n) : ℝ :=
  ∑ u : Draw, if staticStep s u = t then drawWeight p.val u else 0

theorem staticWeight_nonneg {n : ℕ} (p : AdmissibleBias)
    (s t : ChainState n) : 0 ≤ staticWeight p s t := by
  classical
  apply Finset.sum_nonneg
  intro u _
  split_ifs
  · exact drawWeight_nonneg p.val (le_trans (by norm_num) p.property.1) p.property.2 u
  · exact le_rfl

theorem staticWeight_sum {n : ℕ} (p : AdmissibleBias) (s : ChainState n) :
    ∑ t, staticWeight p s t = 1 := by
  classical
  unfold staticWeight
  rw [Finset.sum_comm]
  simpa using drawWeight_sum p.val

/-- The actual finite Markov kernel for a fixed admissible law and the
    least-failed selector. It is a specialization of the history process. -/
noncomputable def staticKernel (p : AdmissibleBias) (n : ℕ) :
    FiniteKernel (ChainState n) where
  weight := staticWeight p
  nonneg := staticWeight_nonneg p
  sum_eq_one := staticWeight_sum p

theorem expect_staticKernel {n : ℕ} (p : AdmissibleBias)
    (f : ChainState n → ℝ) (s : ChainState n) :
    expect (staticKernel p n) f s = average p.val (fun u => f (staticStep s u)) := by
  classical
  unfold expect staticKernel staticWeight average
  simp only [Finset.sum_mul]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro u _
  simp

noncomputable def rawActiveCost {n : ℕ} (s : ChainState n) : ℝ :=
  if firstFailure s = none then 0 else 1

theorem rawActiveCost_nonneg {n : ℕ} (s : ChainState n) : 0 ≤ rawActiveCost s := by
  unfold rawActiveCost
  split_ifs <;> norm_num

theorem rawActiveCost_of_bad {n : ℕ} (s : ActiveState n) : rawActiveCost s.val = 1 := by
  simp [rawActiveCost, activeSelected_firstFailure s]

/-- The generic finite-kernel accounting and the actual history recurrence
    count the same redraws for the fixed-policy specialization. -/
theorem staticWork_eq {n : ℕ} (p : AdmissibleBias) (m : ℕ)
    (history : List (ChainState n)) (s : ChainState n) :
    adaptiveWork (staticPolicy p) m history s =
      work (staticKernel p n) rawActiveCost m s := by
  induction m generalizing history s with
  | zero => rfl
  | succ m ih =>
      rw [work_succ, expect_staticKernel]
      simp only [adaptiveWork]
      split_ifs with hb
      · have hc : rawActiveCost s = 1 := rawActiveCost_of_bad ⟨s, hb⟩
        rw [hc]
        congr 1
        apply congrArg (average p.val)
        funext u
        change adaptiveWork (staticPolicy p) m (s :: history)
            (replace s (activeSelected (⟨s, hb⟩ : ActiveState n)) u) = _
        rw [ih]
        rw [staticStep_of_bad (⟨s, hb⟩ : ActiveState n)]
      · have hg : firstFailure s = none := by simp [firstFailure, hb]
        have hc : rawActiveCost s = 0 := by simp [rawActiveCost, hg]
        rw [hc, zero_add]
        have hw : work (staticKernel p n) rawActiveCost m s = 0 := by
          rw [← ih history s]
          exact adaptiveWork_of_good _ _ _ _ hg
        simp [staticStep_of_good s _ hg, hw, average_const]

theorem staticWork_history_independent {n : ℕ} (p : AdmissibleBias) (m : ℕ)
    (history otherHistory : List (ChainState n)) (s : ChainState n) :
    adaptiveWork (staticPolicy p) m history s =
      adaptiveWork (staticPolicy p) m otherHistory s := by
  rw [staticWork_eq, staticWork_eq]

theorem staticTotalWork_eq {n : ℕ} (p : AdmissibleBias)
    (history : List (ChainState n)) (s : ChainState n) :
    adaptiveTotalWork (staticPolicy p) history s =
      totalWork (staticKernel p n) rawActiveCost s := by
  simp only [adaptiveTotalWork, totalWork, staticWork_eq]

end MTChainFormal.BiasedResampling
