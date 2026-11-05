import SeparableBase

set_option autoImplicit false
set_option maxHeartbeats 3000000

namespace PotentialSeparation

open MTChainFormal MTChainFormal.Tightness
open scoped BigOperators

noncomputable def meanInitial {n : ℕ} (h : ChainState n → ℝ) : ℝ :=
  ∑ s, initialFull s * h s

theorem meanInitial_add {n : ℕ} (h k : ChainState n → ℝ) :
    meanInitial (fun s => h s + k s) = meanInitial h + meanInitial k := by
  simp [meanInitial, mul_add, Finset.sum_add_distrib]

theorem meanInitial_const (n : ℕ) (a : ℝ) :
    meanInitial (fun _ : ChainState n => a) = a := by
  rw [meanInitial, ← Finset.sum_mul, initialFull_sum, one_mul]

theorem meanInitial_sum {n : ℕ} {ι : Type*} [Fintype ι]
    (h : ι → ChainState n → ℝ) :
    meanInitial (fun s => ∑ j, h j s) = ∑ j, meanInitial (h j) := by
  simp only [meanInitial, Finset.mul_sum]
  rw [Finset.sum_comm]

theorem meanInitial_mono {n : ℕ} (h k : ChainState n → ℝ)
    (hle : ∀ s, h s ≤ k s) : meanInitial h ≤ meanInitial k := by
  exact Finset.sum_le_sum fun s _ =>
    mul_le_mul_of_nonneg_left (hle s) (initialFull_nonneg s)

theorem drawAverage_first (a : Fin 3 → ℝ) :
    drawAverage (fun u => a u.1) = mean3 a := by
  norm_num [drawAverage, mean3, Fintype.sum_prod_type, Fin.sum_univ_succ]
  ring

theorem drawAverage_last (a : Fin 4 → ℝ) :
    drawAverage (fun u => a u.2.2) = mean4 a := by
  norm_num [drawAverage, mean4, Fintype.sum_prod_type, Fin.sum_univ_succ]
  ring

theorem meanInitial_threshold {n : ℕ} (j : Fin (n - 1)) (a : Fin 3 → ℝ) :
    meanInitial (fun s : ChainState n => a (s.values j)) = mean3 a := by
  let i : Fin n := ⟨j.val + 1, by omega⟩
  have hvalue (s : ChainState n) (u : Draw) : (replace s i u).values j = u.1 := by
    simp [replace, i]
  unfold meanInitial
  rw [← uniform_fixed_refresh i (fun s => a (s.values j))]
  simp_rw [hvalue, drawAverage_first]
  rw [← Finset.sum_mul, initialFull_sum, one_mul]

theorem meanInitial_tactic {n : ℕ} (j : Fin n) (a : Fin 4 → ℝ) :
    meanInitial (fun s : ChainState n => a (s.tactic j)) = mean4 a := by
  unfold meanInitial
  rw [← uniform_fixed_refresh j (fun s => a (s.tactic j))]
  simp_rw [replace_tactic_same, drawAverage_last]
  rw [← Finset.sum_mul, initialFull_sum, one_mul]

noncomputable def low {α : Type*} [Fintype α] [Nonempty α] (a : α → ℝ) : ℝ :=
  (Finset.univ.image a).min' (by simp)

noncomputable def high {α : Type*} [Fintype α] [Nonempty α] (a : α → ℝ) : ℝ :=
  (Finset.univ.image a).max' (by simp)

theorem exists_low {α : Type*} [Fintype α] [Nonempty α] (a : α → ℝ) :
    ∃ x, a x = low a := by
  classical
  have h := Finset.min'_mem (Finset.univ.image a) (by simp)
  obtain ⟨x, _, hx⟩ := Finset.mem_image.mp h
  exact ⟨x, hx⟩

noncomputable def lowArg {α : Type*} [Fintype α] [Nonempty α] (a : α → ℝ) : α :=
  Classical.choose (exists_low a)

theorem lowArg_value {α : Type*} [Fintype α] [Nonempty α] (a : α → ℝ) :
    a (lowArg a) = low a := Classical.choose_spec (exists_low a)

theorem low_le {α : Type*} [Fintype α] [Nonempty α] (a : α → ℝ) (x : α) :
    low a ≤ a x := by
  classical
  exact Finset.min'_le _ _ (Finset.mem_image.mpr ⟨x, Finset.mem_univ x, rfl⟩)

theorem high_gap_le_sum (a : Fin 3 → ℝ) :
    high a - low a ≤ ∑ x, (a x - low a) := by
  classical
  obtain ⟨x, _, hx⟩ := Finset.mem_image.mp
    (Finset.max'_mem (Finset.univ.image a) (by simp))
  unfold high
  rw [← hx]
  exact Finset.single_le_sum (fun y _ => sub_nonneg.mpr (low_le a y))
    (Finset.mem_univ x)

theorem mean3_gap (a : Fin 3 → ℝ) :
    (high a - low a) / 3 ≤ mean3 a - low a := by
  have h := high_gap_le_sum a
  rw [Finset.sum_sub_distrib] at h
  norm_num [mean3] at h ⊢
  linarith

theorem low_le_mean4 (a : Fin 4 → ℝ) : low a ≤ mean4 a := by
  have h := Finset.sum_le_sum (fun x (_ : x ∈ (Finset.univ : Finset (Fin 4))) => low_le a x)
  norm_num [mean4] at h ⊢
  linarith

def pinRemote (m : ℕ) (s : ChainState (m + 2)) : ChainState (m + 2) :=
  replace s (Fin.last (m + 1)) (1, 0, 1)

theorem pinRemote_values_last (m : ℕ) (s : ChainState (m + 2)) :
    (pinRemote m s).values (Fin.last m) = 1 := by
  simp [pinRemote, replace]

theorem pinRemote_values_castSucc (m : ℕ) (s : ChainState (m + 2)) (j : Fin m) :
    (pinRemote m s).values j.castSucc = s.values j.castSucc := by
  have hj : j.val ≠ m := by omega
  have hj2 : j.val ≠ m + 1 := by omega
  simp [pinRemote, replace, hj, hj2]

theorem pinRemote_tactic_last (m : ℕ) (s : ChainState (m + 2)) :
    (pinRemote m s).tactic (Fin.last (m + 1)) = 1 := by
  simp [pinRemote]

theorem pinRemote_tactic_castSucc (m : ℕ) (s : ChainState (m + 2)) (i : Fin (m + 1)) :
    (pinRemote m s).tactic i.castSucc = s.tactic i.castSucc := by
  have hi : i.castSucc ≠ Fin.last (m + 1) := Fin.castSucc_ne_last i
  simp [pinRemote, replace_tactic_other s _ _ _ hi]

theorem pinRemote_active (m : ℕ) (s : ChainState (m + 2)) :
    firstFailure (pinRemote m s) ≠ none := by
  apply remote_active (by omega)
  constructor
  · have hv := value_internal (pinRemote m s) (Fin.last m)
    simpa using hv.trans (pinRemote_values_last m s)
  · exact ⟨Fin.last (m + 1), by simp, pinRemote_tactic_last m s⟩

theorem rawScore_pinRemote (m : ℕ) (c : ℝ) (f : ThresholdCosts) (g : TacticCosts)
    (s : ChainState (m + 2)) :
    rawScore c f g (pinRemote m s) =
      c + ((∑ j : Fin m, f (j.val + 1) (s.values j.castSucc)) + f (m + 1) 1) +
        ((∑ i : Fin (m + 1), g i.val (s.tactic i.castSucc)) + g (m + 1) 1) := by
  unfold rawScore
  change c + (∑ j : Fin (m + 1), f (j.val + 1) ((pinRemote m s).values j)) +
    (∑ i : Fin (m + 2), g i.val ((pinRemote m s).tactic i)) = _
  rw [Fin.sum_univ_castSucc (fun j : Fin (m + 1) =>
    f (j.val + 1) ((pinRemote m s).values j))]
  rw [Fin.sum_univ_castSucc (fun i : Fin (m + 2) =>
    g i.val ((pinRemote m s).tactic i))]
  simp only [pinRemote_values_last, pinRemote_values_castSucc,
    pinRemote_tactic_last, pinRemote_tactic_castSucc, Fin.val_castSucc, Fin.val_last]

theorem meanInitial_rawScore_pinRemote (m : ℕ) (c : ℝ)
    (f : ThresholdCosts) (g : TacticCosts) :
    meanInitial (fun s : ChainState (m + 2) => rawScore c f g (pinRemote m s)) =
      c + ((∑ j : Fin m, mean3 (f (j.val + 1))) + f (m + 1) 1) +
        ((∑ i : Fin (m + 1), mean4 (g i.val)) + g (m + 1) 1) := by
  simp only [rawScore_pinRemote, meanInitial_add, meanInitial_sum,
    meanInitial_const, meanInitial_threshold, meanInitial_tactic]

noncomputable def minState (m : ℕ) (f : ThresholdCosts) (g : TacticCosts) :
    ChainState (m + 2) where
  values j := lowArg (f (j.val + 1))
  tactic i := lowArg (g i.val)

theorem pinned_mean_ge_oscillation (m : ℕ) (c : ℝ)
    (f : ThresholdCosts) (g : TacticCosts)
    (hnonneg : ∀ s : ChainState (m + 2), 0 ≤ potential c f g s) :
    (∑ j : Fin m, oscillation f (j.val + 1)) / 3 ≤
      meanInitial (fun s : ChainState (m + 2) => rawScore c f g (pinRemote m s)) := by
  have hmin := hnonneg (pinRemote m (minState m f g))
  rw [potential_of_active c f g _ (pinRemote_active _ _), rawScore_pinRemote] at hmin
  simp only [minState, Fin.val_castSucc, lowArg_value] at hmin
  have hf (j : Fin m) : oscillation f (j.val + 1) / 3 +
      low (f (j.val + 1)) ≤ mean3 (f (j.val + 1)) := by
    have h := mean3_gap (f (j.val + 1))
    change (high (f (j.val + 1)) - low (f (j.val + 1))) / 3 + _ ≤ _
    linarith
  have hfs := Finset.sum_le_sum (fun j (_ : j ∈ (Finset.univ : Finset (Fin m))) => hf j)
  simp only [Finset.sum_add_distrib] at hfs
  rw [← Finset.sum_div] at hfs
  have hgs := Finset.sum_le_sum (fun i (_ : i ∈ (Finset.univ : Finset (Fin (m + 1)))) =>
    low_le_mean4 (g i.val))
  rw [meanInitial_rawScore_pinRemote]
  linarith

theorem replace_last_dummy (m : ℕ) (s : ChainState (m + 2))
    (a b : Fin 3) (r : Fin 4) :
    replace s (Fin.last (m + 1)) (a, b, r) =
      replace s (Fin.last (m + 1)) (a, 0, r) := by
  cases s with
  | mk values tactic =>
    simp only [replace, Fin.val_last]
    congr 1
    funext j
    have hj : j.val ≠ m + 1 := by omega
    simp [hj]

theorem drawAverage_last_refresh (m : ℕ) (s : ChainState (m + 2))
    (V : ChainState (m + 2) → ℝ) :
    drawAverage (fun u => V (replace s (Fin.last (m + 1)) u)) =
      (∑ a : Fin 3, ∑ r : Fin 4,
        V (replace s (Fin.last (m + 1)) (a, 0, r))) / 12 := by
  have heq (u : Draw) : replace s (Fin.last (m + 1)) u =
      replace s (Fin.last (m + 1)) (u.1, 0, u.2.2) :=
    replace_last_dummy m s u.1 u.2.1 u.2.2
  simp_rw [heq]
  norm_num [drawAverage, Fintype.sum_prod_type, Fin.sum_univ_succ]
  ring

theorem pinRemote_le_refresh (m : ℕ) (s : ChainState (m + 2))
    (V : ChainState (m + 2) → ℝ) (hV : ∀ t, 0 ≤ V t) :
    V (pinRemote m s) / 12 ≤
      drawAverage (fun u => V (replace s (Fin.last (m + 1)) u)) := by
  rw [drawAverage_last_refresh]
  apply div_le_div_of_nonneg_right _ (by norm_num)
  have hinner : V (replace s (Fin.last (m + 1)) (1, 0, 1)) ≤
      ∑ r : Fin 4, V (replace s (Fin.last (m + 1)) (1, 0, r)) :=
    Finset.single_le_sum (fun r (_ : r ∈ (Finset.univ : Finset (Fin 4))) =>
      hV (replace s (Fin.last (m + 1)) (1, 0, r)))
      (Finset.mem_univ (1 : Fin 4))
  have houter : (∑ r : Fin 4, V (replace s (Fin.last (m + 1)) (1, 0, r))) ≤
      ∑ a : Fin 3, ∑ r : Fin 4, V (replace s (Fin.last (m + 1)) (a, 0, r)) :=
    Finset.single_le_sum (fun a (_ : a ∈ (Finset.univ : Finset (Fin 3))) =>
      Finset.sum_nonneg fun r _ => hV (replace s (Fin.last (m + 1)) (a, 0, r)))
      (Finset.mem_univ (1 : Fin 3))
  exact hinner.trans houter

theorem initial_budget_pinned (m : ℕ) (c : ℝ) (f : ThresholdCosts) (g : TacticCosts)
    (hnonneg : ∀ s : ChainState (m + 2), 0 ≤ potential c f g s) :
    meanInitial (fun s : ChainState (m + 2) => rawScore c f g (pinRemote m s)) / 12 ≤
      initialBudget (m + 2) c f g := by
  have h := meanInitial_mono
    (fun s : ChainState (m + 2) => potential c f g (pinRemote m s) / 12)
    (fun s => drawAverage (fun u => potential c f g (replace s (Fin.last (m + 1)) u)))
    (fun s => pinRemote_le_refresh m s _ hnonneg)
  simp_rw [potential_of_active c f g _ (pinRemote_active m _)] at h
  unfold meanInitial at h
  rw [uniform_fixed_refresh] at h
  simp_rw [← mul_div_assoc] at h
  rw [← Finset.sum_div] at h
  simpa only [initialBudget, meanInitial] using h

theorem initial_budget_oscillation {n : ℕ} (hn : 4 ≤ n)
    (c : ℝ) (f : ThresholdCosts) (g : TacticCosts)
    (hnonneg : ∀ s : ChainState n, 0 ≤ potential c f g s) :
    (∑ j : Fin (n - 2), oscillation f (j.val + 1)) / 36 ≤ initialBudget n c f g := by
  obtain ⟨m, hm⟩ := Nat.exists_eq_add_of_le (show 2 ≤ n by omega)
  have heq : n = m + 2 := by omega
  clear hm
  subst n
  have hp := pinned_mean_ge_oscillation m c f g hnonneg
  have hb := initial_budget_pinned m c f g hnonneg
  change (∑ j : Fin m, oscillation f (j.val + 1)) / 36 ≤ initialBudget (m + 2) c f g
  linarith

#print axioms initial_budget_oscillation

end PotentialSeparation
