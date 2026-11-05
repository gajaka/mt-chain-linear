module

public import NeighborBase

@[expose] public section

set_option autoImplicit false
set_option maxHeartbeats 3000000

namespace NeighborSeparation

open MTChainFormal MTChainFormal.Tightness
open scoped BigOperators

theorem drawAverage_edge (h : EdgeTable) :
    drawAverage (fun u => h u.1 u.2.1 u.2.2) = meanEdge h := by
  simp only [drawAverage, meanEdge, Fintype.sum_prod_type]
  simp_rw [← Finset.mul_sum]
  ring

theorem meanInitial_edge {n : ℕ} (i : Fin n) (hi : 1 ≤ i.val)
    (hend : i.val + 1 < n) (h : EdgeTable) :
    PotentialSeparation.meanInitial (fun s : ChainState n =>
      h (value s i.val) (value s (i.val + 1)) (s.tactic i)) = meanEdge h := by
  have hleft (s : ChainState n) (u : Draw) :
      value (replace s i u) i.val = u.1 := by
    rw [replace_value (by omega) s i u i.val (by omega)]
    simp [show i.val ≠ 0 by omega, show i.val ≠ n by omega]
  have hright (s : ChainState n) (u : Draw) :
      value (replace s i u) (i.val + 1) = u.2.1 := by
    rw [replace_value (by omega) s i u (i.val + 1) (by omega)]
    simp [show i.val + 1 ≠ n by omega]
  unfold PotentialSeparation.meanInitial
  rw [← uniform_fixed_refresh i
    (fun s => h (value s i.val) (value s (i.val + 1)) (s.tactic i))]
  simp_rw [hleft, hright, replace_tactic_same, drawAverage_edge]
  rw [← Finset.sum_mul, initialFull_sum, one_mul]

theorem pinRemote_remote (m : ℕ) (s : ChainState (m + 2)) :
    Remote (PotentialSeparation.pinRemote m s) := by
  constructor
  · have hv := value_internal (PotentialSeparation.pinRemote m s) (Fin.last m)
    simpa using hv.trans (PotentialSeparation.pinRemote_values_last m s)
  · exact ⟨Fin.last (m + 1), by simp, PotentialSeparation.pinRemote_tactic_last m s⟩

theorem pinRemote_value (m : ℕ) (s : ChainState (m + 2))
    (j : ℕ) (hj : j ≤ m) :
    value (PotentialSeparation.pinRemote m s) j = value s j := by
  unfold PotentialSeparation.pinRemote
  rw [replace_value (by omega) s (Fin.last (m + 1)) (1, 0, 1) j (by omega)]
  by_cases h0 : j = 0
  · subst j
    simp
  · simp [h0, show j ≠ m + 2 by omega, show j ≠ m + 1 by omega]

theorem pinRemote_tactic (m : ℕ) (s : ChainState (m + 2))
    (i : Fin (m + 2)) (hi : i.val ≤ m) :
    (PotentialSeparation.pinRemote m s).tactic i = s.tactic i := by
  have hne : i ≠ Fin.last (m + 1) := by
    intro heq
    have hv := congrArg Fin.val heq
    simp only [Fin.val_last] at hv
    omega
  unfold PotentialSeparation.pinRemote
  exact replace_tactic_other s _ _ _ hne

theorem meanInitial_pinned_edge (m : ℕ) (i : Fin (m + 2))
    (hi : 1 ≤ i.val) (hend : i.val + 1 ≤ m) (h : EdgeTable) :
    PotentialSeparation.meanInitial (fun s : ChainState (m + 2) =>
      h (value (PotentialSeparation.pinRemote m s) i.val)
        (value (PotentialSeparation.pinRemote m s) (i.val + 1))
        ((PotentialSeparation.pinRemote m s).tactic i)) = meanEdge h := by
  simp_rw [pinRemote_value m _ i.val (by omega),
    pinRemote_value m _ (i.val + 1) hend, pinRemote_tactic m _ i (by omega)]
  exact meanInitial_edge i hi (by omega) h

theorem initial_budget_pinned (m : ℕ) (c : ℝ) (h : EdgeCosts)
    (hnonneg : ∀ s : ChainState (m + 2), 0 ≤ potential c h s) :
    PotentialSeparation.meanInitial (fun s : ChainState (m + 2) =>
      rawScore c h (PotentialSeparation.pinRemote m s)) / 12 ≤
        initialBudget (m + 2) c h := by
  have hb := PotentialSeparation.meanInitial_mono
    (fun s : ChainState (m + 2) => potential c h (PotentialSeparation.pinRemote m s) / 12)
    (fun s => drawAverage (fun u => potential c h (replace s (Fin.last (m + 1)) u)))
    (fun s => PotentialSeparation.pinRemote_le_refresh m s _ hnonneg)
  simp_rw [potential_of_active c h _ (PotentialSeparation.pinRemote_active m _)] at hb
  unfold PotentialSeparation.meanInitial at hb
  rw [uniform_fixed_refresh] at hb
  simp_rw [← mul_div_assoc] at hb
  rw [← Finset.sum_div] at hb
  simpa only [initialBudget, PotentialSeparation.meanInitial] using hb

theorem shifted_sum_le {n m : ℕ} (hn : m + 1 ≤ n)
    (f : Fin n → ℝ) (hf : ∀ i, 0 ≤ f i) :
    (∑ j : Fin m, f ⟨j.val + 1, by omega⟩) ≤ ∑ i : Fin n, f i := by
  classical
  let e : Fin m → Fin n := fun j => ⟨j.val + 1, by omega⟩
  have he : Function.Injective e := by
    intro a b hab
    apply Fin.ext
    have hv := congrArg Fin.val hab
    dsimp [e] at hv
    omega
  have hs := Finset.sum_le_sum_of_subset_of_nonneg
    (Finset.subset_univ (Finset.univ.image e))
    (fun i _ _ => hf i)
  rw [Finset.sum_image (fun a _ b _ hab => he hab)] at hs
  simpa [e] using hs

theorem pinned_score_bulk (m : ℕ) (hm : 1 ≤ m) (b : ℝ) (k : EdgeCosts)
    (hb : 0 ≤ b) (hk : Nonnegative k) :
    (∑ j : Fin (m - 1), meanEdge (k (j.val + 1))) ≤
      PotentialSeparation.meanInitial (fun s : ChainState (m + 2) =>
        rawScore b k (PotentialSeparation.pinRemote m s)) := by
  let edge : Fin (m - 1) → Fin (m + 2) := fun j => ⟨j.val + 1, by omega⟩
  let term (s : ChainState (m + 2)) (i : Fin (m + 2)) :=
    k i.val (value (PotentialSeparation.pinRemote m s) i.val)
      (value (PotentialSeparation.pinRemote m s) (i.val + 1))
      ((PotentialSeparation.pinRemote m s).tactic i)
  have hp (s : ChainState (m + 2)) :
      (∑ j : Fin (m - 1), term s (edge j)) ≤
        rawScore b k (PotentialSeparation.pinRemote m s) := by
    have hs := shifted_sum_le (n := m + 2) (m := m - 1) (by omega)
      (term s)
      (fun i => hk _ _ _ _)
    have heq : rawScore b k (PotentialSeparation.pinRemote m s) = b + ∑ i, term s i := rfl
    rw [heq]
    exact hs.trans (le_add_of_nonneg_left hb)
  have hmean := PotentialSeparation.meanInitial_mono _ _ hp
  rw [PotentialSeparation.meanInitial_sum] at hmean
  have hterm (j : Fin (m - 1)) :
      PotentialSeparation.meanInitial (fun s : ChainState (m + 2) => term s (edge j)) =
        meanEdge (k (j.val + 1)) := by
    have hi : 1 ≤ (edge j).val := by dsimp [edge]; omega
    have hend : (edge j).val + 1 ≤ m := by dsimp [edge]; omega
    exact meanInitial_pinned_edge m (edge j) hi hend (k (j.val + 1))
  simpa only [hterm] using hmean

theorem product_budget_bulk {n : ℕ} (hn : 6 ≤ n) (c : ℝ) (h : EdgeCosts)
    (b : ℝ) (k : EdgeCosts)
    (hnonneg : ∀ s : ChainState n, 0 ≤ potential c h s)
    (hb : 0 ≤ b) (hk : Nonnegative k)
    (hagree : ∀ s : ChainState n, Remote s → rawScore c h s = rawScore b k s) :
    (∑ j : Fin (n - 3), meanEdge (k (j.val + 1))) / 12 ≤ initialBudget n c h := by
  obtain ⟨m, hm⟩ := Nat.exists_eq_add_of_le (show 2 ≤ n by omega)
  have heq : n = m + 2 := by omega
  clear hm
  subst n
  have hp := pinned_score_bulk m (by omega) b k hb hk
  have hi := initial_budget_pinned m c h hnonneg
  have hpin (s : ChainState (m + 2)) :
      rawScore c h (PotentialSeparation.pinRemote m s) =
        rawScore b k (PotentialSeparation.pinRemote m s) :=
    hagree _ (pinRemote_remote m s)
  simp_rw [hpin] at hi
  have hdim : m + 2 - 3 = m - 1 := by omega
  rw [hdim]
  linarith

#print axioms product_budget_bulk

end NeighborSeparation
