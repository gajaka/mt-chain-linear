import NeighborBase

set_option autoImplicit false

namespace NeighborSeparation

open MTChainFormal

theorem remote_replace {n : ℕ} (hn : 6 ≤ n) (s : ChainState n)
    (i : Fin n) (hi : i.val + 4 ≤ n) (hs : Remote s) (u : Draw) :
    Remote (replace s i u) := by
  obtain ⟨hv, j, hj, hr⟩ := hs
  refine ⟨?_, ⟨j, hj, ?_⟩⟩
  · rw [replace_value (by omega : 2 ≤ n) s i u (n - 1) (by omega)]
    simp only [show n - 1 ≠ 0 by omega, show n - 1 ≠ n by omega,
      show n - 1 ≠ i.val by omega, show n - 1 ≠ i.val + 1 by omega,
      ↓reduceIte]
    exact hv
  · rw [replace_tactic_other s i j u (by
      intro heq
      have := congrArg Fin.val heq
      omega)]
    exact hr

/-- The final proof invokes this only with a gauge proved to exist by min-plus.
    Score equality is used on both sides of every actual remote witness step. -/
theorem bulkDrift_of_gauge {n : ℕ} (hn : 6 ≤ n) (c : ℝ) (h : EdgeCosts)
    (b : ℝ) (k : EdgeCosts) (δ : ℝ) (hd : PointwiseDrift (n := n) c h δ)
    (hagree : ∀ s : ChainState n, Remote s → rawScore c h s = rawScore b k s) :
    BulkDrift n k δ := by
  intro s i hs hi _ hbulk
  have hp := hd s i hi
  have hscore (t : ChainState n) (ht : Remote t) :
      potential c h t = b + rawScore 0 k t := by
    rw [potential_of_active c h t (PotentialSeparation.remote_active (by omega) t ht),
      hagree t ht, rawScore_offset]
  rw [hscore s hs] at hp
  have hafter (u : Draw) : potential c h (replace s i u) =
      b + rawScore 0 k (replace s i u) :=
    hscore _ (remote_replace hn s i hbulk hs u)
  simp_rw [hafter] at hp
  rw [drawAverage_add, drawAverage_const] at hp
  linarith

end NeighborSeparation

#print axioms NeighborSeparation.bulkDrift_of_gauge
