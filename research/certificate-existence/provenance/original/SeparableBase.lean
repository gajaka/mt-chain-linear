import InitialBadMoment

set_option autoImplicit false

namespace PotentialSeparation

open MTChainFormal
open scoped BigOperators

/-- Natural threshold sites are 1,...,n-1; tactic sites are zero based. -/
abbrev ThresholdCosts := ℕ → Fin 3 → ℝ
abbrev TacticCosts := ℕ → Fin 4 → ℝ

def rawScore {n : ℕ} (c : ℝ) (f : ThresholdCosts) (g : TacticCosts)
    (s : ChainState n) : ℝ :=
  c + (∑ j : Fin (n - 1), f (j.val + 1) (s.values j)) +
    ∑ i : Fin n, g i.val (s.tactic i)

noncomputable def potential {n : ℕ} (c : ℝ) (f : ThresholdCosts) (g : TacticCosts)
    (s : ChainState n) : ℝ :=
  if firstFailure s = none then 0 else rawScore c f g s

noncomputable def mean3 (a : Fin 3 → ℝ) : ℝ := (∑ x, a x) / 3
noncomputable def mean4 (a : Fin 4 → ℝ) : ℝ := (∑ x, a x) / 4
def contrast (f : ThresholdCosts) (j : ℕ) : ℝ := f j 0 - f j 2
noncomputable def oscillation (f : ThresholdCosts) (j : ℕ) : ℝ :=
  (Finset.univ.image (f j)).max' (by simp) -
    (Finset.univ.image (f j)).min' (by simp)

def PointwiseDrift {n : ℕ} (c : ℝ) (f : ThresholdCosts) (g : TacticCosts)
    (δ : ℝ) : Prop :=
  ∀ (s : ChainState n) (i : Fin n), firstFailure s = some i →
    δ ≤ potential c f g s -
      drawAverage (fun u => potential c f g (replace s i u))

noncomputable def initialBudget (n : ℕ) (c : ℝ) (f : ThresholdCosts)
    (g : TacticCosts) : ℝ :=
  ∑ s : ChainState n, initialFull s * potential c f g s

def RemoteFailure {n : ℕ} (s : ChainState n) : Prop :=
  value s (n - 1) = 1 ∧ ∃ i : Fin n, i.val = n - 1 ∧ s.tactic i = 1

theorem potential_of_active {n : ℕ} (c : ℝ) (f : ThresholdCosts)
    (g : TacticCosts) (s : ChainState n) (h : firstFailure s ≠ none) :
    potential c f g s = rawScore c f g s := by
  simp [potential, h]

theorem potential_of_good {n : ℕ} (c : ℝ) (f : ThresholdCosts)
    (g : TacticCosts) (s : ChainState n) (h : firstFailure s = none) :
    potential c f g s = 0 := by
  simp [potential, h]

theorem remote_active {n : ℕ} (hn : 2 ≤ n) (s : ChainState n)
    (h : RemoteFailure s) : firstFailure s ≠ none := by
  intro hg
  obtain ⟨hv, i, hi, hr⟩ := h
  have hp := (no_failure_iff s).mp hg i
  unfold passes at hp
  rw [hi, show n - 1 + 1 = n by omega, hv, value_right (by omega : 0 < n)] at hp
  norm_num [MTChainProof.bridgePass, hr] at hp

end PotentialSeparation
