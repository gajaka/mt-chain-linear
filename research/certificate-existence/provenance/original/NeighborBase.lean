import SeparableProduct

set_option autoImplicit false

namespace NeighborSeparation

open MTChainFormal
open scoped BigOperators

abbrev EdgeTable := Fin 3 → Fin 3 → Fin 4 → ℝ
abbrev EdgeCosts := ℕ → EdgeTable

/-- Source edges are zero based; endpoints are the original `value` function. -/
def rawScore {n : ℕ} (c : ℝ) (h : EdgeCosts) (s : ChainState n) : ℝ :=
  c + ∑ i : Fin n, h i.val (value s i.val) (value s (i.val + 1)) (s.tactic i)

noncomputable def potential {n : ℕ} (c : ℝ) (h : EdgeCosts) (s : ChainState n) : ℝ :=
  if firstFailure s = none then 0 else rawScore c h s

def PointwiseDrift {n : ℕ} (c : ℝ) (h : EdgeCosts) (δ : ℝ) : Prop :=
  ∀ (s : ChainState n) (i : Fin n), firstFailure s = some i →
    δ ≤ potential c h s - drawAverage (fun u => potential c h (replace s i u))

noncomputable def initialBudget (n : ℕ) (c : ℝ) (h : EdgeCosts) : ℝ :=
  ∑ s : ChainState n, initialFull s * potential c h s

abbrev Remote {n : ℕ} (s : ChainState n) := PotentialSeparation.RemoteFailure s

def Nonnegative (h : EdgeCosts) : Prop := ∀ i a b r, 0 ≤ h i a b r

noncomputable def meanEdge (h : EdgeTable) : ℝ :=
  (∑ a : Fin 3, ∑ b : Fin 3, ∑ r : Fin 4, h a b r) / 36

/-- An intermediate property; the final theorem must derive this from actual
stopped-potential drift and a proved gauge identity on the remote cylinder. -/
def BulkDrift (n : ℕ) (h : EdgeCosts) (δ : ℝ) : Prop :=
  ∀ (s : ChainState n) (i : Fin n), Remote s → firstFailure s = some i →
    2 ≤ i.val → i.val + 4 ≤ n →
    δ ≤ rawScore 0 h s - drawAverage (fun u => rawScore 0 h (replace s i u))

theorem potential_of_active {n : ℕ} (c : ℝ) (h : EdgeCosts) (s : ChainState n)
    (hs : firstFailure s ≠ none) : potential c h s = rawScore c h s := by
  simp [potential, hs]

theorem meanEdge_nonneg (h : EdgeTable) (hh : ∀ a b r, 0 ≤ h a b r) :
    0 ≤ meanEdge h := by
  apply div_nonneg _ (by norm_num)
  exact Finset.sum_nonneg fun a _ => Finset.sum_nonneg fun b _ =>
    Finset.sum_nonneg fun r _ => hh a b r

theorem rawScore_nonneg {n : ℕ} (b : ℝ) (h : EdgeCosts)
    (hb : 0 ≤ b) (hh : Nonnegative h) (s : ChainState n) : 0 ≤ rawScore b h s := by
  exact add_nonneg hb (Finset.sum_nonneg fun i _ => hh _ _ _ _)

theorem rawScore_offset {n : ℕ} (c : ℝ) (h : EdgeCosts) (s : ChainState n) :
    rawScore c h s = c + rawScore 0 h s := by simp [rawScore]

end NeighborSeparation
