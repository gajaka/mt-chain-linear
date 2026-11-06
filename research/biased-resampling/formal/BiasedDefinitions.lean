module

public import ChainKernel
public import Filtering

@[expose] public section

set_option autoImplicit false

namespace MTChainFormal.BiasedResampling

open scoped BigOperators

noncomputable section

/-- A threshold law; the two smaller values have equal probability. -/
def thresholdWeight (p : ℝ) (a : Fin 3) : ℝ :=
  if a = 2 then p else (1 - p) / 2

/-- Two independent threshold draws and one uniform raw tactic draw.
    Fixed endpoint draws remain unused, exactly as in `replace`. -/
def drawWeight (p : ℝ) (u : Draw) : ℝ :=
  thresholdWeight p u.1 * thresholdWeight p u.2.1 * (1 / 4)

noncomputable def average (p : ℝ) (f : Draw → ℝ) : ℝ :=
  ∑ u, drawWeight p u * f u

def thresholdCost (a : Fin 3) : ℝ := if a = 2 then 0 else 6

def tacticCost (r : Fin 4) : ℝ := if r = 1 then 4 else 0

def nonMaxCount {n : ℕ} (s : ChainState n) : ℕ :=
  (Finset.univ.filter (fun j => s.values j ≠ 2)).card

def weakCount {n : ℕ} (s : ChainState n) : ℕ :=
  (Finset.univ.filter (fun i => s.tactic i = 1)).card

/-- The raw score need not vanish on Good. Stopping, rather than an
    unproved change of the transition law, handles terminal states. -/
noncomputable def potential {n : ℕ} (s : ChainState n) : ℝ :=
  (∑ j, thresholdCost (s.values j)) + ∑ i, tacticCost (s.tactic i)

def coordinateWeight {n : ℕ} (p : ℝ) (c : Filtering.Coord n) :
    Filtering.Alphabet c → ℝ :=
  match c with
  | .inl _ => thresholdWeight p
  | .inr _ => fun _ => 1 / 4

/-- Initialization is specified separately from the repair law. In
    particular p=1/3 is the old uniform initialization. -/
noncomputable def initialWeight {n : ℕ} (p : ℝ) (s : ChainState n) : ℝ :=
  ProductFiltering.density (coordinateWeight p) (Filtering.toCoords s)

/-- The interval on which one common raw pointwise certificate works. -/
abbrev AdmissibleBias := {p : ℝ // (2 / 3 : ℝ) ≤ p ∧ p ≤ 1}

def staticBias : AdmissibleBias := ⟨2 / 3, by constructor <;> norm_num⟩

end

end MTChainFormal.BiasedResampling
