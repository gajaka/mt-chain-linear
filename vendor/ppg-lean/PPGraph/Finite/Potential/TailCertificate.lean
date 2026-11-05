/-
  Exact checked survival tables. An external producer may calculate the
  rows; Lean checks the initial row and every one-step recurrence. No
  external matrix exponentiation or floating-point probability is trusted.
-/

module

public import PPGraph.Finite.Potential.Tail

@[expose] public section

set_option linter.unusedSectionVars false

namespace FinitePotential

variable {S : Type*} [Fintype S] [DecidableEq S]

def SurvivalTable (M : FiniteDrift.Model S) (F : ℕ → S → ℚ) (H : ℕ) : Prop :=
  (∀ s, F 0 s = if M.good s then 0 else 1) ∧
  ∀ k : Fin H, ∀ s, F (k.val + 1) s =
    if M.good s then 0 else ∑ t, M.transition s t * F k.val t

instance survivalTableDecidable (M : FiniteDrift.Model S) (F : ℕ → S → ℚ) (H : ℕ) :
    Decidable (SurvivalTable M F H) :=
  inferInstanceAs (Decidable (_ ∧ _))

def checkSurvivalTable (M : FiniteDrift.Model S) (F : ℕ → S → ℚ) (H : ℕ) : Bool :=
  decide (SurvivalTable M F H)

theorem checkSurvivalTable_iff (M : FiniteDrift.Model S) (F : ℕ → S → ℚ) (H : ℕ) :
    checkSurvivalTable M F H = true ↔ SurvivalTable M F H := decide_eq_true_iff

theorem survivalTable_exact (M : FiniteDrift.Model S) (F : ℕ → S → ℚ) (H : ℕ)
    (h : SurvivalTable M F H) (n : ℕ) (hn : n ≤ H) (s : S) :
    F n s = survival M n s := by
  induction n generalizing s with
  | zero => exact h.1 s
  | succ n ih =>
    have hlt : n < H := by omega
    have hh := h.2 ⟨n, hlt⟩ s
    simp only at hh
    rw [hh]
    cases hs : M.good s <;> simp only [survival, hs, Bool.false_eq_true, ↓reduceIte]
    · apply Finset.sum_congr rfl
      intro t _
      rw [ih (by omega) t]

theorem checkedSurvivalTable_exact (M : FiniteDrift.Model S) (F : ℕ → S → ℚ) (H : ℕ)
    (hc : checkSurvivalTable M F H = true) (s : S) :
    F H s = survival M H s :=
  survivalTable_exact M F H ((checkSurvivalTable_iff M F H).mp hc) H le_rfl s

theorem checkedSurvivalTable_blocks_le (M : FiniteDrift.Model S) (hm : Stochastic M)
    (F : ℕ → S → ℚ) (H : ℕ) (hc : checkSurvivalTable M F H = true)
    (b : ℚ) (hb0 : 0 ≤ b) (hb : ∀ s, F H s ≤ b) (k : ℕ) (s : S) :
    survival M (k * H) s ≤ b ^ k :=
  survival_blocks_le M hm H b hb0
    (fun t => by rw [← checkedSurvivalTable_exact M F H hc t]; exact hb t) k s

end FinitePotential

#check @FinitePotential.checkSurvivalTable_iff
#check @FinitePotential.survivalTable_exact
#check @FinitePotential.checkedSurvivalTable_exact
#check @FinitePotential.checkedSurvivalTable_blocks_le
