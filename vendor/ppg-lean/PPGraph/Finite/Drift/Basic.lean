/-
  Exact finite certificates for additive drift.

  A model supplies rational transition probabilities and a fixed good-state
  predicate. A witness supplies a rational nonnegative potential, zero at
  good states, and a positive uniform decrease. The executable checker
  verifies normalization and every local expected-decrease inequality.

  Source: Lengler, Drift Analysis, arXiv:1712.00964, additive drift.
  This is a finite, bounded, stopped-potential specialization. No eventual
  success or expected-duration assertion is a certificate field. Rejection
  means that this witness fails; it is not an infeasibility certificate.
-/

module

public import PPGraph.Drift.Additive
public import Mathlib.Probability.ProbabilityMassFunction.Constructions
public import Mathlib.Probability.ProbabilityMassFunction.Integrals

@[expose] public section

set_option linter.unusedSectionVars false

open MeasureTheory
open scoped ENNReal NNReal

namespace FiniteDrift

variable {S : Type*} [Fintype S] [DecidableEq S]

structure Model (S : Type*) where
  transition : S → S → ℚ
  good : S → Bool

structure Witness (S : Type*) where
  potential : S → ℚ
  delta : ℚ

def localExpectation (M : Model S) (W : Witness S) (s : S) : ℚ :=
  ∑ t, M.transition s t * W.potential t

def Conditions (M : Model S) (W : Witness S) : Prop :=
  (∀ s t, 0 ≤ M.transition s t) ∧
  (∀ s, ∑ t, M.transition s t = 1) ∧
  (∀ s, 0 ≤ W.potential s) ∧
  (∀ s, M.good s = true → W.potential s = 0) ∧
  0 < W.delta ∧
  ∀ s, localExpectation M W s + (if M.good s then 0 else W.delta) ≤ W.potential s

instance conditionsDecidable (M : Model S) (W : Witness S) : Decidable (Conditions M W) :=
  inferInstanceAs (Decidable (_ ∧ _ ∧ _ ∧ _ ∧ _ ∧ _))

/-- All computations in this acceptance test are exact rational computations. -/
def check (M : Model S) (W : Witness S) : Bool := decide (Conditions M W)

theorem check_eq_true_iff (M : Model S) (W : Witness S) :
    check M W = true ↔ Conditions M W := by
  exact decide_eq_true_iff

theorem check_sound (M : Model S) (W : Witness S) (h : check M W = true) :
    Conditions M W := (check_eq_true_iff M W).mp h

theorem check_complete (M : Model S) (W : Witness S) (h : Conditions M W) :
    check M W = true := (check_eq_true_iff M W).mpr h

theorem transition_nonnegative (M : Model S) (W : Witness S)
    (h : check M W = true) (s t : S) : 0 ≤ M.transition s t :=
  (check_sound M W h).1 s t

theorem transition_normalized (M : Model S) (W : Witness S)
    (h : check M W = true) (s : S) : ∑ t, M.transition s t = 1 :=
  (check_sound M W h).2.1 s

theorem potential_nonnegative (M : Model S) (W : Witness S)
    (h : check M W = true) (s : S) : 0 ≤ W.potential s :=
  (check_sound M W h).2.2.1 s

theorem potential_zero_of_good (M : Model S) (W : Witness S)
    (h : check M W = true) (s : S) (hs : M.good s = true) : W.potential s = 0 :=
  (check_sound M W h).2.2.2.1 s hs

theorem delta_positive (M : Model S) (W : Witness S)
    (h : check M W = true) : 0 < W.delta :=
  (check_sound M W h).2.2.2.2.1

theorem local_decrease (M : Model S) (W : Witness S)
    (h : check M W = true) (s : S) :
    localExpectation M W s + (if M.good s then 0 else W.delta) ≤ W.potential s :=
  (check_sound M W h).2.2.2.2.2 s

theorem localExpectation_nonnegative (M : Model S) (W : Witness S)
    (h : check M W = true) (s : S) : 0 ≤ localExpectation M W s := by
  exact Finset.sum_nonneg (fun t _ => mul_nonneg
    (transition_nonnegative M W h s t) (potential_nonnegative M W h t))

theorem potential_ge_delta_of_bad (M : Model S) (W : Witness S)
    (h : check M W = true) (s : S) (hs : M.good s = false) : W.delta ≤ W.potential s := by
  have hd := local_decrease M W h s
  have hn := localExpectation_nonnegative M W h s
  simp only [hs, Bool.false_eq_true, ↓reduceIte] at hd
  linarith

/-- Accepted good states cannot put positive transition mass on a bad state. -/
theorem transition_zero_good_bad (M : Model S) (W : Witness S)
    (h : check M W = true) (s t : S)
    (hs : M.good s = true) (ht : M.good t = false) : M.transition s t = 0 := by
  have hd := local_decrease M W h s
  rw [hs, potential_zero_of_good M W h s hs] at hd
  simp only [↓reduceIte, add_zero] at hd
  have hterm : M.transition s t * W.potential t ≤ localExpectation M W s := by
    exact Finset.single_le_sum (fun u _ => mul_nonneg
      (transition_nonnegative M W h s u) (potential_nonnegative M W h u))
      (Finset.mem_univ t)
  have hp : 0 < W.potential t := lt_of_lt_of_le (delta_positive M W h)
    (potential_ge_delta_of_bad M W h t ht)
  have hk := transition_nonnegative M W h s t
  nlinarith

theorem real_localExpectation (M : Model S) (W : Witness S) (s : S) :
    (localExpectation M W s : ℝ) = ∑ t, (M.transition s t : ℝ) * (W.potential t : ℝ) := by
  simp only [localExpectation, Rat.cast_sum, Rat.cast_mul]

theorem real_local_decrease (M : Model S) (W : Witness S)
    (h : check M W = true) (s : S) :
    (∑ t, (M.transition s t : ℝ) * (W.potential t : ℝ)) +
      (if M.good s then 0 else (W.delta : ℝ)) ≤ (W.potential s : ℝ) := by
  have hd : (localExpectation M W s : ℝ) +
      ((if M.good s then 0 else W.delta : ℚ) : ℝ) ≤ (W.potential s : ℝ) := by
    exact_mod_cast local_decrease M W h s
  rw [real_localExpectation] at hd
  simpa only [apply_ite, Rat.cast_zero] using hd

/-- The checked rows are genuine probability mass functions. -/
noncomputable def rowPMF (M : Model S) (W : Witness S)
    (h : check M W = true) (s : S) : PMF S :=
  PMF.ofFintype (fun t => ENNReal.ofReal (M.transition s t : ℝ)) (by
    rw [← ENNReal.ofReal_sum_of_nonneg]
    · have hn : (∑ t, (M.transition s t : ℝ)) = 1 := by
        exact_mod_cast transition_normalized M W h s
      rw [hn, ENNReal.ofReal_one]
    · intro t _
      exact_mod_cast transition_nonnegative M W h s t)

theorem rowPMF_apply (M : Model S) (W : Witness S)
    (h : check M W = true) (s t : S) :
    rowPMF M W h s t = ENNReal.ofReal (M.transition s t : ℝ) := rfl

theorem rowPMF_toReal (M : Model S) (W : Witness S)
    (h : check M W = true) (s t : S) :
    (rowPMF M W h s t).toReal = (M.transition s t : ℝ) := by
  rw [rowPMF_apply, ENNReal.toReal_ofReal]
  exact_mod_cast transition_nonnegative M W h s t

theorem rowPMF_integral [MeasurableSpace S] [MeasurableSingletonClass S]
    (M : Model S) (W : Witness S) (h : check M W = true) (s : S) :
    (∫ t, (W.potential t : ℝ) ∂(rowPMF M W h s).toMeasure) =
      (localExpectation M W s : ℝ) := by
  rw [PMF.integral_eq_sum, real_localExpectation]
  apply Finset.sum_congr rfl
  intro t _
  rw [rowPMF_toReal, smul_eq_mul]

end FiniteDrift

#check @FiniteDrift.check_eq_true_iff
#check @FiniteDrift.check_sound
#check @FiniteDrift.check_complete
#check @FiniteDrift.transition_nonnegative
#check @FiniteDrift.transition_normalized
#check @FiniteDrift.potential_nonnegative
#check @FiniteDrift.potential_zero_of_good
#check @FiniteDrift.delta_positive
#check @FiniteDrift.local_decrease
#check @FiniteDrift.localExpectation_nonnegative
#check @FiniteDrift.potential_ge_delta_of_bad
#check @FiniteDrift.transition_zero_good_bad
#check @FiniteDrift.real_localExpectation
#check @FiniteDrift.real_local_decrease
#check @FiniteDrift.rowPMF_apply
#check @FiniteDrift.rowPMF_toReal
#check @FiniteDrift.rowPMF_integral
