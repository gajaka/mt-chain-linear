/-
  Exact transition kernels derived from a finite randomized update.

  Inputs are the probability of each fresh input, the deterministic update,
  and the unchanged good-state test. The transition matrix is computed by
  summing the input probabilities over the fibers of the actual update.
  No transition matrix or expected-decrease conclusion is an input field.

  A process bridge derives FiniteDrift.Realization from adaptation, execution
  of this update, and the conditional law of its fresh input. Freshness is
  a separate probability-law obligation, not an assumption of convergence.
  This file does not assert the law of the existing counter-indexed MT table
  execution or of a physical controller.
-/

module

public import PPGraph.Finite.Drift.Process
public import Mathlib.MeasureTheory.Function.ConditionalExpectation.PullOut

@[expose] public section

set_option linter.unusedSectionVars false

open MeasureTheory
open scoped ENNReal NNReal

namespace FiniteUpdate

variable {S A : Type*} [Fintype S] [DecidableEq S] [Fintype A] [DecidableEq A]

structure Rule (S A : Type*) where
  mass : A → ℚ
  update : S → A → S
  good : S → Bool

def Valid (R : Rule S A) : Prop :=
  (∀ a, 0 ≤ R.mass a) ∧ ∑ a, R.mass a = 1

def kernel (R : Rule S A) (s t : S) : ℚ :=
  ∑ a, if R.update s a = t then R.mass a else 0

def model (R : Rule S A) : FiniteDrift.Model S where
  transition := kernel R
  good := R.good

theorem kernel_nonnegative (R : Rule S A) (h : Valid R) (s t : S) :
    0 ≤ kernel R s t := by
  apply Finset.sum_nonneg
  intro a _
  split_ifs
  · exact h.1 a
  · exact le_rfl

theorem kernel_normalized (R : Rule S A) (h : Valid R) (s : S) :
    ∑ t, kernel R s t = 1 := by
  simp only [kernel]
  rw [Finset.sum_comm]
  simpa using h.2

theorem kernel_zero_of_unreachable (R : Rule S A) (s t : S)
    (h : ∀ a, R.update s a ≠ t) : kernel R s t = 0 := by
  simp [kernel, h]

theorem kernel_eq_pure_of_fixed (R : Rule S A) (h : Valid R) (s : S)
    (hfixed : ∀ a, R.update s a = s) (t : S) :
    kernel R s t = if s = t then 1 else 0 := by
  simp only [kernel, hfixed]
  split_ifs with ht
  · simpa using h.2
  · simp

theorem weighted_next_value (R : Rule S A) (f : S → ℚ) (s : S) :
    (∑ t, kernel R s t * f t) = ∑ a, R.mass a * f (R.update s a) := by
  simp only [kernel, Finset.sum_mul]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro a _
  simp [ite_mul]

theorem localExpectation_eq_update (R : Rule S A) (W : FiniteDrift.Witness S) (s : S) :
    FiniteDrift.localExpectation (model R) W s =
      ∑ a, R.mass a * W.potential (R.update s a) :=
  weighted_next_value R W.potential s

/-- This checker computes the matrix from the update, rather than trusting an export. -/
def check (R : Rule S A) (W : FiniteDrift.Witness S) : Bool :=
  FiniteDrift.check (model R) W

theorem check_eq_true_iff (R : Rule S A) (h : Valid R) (W : FiniteDrift.Witness S) :
    check R W = true ↔
      (∀ s, 0 ≤ W.potential s) ∧
      (∀ s, R.good s = true → W.potential s = 0) ∧
      0 < W.delta ∧
      ∀ s, (∑ a, R.mass a * W.potential (R.update s a)) +
        (if R.good s then 0 else W.delta) ≤ W.potential s := by
  rw [check, FiniteDrift.check_eq_true_iff]
  constructor
  · rintro ⟨_, _, hp, hz, hd, hdec⟩
    refine ⟨hp, hz, hd, ?_⟩
    intro s
    have hs := hdec s
    rw [localExpectation_eq_update] at hs
    exact hs
  · rintro ⟨hp, hz, hd, hdec⟩
    refine ⟨kernel_nonnegative R h, kernel_normalized R h, hp, hz, hd, ?_⟩
    intro s
    rw [localExpectation_eq_update]
    exact hdec s

noncomputable def inputPMF (R : Rule S A) (h : Valid R) : PMF A :=
  PMF.ofFintype (fun a => ENNReal.ofReal (R.mass a : ℝ)) (by
    rw [← ENNReal.ofReal_sum_of_nonneg]
    · have hn : (∑ a, (R.mass a : ℝ)) = 1 := by exact_mod_cast h.2
      rw [hn, ENNReal.ofReal_one]
    · intro a _
      exact_mod_cast h.1 a)

theorem inputPMF_toReal (R : Rule S A) (h : Valid R) (a : A) :
    (inputPMF R h a).toReal = (R.mass a : ℝ) := by
  rw [inputPMF, PMF.ofFintype_apply, ENNReal.toReal_ofReal]
  exact_mod_cast h.1 a

noncomputable def nextPMF (R : Rule S A) (h : Valid R) (s : S) : PMF S :=
  (inputPMF R h).map (R.update s)

theorem nextPMF_apply (R : Rule S A) (h : Valid R) (s t : S) :
    nextPMF R h s t = ENNReal.ofReal (kernel R s t : ℝ) := by
  rw [nextPMF, PMF.map_apply, tsum_fintype, kernel]
  simp only [Rat.cast_sum]
  rw [ENNReal.ofReal_sum_of_nonneg]
  · apply Finset.sum_congr rfl
    intro a _
    simp only [inputPMF, PMF.ofFintype_apply]
    by_cases he : R.update s a = t
    · simp [he]
    · simp [he, Ne.symm he]
  · intro a _
    split_ifs
    · exact_mod_cast h.1 a
    · simp

theorem nextPMF_toReal (R : Rule S A) (h : Valid R) (s t : S) :
    (nextPMF R h s t).toReal = (kernel R s t : ℝ) := by
  rw [nextPMF_apply, ENNReal.toReal_ofReal]
  exact_mod_cast kernel_nonnegative R h s t

theorem nextPMF_eq_checked_row (R : Rule S A) (h : Valid R)
    (W : FiniteDrift.Witness S) (hc : check R W = true) (s : S) :
    nextPMF R h s = FiniteDrift.rowPMF (model R) W hc s := by
  ext t
  exact nextPMF_apply R h s t

section Process

variable {Ω : Type*} [MeasurableSpace S] [MeasurableSingletonClass S]
  [MeasurableSpace A] [MeasurableSingletonClass A] [mΩ : MeasurableSpace Ω]

/-- Only execution and the fresh-input law; no drift or repair conclusion. -/
structure Execution (R : Rule S A) (μ : Measure Ω)
    (history : Filtration ℕ mΩ) (X : ℕ → Ω → S) (draw : ℕ → Ω → A) : Prop where
  adapted : ∀ n, Measurable[history n] (X n)
  draw_measurable : ∀ n, Measurable (draw n)
  step : ∀ n ω, X (n + 1) ω = R.update (X n ω) (draw n ω)
  fresh : ∀ n a,
    μ[FiniteDrift.stateIndicator (draw n) a | history n] =ᵐ[μ]
      fun _ => (R.mass a : ℝ)

theorem next_indicator_expansion (R : Rule S A) (X : Ω → S) (Y : Ω → A) (t : S) :
    FiniteDrift.stateIndicator (fun ω => R.update (X ω) (Y ω)) t =
      ∑ a, (fun ω => if R.update (X ω) a = t then (1 : ℝ) else 0) *
        FiniteDrift.stateIndicator Y a := by
  funext ω
  simp [FiniteDrift.stateIndicator, Finset.sum_apply, Pi.mul_apply,
    Set.indicator_apply, eq_comm]

theorem execution_transition (R : Rule S A) (μ : Measure Ω) [IsFiniteMeasure μ]
    (history : Filtration ℕ mΩ) (X : ℕ → Ω → S) (draw : ℕ → Ω → A)
    (E : Execution R μ history X draw) (n : ℕ) (t : S) :
    μ[FiniteDrift.stateIndicator (X (n + 1)) t | history n] =ᵐ[μ]
      fun ω => (kernel R (X n ω) t : ℝ) := by
  let f (a : A) : Ω → ℝ := fun ω => if R.update (X n ω) a = t then 1 else 0
  have hf (a : A) : StronglyMeasurable[history n] (f a) :=
    ((measurable_of_finite (fun s => if R.update s a = t then (1 : ℝ) else 0)).comp
      (E.adapted n)).stronglyMeasurable
  have hi (a : A) : Integrable (FiniteDrift.stateIndicator (draw n) a) μ :=
    (integrable_const (1 : ℝ)).indicator (E.draw_measurable n (measurableSet_singleton a))
  have hp (a : A) : Integrable (f a * FiniteDrift.stateIndicator (draw n) a) μ := by
    exact (hi a).bdd_mul ((hf a).measurable.mono (history.le n) le_rfl).aestronglyMeasurable
      (c := 1) (Filter.Eventually.of_forall (fun ω => by
        dsimp [f]
        split_ifs <;> norm_num))
  have hexp : FiniteDrift.stateIndicator (X (n + 1)) t =
      ∑ a, f a * FiniteDrift.stateIndicator (draw n) a := by
    have he : X (n + 1) = fun ω => R.update (X n ω) (draw n ω) := funext (E.step n)
    rw [he]
    exact next_indicator_expansion R (X n) (draw n) t
  rw [hexp]
  have hs := condExp_finsetSum (fun a (_ : a ∈ Finset.univ) => hp a) (history n)
  have ht (a : A) :
      μ[f a * FiniteDrift.stateIndicator (draw n) a | history n] =ᵐ[μ]
        fun ω => f a ω * (R.mass a : ℝ) := by
    filter_upwards [condExp_mul_of_stronglyMeasurable_left (hf a) (hp a) (hi a),
      E.fresh n a] with ω hmul hfresh
    simp only [hmul, Pi.mul_apply, hfresh]
  filter_upwards [hs, ae_all_iff.mpr ht] with ω hsum hterm
  simp only [Finset.sum_apply] at hsum
  rw [hsum]
  simp only [kernel, Rat.cast_sum]
  apply Finset.sum_congr rfl
  intro a _
  rw [hterm a]
  dsimp [f]
  split_ifs <;> simp

/-- The transition-law obligation of yesterday's checker is now derived. -/
theorem toRealization (R : Rule S A) (μ : Measure Ω) [IsFiniteMeasure μ]
    (history : Filtration ℕ mΩ) (X : ℕ → Ω → S) (draw : ℕ → Ω → A)
    (E : Execution R μ history X draw) :
    FiniteDrift.Realization (model R) μ history X where
  adapted := E.adapted
  transition := execution_transition R μ history X draw E

theorem execution_expectedHitCount_le (R : Rule S A) (W : FiniteDrift.Witness S)
    (hc : check R W = true) (μ : Measure Ω) [IsFiniteMeasure μ]
    (history : Filtration ℕ mΩ) (X : ℕ → Ω → S) (draw : ℕ → Ω → A)
    (E : Execution R μ history X draw) :
    FiniteDrift.expectedHitCount (model R) μ X ≤
      ENNReal.ofReal (∫ ω, (W.potential (X 0 ω) : ℝ) ∂μ) /
        ENNReal.ofReal (W.delta : ℝ) :=
  FiniteDrift.expectedHitCount_le (model R) W hc μ history X
    (toRealization R μ history X draw E)

theorem execution_ae_exists_good (R : Rule S A) (W : FiniteDrift.Witness S)
    (hc : check R W = true) (μ : Measure Ω) [IsFiniteMeasure μ]
    (history : Filtration ℕ mΩ) (X : ℕ → Ω → S) (draw : ℕ → Ω → A)
    (E : Execution R μ history X draw) : ∀ᵐ ω ∂μ, ∃ T, R.good (X T ω) = true :=
  FiniteDrift.ae_exists_good (model R) W hc μ history X
    (toRealization R μ history X draw E)

end Process
end FiniteUpdate

#check @FiniteUpdate.kernel_nonnegative
#check @FiniteUpdate.kernel_normalized
#check @FiniteUpdate.kernel_zero_of_unreachable
#check @FiniteUpdate.kernel_eq_pure_of_fixed
#check @FiniteUpdate.weighted_next_value
#check @FiniteUpdate.localExpectation_eq_update
#check @FiniteUpdate.check_eq_true_iff
#check @FiniteUpdate.inputPMF_toReal
#check @FiniteUpdate.nextPMF_apply
#check @FiniteUpdate.nextPMF_toReal
#check @FiniteUpdate.nextPMF_eq_checked_row
#check @FiniteUpdate.next_indicator_expansion
#check @FiniteUpdate.execution_transition
#check @FiniteUpdate.toRealization
#check @FiniteUpdate.execution_expectedHitCount_le
#check @FiniteUpdate.execution_ae_exists_good
