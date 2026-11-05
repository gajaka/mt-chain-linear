/-
  Concrete independent-input execution of an exact finite update rule.

  The sample space is the infinite product of the rule's rational input
  distribution. Before step n, history contains exactly the inputs at
  indices strictly below n. Independence of input n from that history is
  proved, and supplies the fresh-input law needed by FiniteUpdate.Execution.

  Accepted drift certificates therefore bound this concrete execution from
  every fixed initial state, without assuming termination or a transition
  matrix realization. This is a fresh-row implementation. Equality in law
  with the existing per-variable-counter MT trajectory is not asserted.
-/

module

public import PPGraph.Finite.Update.Basic
public import Mathlib.Probability.Independence.InfinitePi
public import Mathlib.Probability.ConditionalExpectation

@[expose] public section

set_option linter.unusedSectionVars false

open MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal

namespace FiniteUpdate

variable {S A : Type*} [Fintype S] [DecidableEq S] [Fintype A] [DecidableEq A]
  [MeasurableSpace S] [MeasurableSingletonClass S]
  [MeasurableSpace A] [MeasurableSingletonClass A]

noncomputable def iidMeasure (R : Rule S A) (h : Valid R) : Measure (ℕ → A) :=
  Measure.infinitePi (fun _ : ℕ => (inputPMF R h).toMeasure)

instance iidMeasure_probability (R : Rule S A) (h : Valid R) :
    IsProbabilityMeasure (iidMeasure R h) := by
  unfold iidMeasure
  infer_instance

def inputHistory : Filtration ℕ (inferInstance : MeasurableSpace (ℕ → A)) where
  seq n := ⨆ k < n, MeasurableSpace.comap (fun ω : ℕ → A => ω k) inferInstance
  mono' _ _ h := biSup_mono (fun _ hk => lt_of_lt_of_le hk h)
  le' n := by
    apply iSup₂_le
    intro k _
    exact (measurable_pi_apply k).comap_le

theorem input_measurable_history (k n : ℕ) (hkn : k < n) :
    Measurable[inputHistory (A := A) n] (fun ω : ℕ → A => ω k) := by
  intro B hB
  have hle : MeasurableSpace.comap (fun ω : ℕ → A => ω k) inferInstance ≤
      inputHistory (A := A) n := le_iSup_of_le k (le_iSup_of_le hkn le_rfl)
  exact hle _ ⟨B, hB, rfl⟩

def iidTrajectory (R : Rule S A) (s₀ : S) : ℕ → (ℕ → A) → S
  | 0, _ => s₀
  | n + 1, ω => R.update (iidTrajectory R s₀ n ω) (ω n)

theorem iidTrajectory_zero (R : Rule S A) (s₀ : S) (ω : ℕ → A) :
    iidTrajectory R s₀ 0 ω = s₀ := rfl

theorem iidTrajectory_step (R : Rule S A) (s₀ : S) (n : ℕ) (ω : ℕ → A) :
    iidTrajectory R s₀ (n + 1) ω = R.update (iidTrajectory R s₀ n ω) (ω n) := rfl

theorem iidTrajectory_adapted (R : Rule S A) (s₀ : S) (n : ℕ) :
    Measurable[inputHistory (A := A) n] (iidTrajectory R s₀ n) := by
  induction n with
  | zero => exact measurable_const
  | succ n ih =>
    have hx := ih.mono (inputHistory.mono (Nat.le_succ n)) le_rfl
    have hy := input_measurable_history (A := A) n (n + 1) (Nat.lt_succ_self n)
    exact (measurable_of_finite (fun p : S × A => R.update p.1 p.2)).comp (hx.prodMk hy)

theorem iid_inputs_independent (R : Rule S A) (h : Valid R) :
    iIndepFun (fun n (ω : ℕ → A) => ω n) (iidMeasure R h) :=
  iIndepFun_infinitePi (X := fun (_ : ℕ) (a : A) => a) (fun _ => measurable_id)

theorem iid_input_independent_history (R : Rule S A) (h : Valid R) (n : ℕ) :
    Indep (MeasurableSpace.comap (fun ω : ℕ → A => ω n) inferInstance)
      (inputHistory (A := A) n) (iidMeasure R h) := by
  have hh := indep_iSup_of_disjoint
    (fun k : ℕ => (show Measurable (fun ω : ℕ → A => ω k) from
      measurable_pi_apply k).comap_le)
    (iid_inputs_independent R h)
    (S := ({n} : Set ℕ)) (T := {k | k < n}) (by
      apply Set.disjoint_left.mpr
      intro k hk hlt
      have heq : k = n := Set.mem_singleton_iff.mp hk
      exact Nat.lt_irrefl n (heq ▸ hlt))
  simpa only [iSup_singleton, inputHistory, Set.mem_ofPred_eq] using hh

theorem iid_input_map (R : Rule S A) (h : Valid R) (n : ℕ) :
    (iidMeasure R h).map (fun ω : ℕ → A => ω n) = (inputPMF R h).toMeasure :=
  Measure.infinitePi_map_eval (fun _ : ℕ => (inputPMF R h).toMeasure) n

theorem iid_input_indicator_integral (R : Rule S A) (h : Valid R) (n : ℕ) (a : A) :
    (∫ ω, FiniteDrift.stateIndicator (fun ω : ℕ → A => ω n) a ω ∂iidMeasure R h) =
      (R.mass a : ℝ) := by
  have hm : MeasurableSet {ω : ℕ → A | ω n = a} :=
    (show Measurable (fun ω : ℕ → A => ω n) from
      measurable_pi_apply n) (measurableSet_singleton a)
  rw [FiniteDrift.stateIndicator, integral_indicator_const (1 : ℝ) hm]
  simp only [smul_eq_mul, mul_one, measureReal_def]
  have heq : (iidMeasure R h) {ω : ℕ → A | ω n = a} = inputPMF R h a := by
    rw [← PMF.toMeasure_apply_singleton _ a (measurableSet_singleton a),
      ← iid_input_map R h n, Measure.map_apply (measurable_pi_apply n)
        (measurableSet_singleton a)]
    rfl
  rw [heq, inputPMF_toReal]

/-- Freshness follows from the constructed product measure, not a certificate field. -/
theorem iid_input_fresh (R : Rule S A) (h : Valid R) (n : ℕ) (a : A) :
    (iidMeasure R h)[FiniteDrift.stateIndicator (fun ω : ℕ → A => ω n) a |
      inputHistory (A := A) n] =ᵐ[iidMeasure R h] fun _ => (R.mass a : ℝ) := by
  have hm : MeasurableSet[MeasurableSpace.comap (fun ω : ℕ → A => ω n) inferInstance]
      {ω : ℕ → A | ω n = a} :=
    (comap_measurable (fun ω : ℕ → A => ω n)) (measurableSet_singleton a)
  have hf : StronglyMeasurable[
      MeasurableSpace.comap (fun ω : ℕ → A => ω n) inferInstance]
      (FiniteDrift.stateIndicator (fun ω : ℕ → A => ω n) a) :=
    stronglyMeasurable_const.indicator hm
  have hc := condExp_indep_eq (measurable_pi_apply n).comap_le
    ((inputHistory (A := A)).le n) hf (iid_input_independent_history R h n)
  simpa only [iid_input_indicator_integral] using hc

theorem iidExecution (R : Rule S A) (h : Valid R) (s₀ : S) :
    Execution R (iidMeasure R h) (inputHistory (A := A))
      (iidTrajectory R s₀) (fun n ω => ω n) where
  adapted := iidTrajectory_adapted R s₀
  draw_measurable := fun n => measurable_pi_apply n
  step := iidTrajectory_step R s₀
  fresh := iid_input_fresh R h

theorem iidRealization (R : Rule S A) (h : Valid R) (s₀ : S) :
    FiniteDrift.Realization (model R) (iidMeasure R h) (inputHistory (A := A))
      (iidTrajectory R s₀) :=
  toRealization R (iidMeasure R h) (inputHistory (A := A))
    (iidTrajectory R s₀) (fun n ω => ω n) (iidExecution R h s₀)

theorem iid_expectedHitCount_le (R : Rule S A) (h : Valid R)
    (W : FiniteDrift.Witness S) (hc : check R W = true) (s₀ : S) :
    FiniteDrift.expectedHitCount (model R) (iidMeasure R h) (iidTrajectory R s₀) ≤
      ENNReal.ofReal (W.potential s₀ : ℝ) / ENNReal.ofReal (W.delta : ℝ) :=
  FiniteDrift.expectedHitCount_fixed_le (model R) W hc (iidMeasure R h)
    (inputHistory (A := A)) (iidTrajectory R s₀) (iidRealization R h s₀) s₀ (fun _ => rfl)

theorem iid_expectedHitCount_lt_top (R : Rule S A) (h : Valid R)
    (W : FiniteDrift.Witness S) (hc : check R W = true) (s₀ : S) :
    FiniteDrift.expectedHitCount (model R) (iidMeasure R h) (iidTrajectory R s₀) < ⊤ :=
  FiniteDrift.expectedHitCount_lt_top (model R) W hc (iidMeasure R h)
    (inputHistory (A := A)) (iidTrajectory R s₀) (iidRealization R h s₀)

theorem iid_ae_exists_good (R : Rule S A) (h : Valid R)
    (W : FiniteDrift.Witness S) (hc : check R W = true) (s₀ : S) :
    ∀ᵐ ω ∂iidMeasure R h, ∃ T, R.good (iidTrajectory R s₀ T ω) = true :=
  FiniteDrift.ae_exists_good (model R) W hc (iidMeasure R h)
    (inputHistory (A := A)) (iidTrajectory R s₀) (iidRealization R h s₀)

theorem iid_measure_success_eq_one (R : Rule S A) (h : Valid R)
    (W : FiniteDrift.Witness S) (hc : check R W = true) (s₀ : S) :
    iidMeasure R h {ω | ∃ T, R.good (iidTrajectory R s₀ T ω) = true} = 1 :=
  FiniteDrift.measure_success_eq_one (model R) W hc (iidMeasure R h)
    (inputHistory (A := A)) (iidTrajectory R s₀) (iidRealization R h s₀)

end FiniteUpdate

#check @FiniteUpdate.input_measurable_history
#check @FiniteUpdate.iidTrajectory_zero
#check @FiniteUpdate.iidTrajectory_step
#check @FiniteUpdate.iidTrajectory_adapted
#check @FiniteUpdate.iid_inputs_independent
#check @FiniteUpdate.iid_input_independent_history
#check @FiniteUpdate.iid_input_map
#check @FiniteUpdate.iid_input_indicator_integral
#check @FiniteUpdate.iid_input_fresh
#check @FiniteUpdate.iidExecution
#check @FiniteUpdate.iidRealization
#check @FiniteUpdate.iid_expectedHitCount_le
#check @FiniteUpdate.iid_expectedHitCount_lt_top
#check @FiniteUpdate.iid_ae_exists_good
#check @FiniteUpdate.iid_measure_success_eq_one
