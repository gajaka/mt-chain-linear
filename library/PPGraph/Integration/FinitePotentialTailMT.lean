/-
  Tail and negative certificates for the existing finite MT log process.
  The adaptive-table law is proved upstream. Bounds count resamplings;
  no independence of whole trajectories, LLL criterion, physical response
  law, or hardware execution time is supplied as a premise or conclusion.
-/

module

public import PPGraph.Finite.Potential.TailCertificate
public import PPGraph.Integration.FinitePotentialExpectationMT

@[expose] public section

set_option linter.unusedSectionVars false
set_option backward.isDefEq.respectTransparency false

open MeasureTheory
open scoped ENNReal NNReal

namespace FiniteResampling

variable {V : Type} [Fintype V] [DecidableEq V]
  {D : V → Type} [∀ v, Fintype (D v)] [∀ v, DecidableEq (D v)]
  [∀ v, MeasurableSpace (D v)] [∀ v, MeasurableSingletonClass (D v)]

theorem table_timeout_eq_survival (Q : Marginals D) (h : Valid Q) (P : Policy D)
    (init : LogSpace (varSpaces Q h) → State D) (hi : Measurable init)
    (hl : FiniteTable.InitialLocal init) (N : ℕ) :
    logMeasure (varSpaces Q h) {ω | (N : ℝ≥0∞) <
      FiniteDrift.hitCount (FiniteUpdate.model (rule Q P))
        (FiniteTable.trajectory (activeFootprint P) init) ω} =
      ENNReal.ofReal (∫ ω, (FinitePotential.survival (FiniteUpdate.model (rule Q P))
        N (init ω) : ℝ) ∂logMeasure (varSpaces Q h)) := by
  have hh := FinitePotential.running_measure_eq_survival (FiniteUpdate.model (rule Q P))
    (logMeasure (varSpaces Q h)) (FiniteTable.history (activeFootprint P) init hi)
    (FiniteTable.trajectory (activeFootprint P) init) (tableRealization Q h P init hi hl) N
  rw [FinitePotential.runningEvent_eq_hitCount_gt] at hh
  simpa only [FiniteTable.trajectory_zero] using hh

variable {I : Type} [Fintype I] [DecidableEq I] [Nonempty I]

theorem TLog_timeout_eq_survival (Q : Marginals D) (h : Valid Q) (B : Problem D I)
    (s₀ : State D) (N : ℕ) :
    logMeasure (varSpaces Q h) {ω | (N : ℝ≥0∞) < TLog (mtProcess Q h B) s₀ ω} =
      ENNReal.ofReal (FinitePotential.survival
        (FiniteUpdate.model (rule Q (firstPolicy Q h B))) N s₀ : ℝ) := by
  have hh := table_timeout_eq_survival Q h (firstPolicy Q h B)
    (fun _ => s₀) measurable_const (FiniteTable.initialLocal_const (S := varSpaces Q h) s₀) N
  simpa only [table_hitCount_eq_TLog, integral_const, probReal_univ, one_smul] using hh

theorem randomInitTLog_timeout_eq_sum (Q : Marginals D) (h : Valid Q)
    (B : Problem D I) (N : ℕ) :
    logMeasure (varSpaces Q h) {ω | (N : ℝ≥0∞) < randomInitTLog (mtProcess Q h B) ω} =
      ENNReal.ofReal ((∑ s, productMass Q s * FinitePotential.survival
        (FiniteUpdate.model (rule Q (firstPolicy Q h B))) N s : ℚ) : ℝ) := by
  have hh := table_timeout_eq_survival Q h (firstPolicy Q h B)
    initialStateFromLog measurable_initialStateFromLog (initialStateFromLog_local Q h) N
  rw [initialStateFromLog_integral_eq_sum Q h (firstPolicy Q h B)] at hh
  simpa only [table_hitCount_eq_TLog, randomInitTLog, Rat.cast_sum, Rat.cast_mul] using hh

theorem TLog_timeout_le_mean_div (Q : Marginals D) (h : Valid Q)
    (B : Problem D I) (s₀ : State D) (N : ℕ) :
    logMeasure (varSpaces Q h) {ω | (N : ℝ≥0∞) < TLog (mtProcess Q h B) s₀ ω} ≤
      ETLog (mtProcess Q h B) s₀ / (N + 1) := by
  have L := tableRealization Q h (firstPolicy Q h B) (fun _ => s₀) measurable_const
    (FiniteTable.initialLocal_const (S := varSpaces Q h) s₀)
  have hX := FiniteDrift.realization_measurable
    (FiniteUpdate.model (rule Q (firstPolicy Q h B))) (logMeasure (varSpaces Q h)) _ _ L
  have hh := FinitePotential.running_measure_le_mean_div
    (FiniteUpdate.model (rule Q (firstPolicy Q h B))) (logMeasure (varSpaces Q h)) _ hX N
  rw [FinitePotential.runningEvent_eq_hitCount_gt] at hh
  simpa only [table_hitCount_eq_TLog, FiniteDrift.expectedHitCount, ETLog] using hh

theorem randomInitTLog_timeout_le_mean_div (Q : Marginals D) (h : Valid Q)
    (B : Problem D I) (N : ℕ) :
    logMeasure (varSpaces Q h) {ω | (N : ℝ≥0∞) < randomInitTLog (mtProcess Q h B) ω} ≤
      randomInitETLog (mtProcess Q h B) / (N + 1) := by
  have L := tableRealization Q h (firstPolicy Q h B) initialStateFromLog
    measurable_initialStateFromLog (initialStateFromLog_local Q h)
  have hX := FiniteDrift.realization_measurable
    (FiniteUpdate.model (rule Q (firstPolicy Q h B))) (logMeasure (varSpaces Q h)) _ _ L
  have hh := FinitePotential.running_measure_le_mean_div
    (FiniteUpdate.model (rule Q (firstPolicy Q h B))) (logMeasure (varSpaces Q h)) _ hX N
  rw [FinitePotential.runningEvent_eq_hitCount_gt] at hh
  simpa only [table_hitCount_eq_TLog, FiniteDrift.expectedHitCount,
    randomInitTLog, randomInitETLog] using hh

theorem TLog_timeout_blocks_le (Q : Marginals D) (h : Valid Q) (B : Problem D I)
    (Lblock : ℕ) (b : ℚ) (hb0 : 0 ≤ b)
    (hb : ∀ s, FinitePotential.survival
      (FiniteUpdate.model (rule Q (firstPolicy Q h B))) Lblock s ≤ b)
    (s₀ : State D) (k : ℕ) :
    logMeasure (varSpaces Q h) {ω | ((k * Lblock : ℕ) : ℝ≥0∞) < TLog (mtProcess Q h B) s₀ ω} ≤
      ENNReal.ofReal (b ^ k : ℝ) := by
  rw [TLog_timeout_eq_survival Q h B s₀ (k * Lblock)]
  apply ENNReal.ofReal_le_ofReal
  exact_mod_cast FinitePotential.survival_blocks_le _ (model_stochastic Q h _)
    Lblock b hb0 hb k s₀

theorem TLog_timeout_checkedTable_blocks_le (Q : Marginals D) (h : Valid Q)
    (B : Problem D I) (F : ℕ → State D → ℚ) (H : ℕ)
    (hc : FinitePotential.checkSurvivalTable (FiniteUpdate.model (rule Q (firstPolicy Q h B))) F H = true)
    (b : ℚ) (hb0 : 0 ≤ b) (hb : ∀ s, F H s ≤ b) (s₀ : State D) (k : ℕ) :
    logMeasure (varSpaces Q h) {ω | ((k * H : ℕ) : ℝ≥0∞) < TLog (mtProcess Q h B) s₀ ω} ≤
      ENNReal.ofReal (b ^ k : ℝ) :=
  TLog_timeout_blocks_le Q h B H b hb0 (fun s => by
    rw [← FinitePotential.checkedSurvivalTable_exact _ F H hc s]; exact hb s) s₀ k

theorem randomInitTLog_timeout_blocks_le (Q : Marginals D) (h : Valid Q) (B : Problem D I)
    (Lblock : ℕ) (b : ℚ) (hb0 : 0 ≤ b)
    (hb : ∀ s, FinitePotential.survival
      (FiniteUpdate.model (rule Q (firstPolicy Q h B))) Lblock s ≤ b) (k : ℕ) :
    logMeasure (varSpaces Q h) {ω | ((k * Lblock : ℕ) : ℝ≥0∞) < randomInitTLog (mtProcess Q h B) ω} ≤
      ENNReal.ofReal (b ^ k : ℝ) := by
  have L := tableRealization Q h (firstPolicy Q h B) initialStateFromLog
    measurable_initialStateFromLog (initialStateFromLog_local Q h)
  have hh := FinitePotential.running_measure_blocks_le _ (model_stochastic Q h _)
    Lblock b hb0 hb (logMeasure (varSpaces Q h)) _ _ L k
  rw [FinitePotential.runningEvent_eq_hitCount_gt] at hh
  simpa only [table_hitCount_eq_TLog, randomInitTLog] using hh

theorem ETLog_checkedClosedBad_eq_top (Q : Marginals D) (h : Valid Q) (B : Problem D I)
    (U : State D → Bool)
    (hc : FinitePotential.checkClosedBad (FiniteUpdate.model (rule Q (firstPolicy Q h B))) U = true)
    (s₀ : State D) (hs : U s₀ = true) : ETLog (mtProcess Q h B) s₀ = ⊤ := by
  have hh := FinitePotential.expectedHitCount_closedBad_eq_top _ (model_stochastic Q h _)
    U hc (logMeasure (varSpaces Q h))
    (FiniteTable.history (activeFootprint (firstPolicy Q h B)) (fun _ => s₀) measurable_const)
    (FiniteTable.trajectory (activeFootprint (firstPolicy Q h B)) (fun _ => s₀))
    (tableRealization Q h _ (fun _ => s₀) measurable_const
      (FiniteTable.initialLocal_const (S := varSpaces Q h) s₀)) s₀ hs
    (fun _ => FiniteTable.trajectory_zero _ _ _)
  simpa only [FiniteDrift.expectedHitCount, table_hitCount_eq_TLog, ETLog] using hh

end FiniteResampling

#check @FiniteResampling.table_timeout_eq_survival
#check @FiniteResampling.TLog_timeout_eq_survival
#check @FiniteResampling.randomInitTLog_timeout_eq_sum
#check @FiniteResampling.TLog_timeout_le_mean_div
#check @FiniteResampling.randomInitTLog_timeout_le_mean_div
#check @FiniteResampling.TLog_timeout_blocks_le
#check @FiniteResampling.TLog_timeout_checkedTable_blocks_le
#check @FiniteResampling.randomInitTLog_timeout_blocks_le
#check @FiniteResampling.ETLog_checkedClosedBad_eq_top
