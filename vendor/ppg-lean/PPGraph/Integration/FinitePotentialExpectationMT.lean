/-
  Exact mean work of the existing finite Moser--Tardos process.

  First-step equations, not merely drift inequalities, identify the exact
  mean. The previously proved adaptive-counter law and pointwise equality
  of stopped hitCount with legacy TLog transfer that identity. Slot-zero
  initialization has the declared product law, so its mean is an exact
  finite rational weighted sum. No termination hypothesis or LLL criterion
  is used. These statements count resamplings, not physical elapsed time.
-/

module

public import PPGraph.Finite.Potential.Expectation
public import PPGraph.Integration.FinitePotentialMT

@[expose] public section

set_option linter.unusedSectionVars false
set_option backward.isDefEq.respectTransparency false

open MeasureTheory
open scoped ENNReal NNReal

namespace FiniteResampling

variable {V : Type} [Fintype V] [DecidableEq V]
  {D : V → Type} [∀ v, Fintype (D v)] [∀ v, DecidableEq (D v)]
  [∀ v, MeasurableSpace (D v)] [∀ v, MeasurableSingletonClass (D v)]

theorem table_expectedHitCount_eq_of_equations (Q : Marginals D) (h : Valid Q)
    (P : Policy D) (f : State D → ℚ)
    (he : FinitePotential.Equations (FiniteUpdate.model (rule Q P)) f)
    (init : LogSpace (varSpaces Q h) → State D) (hi : Measurable init)
    (hl : FiniteTable.InitialLocal init) :
    FiniteDrift.expectedHitCount (FiniteUpdate.model (rule Q P)) (logMeasure (varSpaces Q h))
      (FiniteTable.trajectory (activeFootprint P) init) =
      ENNReal.ofReal (∫ ω, (f (init ω) : ℝ) ∂logMeasure (varSpaces Q h)) := by
  have hb := FinitePotential.expectedHitCount_eq_of_equations _ f
    (model_stochastic Q h P) (model_absorbing Q h P) he (logMeasure (varSpaces Q h))
    (FiniteTable.history (activeFootprint P) init hi)
    (FiniteTable.trajectory (activeFootprint P) init) (tableRealization Q h P init hi hl)
  simpa only [FiniteTable.trajectory_zero] using hb

/-- The initialization used by legacy MT has exactly the declared product mass. -/
theorem initialStateFromLog_integral_eq_sum (Q : Marginals D) (h : Valid Q)
    (P : Policy D) (f : State D → ℚ) :
    (∫ ω, (f (initialStateFromLog ω) : ℝ) ∂logMeasure (varSpaces Q h)) =
      ∑ s, (productMass Q s : ℝ) * (f s : ℝ) := by
  have hf : Measurable (fun s : MTState (varSpaces Q h) => (f s : ℝ)) := measurable_of_finite _
  have hmap : (logMeasure (varSpaces Q h)).map (initialStateFromLog (S := varSpaces Q h)) =
      (FiniteUpdate.inputPMF (rule Q P) (rule_valid Q h P)).toMeasure := by
    have hd : (logMeasure (varSpaces Q h)).map (initialStateFromLog (S := varSpaces Q h)) =
        FiniteTable.productLaw (varSpaces Q h) := FiniteTable.fixedDraw_map (fun _ => 0)
    rw [hd]
    change Measure.pi (fun v => (marginalPMF Q h v).toMeasure) = _
    exact (inputMeasure_eq_product Q h P).symm
  calc
    _ = ∫ s, (f s : ℝ) ∂(logMeasure (varSpaces Q h)).map initialStateFromLog := by
      symm
      exact integral_map measurable_initialStateFromLog.aemeasurable hf.aestronglyMeasurable
    _ = ∫ s, (f s : ℝ) ∂(FiniteUpdate.inputPMF (rule Q P) (rule_valid Q h P)).toMeasure := by
      rw [hmap]
      rfl
    _ = _ := by
      rw [PMF.integral_eq_sum]
      apply Finset.sum_congr rfl
      intro s _
      rw [FiniteUpdate.inputPMF_toReal, smul_eq_mul]
      rfl

variable {I : Type} [Fintype I] [DecidableEq I] [Nonempty I]

theorem ETLog_eq_of_equations (Q : Marginals D) (h : Valid Q) (B : Problem D I)
    (f : State D → ℚ)
    (he : FinitePotential.Equations (FiniteUpdate.model (rule Q (firstPolicy Q h B))) f)
    (s₀ : State D) : ETLog (mtProcess Q h B) s₀ = ENNReal.ofReal (f s₀ : ℝ) := by
  have hb := table_expectedHitCount_eq_of_equations Q h (firstPolicy Q h B) f he
    (fun _ => s₀) measurable_const (FiniteTable.initialLocal_const (S := varSpaces Q h) s₀)
  have ht : FiniteDrift.expectedHitCount (FiniteUpdate.model (rule Q (firstPolicy Q h B)))
      (logMeasure (varSpaces Q h))
      (FiniteTable.trajectory (activeFootprint (firstPolicy Q h B)) (fun _ => s₀)) =
      ETLog (mtProcess Q h B) s₀ :=
    lintegral_congr (table_hitCount_eq_TLog Q h B (fun _ => s₀))
  rw [ht] at hb
  simpa only [integral_const, probReal_univ, one_smul] using hb

theorem randomInitETLog_eq_of_equations (Q : Marginals D) (h : Valid Q) (B : Problem D I)
    (f : State D → ℚ)
    (he : FinitePotential.Equations (FiniteUpdate.model (rule Q (firstPolicy Q h B))) f) :
    randomInitETLog (mtProcess Q h B) =
      ENNReal.ofReal (∫ ω, (f (initialStateFromLog ω) : ℝ) ∂logMeasure (varSpaces Q h)) := by
  have hb := table_expectedHitCount_eq_of_equations Q h (firstPolicy Q h B) f he
    initialStateFromLog measurable_initialStateFromLog (initialStateFromLog_local Q h)
  change (∫⁻ ω, _ ∂logMeasure (varSpaces Q h)) = _ at hb
  simpa only [table_hitCount_eq_TLog, randomInitETLog, randomInitTLog] using hb

theorem randomInitETLog_eq_rational_sum_of_equations (Q : Marginals D) (h : Valid Q)
    (B : Problem D I) (f : State D → ℚ)
    (he : FinitePotential.Equations (FiniteUpdate.model (rule Q (firstPolicy Q h B))) f) :
    randomInitETLog (mtProcess Q h B) =
      ENNReal.ofReal ((∑ s, productMass Q s * f s : ℚ) : ℝ) := by
  rw [randomInitETLog_eq_of_equations Q h B f he,
    initialStateFromLog_integral_eq_sum Q h (firstPolicy Q h B) f]
  simp only [Rat.cast_sum, Rat.cast_mul]

theorem ETLog_eq_potential (Q : Marginals D) (h : Valid Q) (B : Problem D I)
    (hr : FinitePotential.Accessible (FiniteUpdate.model (rule Q (firstPolicy Q h B))))
    (s₀ : State D) : ETLog (mtProcess Q h B) s₀ =
      ENNReal.ofReal (FinitePotential.potential
        (FiniteUpdate.model (rule Q (firstPolicy Q h B))) s₀ : ℝ) :=
  ETLog_eq_of_equations Q h B _ (FinitePotential.potential_equations _
    (FinitePotential.det_ne_zero_of_accessible _ (model_stochastic Q h _) hr)) s₀

theorem randomInitETLog_eq_potential_sum (Q : Marginals D) (h : Valid Q) (B : Problem D I)
    (hr : FinitePotential.Accessible (FiniteUpdate.model (rule Q (firstPolicy Q h B)))) :
    randomInitETLog (mtProcess Q h B) = ENNReal.ofReal
      ((∑ s, productMass Q s * FinitePotential.potential
        (FiniteUpdate.model (rule Q (firstPolicy Q h B))) s : ℚ) : ℝ) :=
  randomInitETLog_eq_rational_sum_of_equations Q h B _ (FinitePotential.potential_equations _
    (FinitePotential.det_ne_zero_of_accessible _ (model_stochastic Q h _) hr))

end FiniteResampling

#check @FiniteResampling.table_expectedHitCount_eq_of_equations
#check @FiniteResampling.initialStateFromLog_integral_eq_sum
#check @FiniteResampling.ETLog_eq_of_equations
#check @FiniteResampling.randomInitETLog_eq_of_equations
#check @FiniteResampling.randomInitETLog_eq_rational_sum_of_equations
#check @FiniteResampling.ETLog_eq_potential
#check @FiniteResampling.randomInitETLog_eq_potential_sum
