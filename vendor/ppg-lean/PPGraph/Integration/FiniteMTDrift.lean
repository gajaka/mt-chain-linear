/-
  An accepted rational drift check bounds the EXISTING MT TLog.

  The conditional transition law of per-variable-counter execution is
  proved from its independent table measure. Initialization may be fixed
  or read slot zero. The stopped execution agrees with the old randTraj
  through the first good state, and its hit count equals the old TLog
  pointwise. No transition-law or convergence premise remains to supply.

  Finite domains, rational marginals and deterministic memoryless selection
  are required. Partial footprints are allowed. No LLL/Shearer/HLS criterion
  is used. This establishes a model theorem, not a physical-controller law.
-/

module

public import PPGraph.Finite.Resampling.TableLaw
public import PPGraph.MoserTardos.Bounds.Drift

@[expose] public section

set_option linter.unusedSectionVars false
set_option backward.isDefEq.respectTransparency false

open MeasureTheory Classical
open scoped ENNReal NNReal

namespace FiniteResampling

variable {V : Type} [Fintype V] [DecidableEq V]
  {D : V → Type} [∀ v, Fintype (D v)] [∀ v, DecidableEq (D v)]
  [∀ v, MeasurableSpace (D v)] [∀ v, MeasurableSingletonClass (D v)]

noncomputable instance tableDomainFintype (Q : Marginals D) (h : Valid Q) :
    ∀ v, Fintype ((varSpaces Q h).space v) :=
  fun v => inferInstanceAs (Fintype (D v))

noncomputable instance tableDomainDecidableEq (Q : Marginals D) (h : Valid Q) :
    ∀ v, DecidableEq ((varSpaces Q h).space v) :=
  fun v => inferInstanceAs (DecidableEq (D v))

instance tableDomainMeasurableSingleton (Q : Marginals D) (h : Valid Q) :
    ∀ v, MeasurableSingletonClass ((varSpaces Q h).space v) :=
  fun v => inferInstanceAs (MeasurableSingletonClass (D v))

theorem tableExecution (Q : Marginals D) (h : Valid Q) (P : Policy D)
    (init : LogSpace (varSpaces Q h) → State D) (hi : Measurable init)
    (hl : FiniteTable.InitialLocal init) :
    FiniteUpdate.Execution (rule Q P) (logMeasure (varSpaces Q h))
      (FiniteTable.history (activeFootprint P) init hi)
      (FiniteTable.trajectory (activeFootprint P) init)
      (FiniteTable.nextDraw (activeFootprint P) init) where
  adapted := FiniteTable.trajectory_adapted _ init hi
  draw_measurable := FiniteTable.measurable_nextDraw _ init hi
  step := FiniteTable.trajectory_step _ init
  fresh n a := by
    have hf := FiniteTable.nextDraw_fresh (activeFootprint P) init hi hl n a
    have hm : (FiniteTable.productLaw (varSpaces Q h) {a}).toReal =
        (productMass Q a : ℝ) := by
      change (Measure.pi (fun v => (marginalPMF Q h v).toMeasure) {a}).toReal = _
      rw [← inputMeasure_eq_product Q h P,
        PMF.toMeasure_apply_singleton _ a (measurableSet_singleton a)]
      exact FiniteUpdate.inputPMF_toReal (rule Q P) (rule_valid Q h P) a
    simpa only [hm, rule] using hf

theorem tableRealization (Q : Marginals D) (h : Valid Q) (P : Policy D)
    (init : LogSpace (varSpaces Q h) → State D) (hi : Measurable init)
    (hl : FiniteTable.InitialLocal init) :
    FiniteDrift.Realization (FiniteUpdate.model (rule Q P)) (logMeasure (varSpaces Q h))
      (FiniteTable.history (activeFootprint P) init hi)
      (FiniteTable.trajectory (activeFootprint P) init) :=
  FiniteUpdate.toRealization _ _ _ _ _ (tableExecution Q h P init hi hl)

theorem table_expectedHitCount_le (Q : Marginals D) (h : Valid Q) (P : Policy D)
    (W : FiniteDrift.Witness (State D)) (hc : FiniteUpdate.check (rule Q P) W = true)
    (init : LogSpace (varSpaces Q h) → State D) (hi : Measurable init)
    (hl : FiniteTable.InitialLocal init) :
    FiniteDrift.expectedHitCount (FiniteUpdate.model (rule Q P)) (logMeasure (varSpaces Q h))
      (FiniteTable.trajectory (activeFootprint P) init) ≤
      ENNReal.ofReal (∫ ω, (W.potential (init ω) : ℝ) ∂logMeasure (varSpaces Q h)) /
        ENNReal.ofReal (W.delta : ℝ) :=
  FiniteUpdate.execution_expectedHitCount_le _ W hc _ _ _ _ (tableExecution Q h P init hi hl)

theorem table_expectedHitCount_lt_top (Q : Marginals D) (h : Valid Q) (P : Policy D)
    (W : FiniteDrift.Witness (State D)) (hc : FiniteUpdate.check (rule Q P) W = true)
    (init : LogSpace (varSpaces Q h) → State D) (hi : Measurable init)
    (hl : FiniteTable.InitialLocal init) :
    FiniteDrift.expectedHitCount (FiniteUpdate.model (rule Q P)) (logMeasure (varSpaces Q h))
      (FiniteTable.trajectory (activeFootprint P) init) < ⊤ :=
  FiniteDrift.expectedHitCount_lt_top _ W hc _ _ _ (tableRealization Q h P init hi hl)

theorem table_ae_exists_good (Q : Marginals D) (h : Valid Q) (P : Policy D)
    (W : FiniteDrift.Witness (State D)) (hc : FiniteUpdate.check (rule Q P) W = true)
    (init : LogSpace (varSpaces Q h) → State D) (hi : Measurable init)
    (hl : FiniteTable.InitialLocal init) :
    ∀ᵐ ω ∂logMeasure (varSpaces Q h),
      ∃ T, P.good (FiniteTable.trajectory (activeFootprint P) init T ω) = true :=
  FiniteDrift.ae_exists_good _ W hc _ _ _ (tableRealization Q h P init hi hl)

variable {I : Type} [Fintype I] [DecidableEq I] [Nonempty I]

noncomputable def firstPolicy (Q : Marginals D) (h : Valid Q) (B : Problem D I) : Policy D :=
  selectedPolicy B (pickFirstViolated (mtProcess Q h B))

theorem firstPolicy_good_iff (Q : Marginals D) (h : Valid Q) (B : Problem D I)
    (s : State D) : (firstPolicy Q h B).good s = true ↔ MTGood (mtProcess Q h B) s := by
  rw [show (firstPolicy Q h B).good s = allGood B s from rfl, allGood_eq_true_iff]
  exact forall_congr' (fun i => Bool.eq_false_iff)

theorem raw_run_eq_randStep (Q : Marginals D) (h : Valid Q) (B : Problem D I)
    (init : LogSpace (varSpaces Q h) → State D) (ω : LogSpace (varSpaces Q h)) (n : ℕ) :
    FiniteTable.run (firstPolicy Q h B).footprint init ω n =
      randStep (mtProcess Q h B) (init ω) ω n := by
  induction n with
  | zero => rfl
  | succ n ih =>
    simp only [FiniteTable.run, randStep, ih]
    rfl

theorem stopped_run_eq_before_good (Q : Marginals D) (h : Valid Q) (B : Problem D I)
    (init : LogSpace (varSpaces Q h) → State D) (ω : LogSpace (varSpaces Q h)) (n : ℕ)
    (hb : ∀ k < n, ¬ MTGood (mtProcess Q h B)
      (randTraj (mtProcess Q h B) (init ω) ω k)) :
    FiniteTable.run (activeFootprint (firstPolicy Q h B)) init ω n =
      randStep (mtProcess Q h B) (init ω) ω n := by
  rw [← raw_run_eq_randStep Q h B init ω n]
  symm
  apply FiniteTable.run_eq_of_footprints_agree
  intro k hk
  have hn : (firstPolicy Q h B).good
      (FiniteTable.trajectory (firstPolicy Q h B).footprint init k ω) = false := by
    apply Bool.eq_false_iff.mpr
    intro hg
    apply hb k hk
    apply (firstPolicy_good_iff Q h B _).mp
    simpa only [FiniteTable.trajectory, raw_run_eq_randStep, randTraj] using hg
  simp only [activeFootprint, hn, Bool.false_eq_true, ↓reduceIte]

theorem raw_run_eq_before_stopped_good (Q : Marginals D) (h : Valid Q) (B : Problem D I)
    (init : LogSpace (varSpaces Q h) → State D) (ω : LogSpace (varSpaces Q h)) (n : ℕ)
    (hb : ∀ k < n, (firstPolicy Q h B).good
      (FiniteTable.trajectory (activeFootprint (firstPolicy Q h B)) init k ω) = false) :
    FiniteTable.run (activeFootprint (firstPolicy Q h B)) init ω n =
      randStep (mtProcess Q h B) (init ω) ω n := by
  rw [← raw_run_eq_randStep Q h B init ω n]
  apply FiniteTable.run_eq_of_footprints_agree
  intro k hk
  simp only [activeFootprint, hb k hk, Bool.false_eq_true, ↓reduceIte]

theorem stopped_before_iff_runningUntil (Q : Marginals D) (h : Valid Q) (B : Problem D I)
    (init : LogSpace (varSpaces Q h) → State D) (ω : LogSpace (varSpaces Q h)) (n : ℕ) :
    (∀ k < n, (firstPolicy Q h B).good
      (FiniteTable.trajectory (activeFootprint (firstPolicy Q h B)) init k ω) = false) ↔
      RunningUntil (mtProcess Q h B) (init ω) ω n := by
  rw [RepairDrift.runningUntil_iff_no_good_before]
  constructor
  · intro hs k hk
    have he := raw_run_eq_before_stopped_good Q h B init ω k
      (fun j hj => hs j (by omega))
    intro hg
    have hb := hs k hk
    have hsg := (firstPolicy_good_iff Q h B _).mpr hg
    change (firstPolicy Q h B).good (randStep (mtProcess Q h B) (init ω) ω k).1 = true at hsg
    rw [← he] at hsg
    exact Bool.false_ne_true (hb.symm.trans hsg)
  · intro hs k hk
    have he := stopped_run_eq_before_good Q h B init ω k
      (fun j hj => hs j (by omega))
    apply Bool.eq_false_iff.mpr
    intro hg
    apply hs k hk
    apply (firstPolicy_good_iff Q h B _).mp
    change (firstPolicy Q h B).good (randStep (mtProcess Q h B) (init ω) ω k).1 = true
    rw [← he]
    exact hg

/-- Equality is pointwise on the same table, stronger than an expectation comparison. -/
theorem table_hitCount_eq_TLog (Q : Marginals D) (h : Valid Q) (B : Problem D I)
    (init : LogSpace (varSpaces Q h) → State D) (ω : LogSpace (varSpaces Q h)) :
    FiniteDrift.hitCount (FiniteUpdate.model (rule Q (firstPolicy Q h B)))
      (FiniteTable.trajectory (activeFootprint (firstPolicy Q h B)) init) ω =
      TLog (mtProcess Q h B) (init ω) ω := by
  unfold FiniteDrift.hitCount RepairDrift.activeCount TLog
  apply tsum_congr
  intro n
  have he := stopped_before_iff_runningUntil Q h B init ω (n + 1)
  simp only [Nat.lt_succ_iff] at he
  simp only [Set.indicator_apply, FiniteDrift.runningEvent, Set.mem_ofPred_eq]
  change (if ∀ k ≤ n, (firstPolicy Q h B).good
      (FiniteTable.trajectory (activeFootprint (firstPolicy Q h B)) init k ω) = false
      then (1 : ℝ≥0∞) else 0) = _
  simp only [he]

theorem checked_ETLog_le (Q : Marginals D) (h : Valid Q) (B : Problem D I)
    (W : FiniteDrift.Witness (State D))
    (hc : check Q (firstPolicy Q h B) W = true) (s₀ : State D) :
    ETLog (mtProcess Q h B) s₀ ≤
      ENNReal.ofReal (W.potential s₀ : ℝ) / ENNReal.ofReal (W.delta : ℝ) := by
  have hb := table_expectedHitCount_le Q h (firstPolicy Q h B) W (check_sound _ _ _ hc).2
    (fun _ => s₀) measurable_const (FiniteTable.initialLocal_const (S := varSpaces Q h) s₀)
  have he : FiniteDrift.expectedHitCount (FiniteUpdate.model (rule Q (firstPolicy Q h B)))
      (logMeasure (varSpaces Q h))
      (FiniteTable.trajectory (activeFootprint (firstPolicy Q h B)) (fun _ => s₀)) =
      ETLog (mtProcess Q h B) s₀ := by
    exact lintegral_congr (table_hitCount_eq_TLog Q h B (fun _ => s₀))
  rw [he] at hb
  simpa using hb

theorem checked_ETLog_lt_top (Q : Marginals D) (h : Valid Q) (B : Problem D I)
    (W : FiniteDrift.Witness (State D))
    (hc : check Q (firstPolicy Q h B) W = true) (s₀ : State D) :
    ETLog (mtProcess Q h B) s₀ < ⊤ := by
  have hb := table_expectedHitCount_lt_top Q h (firstPolicy Q h B) W (check_sound _ _ _ hc).2
    (fun _ => s₀) measurable_const (FiniteTable.initialLocal_const (S := varSpaces Q h) s₀)
  change (∫⁻ ω, _ ∂logMeasure (varSpaces Q h)) < ⊤ at hb
  simpa only [table_hitCount_eq_TLog, ETLog] using hb

theorem checked_randTraj_ae_exists_good (Q : Marginals D) (h : Valid Q) (B : Problem D I)
    (W : FiniteDrift.Witness (State D))
    (hc : check Q (firstPolicy Q h B) W = true) (s₀ : State D) :
    ∀ᵐ ω ∂logMeasure (varSpaces Q h),
      ∃ T, MTGood (mtProcess Q h B) (randTraj (mtProcess Q h B) s₀ ω T) := by
  have hb := table_ae_exists_good Q h (firstPolicy Q h B) W (check_sound _ _ _ hc).2
    (fun _ => s₀) measurable_const (FiniteTable.initialLocal_const (S := varSpaces Q h) s₀)
  filter_upwards [hb] with ω hgood
  by_contra hn
  push Not at hn
  obtain ⟨T, hT⟩ := hgood
  have he := stopped_run_eq_before_good Q h B (fun _ => s₀) ω T (fun k _ => hn k)
  have hlegacy : MTGood (mtProcess Q h B) (randTraj (mtProcess Q h B) s₀ ω T) := by
    apply (firstPolicy_good_iff Q h B _).mp
    change (firstPolicy Q h B).good (randStep (mtProcess Q h B) s₀ ω T).1 = true
    rw [← he]
    exact hT
  exact hn T hlegacy

theorem initialStateFromLog_local (Q : Marginals D) (h : Valid Q) :
    FiniteTable.InitialLocal (initialStateFromLog (S := varSpaces Q h)) := by
  intro ω₁ ω₂ ha
  funext v
  exact ha v

theorem checked_randomInitETLog_le (Q : Marginals D) (h : Valid Q) (B : Problem D I)
    (W : FiniteDrift.Witness (State D))
    (hc : check Q (firstPolicy Q h B) W = true) :
    randomInitETLog (mtProcess Q h B) ≤
      ENNReal.ofReal (∫ ω, (W.potential (initialStateFromLog ω) : ℝ)
        ∂logMeasure (varSpaces Q h)) / ENNReal.ofReal (W.delta : ℝ) := by
  have hb := table_expectedHitCount_le Q h (firstPolicy Q h B) W (check_sound _ _ _ hc).2
    initialStateFromLog measurable_initialStateFromLog (initialStateFromLog_local Q h)
  change (∫⁻ ω, _ ∂logMeasure (varSpaces Q h)) ≤ _ at hb
  simpa only [table_hitCount_eq_TLog, randomInitETLog, randomInitTLog] using hb

theorem checked_randomInitETLog_lt_top (Q : Marginals D) (h : Valid Q) (B : Problem D I)
    (W : FiniteDrift.Witness (State D))
    (hc : check Q (firstPolicy Q h B) W = true) :
    randomInitETLog (mtProcess Q h B) < ⊤ := by
  have hb := table_expectedHitCount_lt_top Q h (firstPolicy Q h B) W (check_sound _ _ _ hc).2
    initialStateFromLog measurable_initialStateFromLog (initialStateFromLog_local Q h)
  change (∫⁻ ω, _ ∂logMeasure (varSpaces Q h)) < ⊤ at hb
  simpa only [table_hitCount_eq_TLog, randomInitETLog, randomInitTLog] using hb

theorem checked_randomInit_randTraj_ae_exists_good (Q : Marginals D) (h : Valid Q)
    (B : Problem D I) (W : FiniteDrift.Witness (State D))
    (hc : check Q (firstPolicy Q h B) W = true) :
    ∀ᵐ ω ∂logMeasure (varSpaces Q h), ∃ T, MTGood (mtProcess Q h B)
      (randTraj (mtProcess Q h B) (initialStateFromLog ω) ω T) := by
  have hb := table_ae_exists_good Q h (firstPolicy Q h B) W (check_sound _ _ _ hc).2
    initialStateFromLog measurable_initialStateFromLog (initialStateFromLog_local Q h)
  filter_upwards [hb] with ω hgood
  by_contra hn
  push Not at hn
  obtain ⟨T, hT⟩ := hgood
  have he := stopped_run_eq_before_good Q h B initialStateFromLog ω T (fun k _ => hn k)
  have hlegacy : MTGood (mtProcess Q h B)
      (randTraj (mtProcess Q h B) (initialStateFromLog ω) ω T) := by
    apply (firstPolicy_good_iff Q h B _).mp
    change (firstPolicy Q h B).good
      (randStep (mtProcess Q h B) (initialStateFromLog ω) ω T).1 = true
    rw [← he]
    exact hT
  exact hn T hlegacy

end FiniteResampling

#check @FiniteResampling.tableExecution
#check @FiniteResampling.tableRealization
#check @FiniteResampling.table_expectedHitCount_le
#check @FiniteResampling.table_expectedHitCount_lt_top
#check @FiniteResampling.table_ae_exists_good
#check @FiniteResampling.firstPolicy_good_iff
#check @FiniteResampling.raw_run_eq_randStep
#check @FiniteResampling.stopped_run_eq_before_good
#check @FiniteResampling.raw_run_eq_before_stopped_good
#check @FiniteResampling.stopped_before_iff_runningUntil
#check @FiniteResampling.table_hitCount_eq_TLog
#check @FiniteResampling.checked_ETLog_le
#check @FiniteResampling.checked_ETLog_lt_top
#check @FiniteResampling.checked_randTraj_ae_exists_good
#check @FiniteResampling.initialStateFromLog_local
#check @FiniteResampling.checked_randomInitETLog_le
#check @FiniteResampling.checked_randomInitETLog_lt_top
#check @FiniteResampling.checked_randomInit_randTraj_ae_exists_good
