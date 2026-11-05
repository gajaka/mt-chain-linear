/-
  Additive drift applied to the existing counter-driven MT trajectory.

  The certificate concerns its actual product-log law, its existing
  pickFirstViolated policy, and its stopped count TLog. A state potential
  is stopped after the first good state. Its natural history filtration,
  adaptation and running-event measurability are proved here.

  Certificate fields are integrability and a one-step conditional expected
  decrease. No repair-existence, termination, finite-expected-work, LLL,
  Shearer or HLS premise is included. Checking the local decrease for a
  particular potential remains a model-specific obligation.
-/

module

public import PPGraph.Drift.Additive
public import PPGraph.Integration.MoserTardosRepair

@[expose] public section

set_option linter.unusedSectionVars false

open MeasureTheory Classical
open scoped ENNReal NNReal

namespace RepairDrift

variable {V : Type} [DecidableEq V] {S : VarSpaces V} {ι : Type}
    [Fintype ι] [DecidableEq ι] [Nonempty ι]

def mtRunningEvent (P : MTProcess S ι) (init : LogSpace S → MTState S)
    (n : ℕ) : Set (LogSpace S) := {ω | RunningUntil P (init ω) ω n}

/-- The filtration reveals states already visited, never future states. -/
noncomputable def mtHistory (P : MTProcess S ι) (hbad : ∀ i, MeasurableSet (P.bad i))
    (init : LogSpace S → MTState S) (hinit : Measurable init) :
    Filtration ℕ (inferInstance : MeasurableSpace (LogSpace S)) where
  seq n := ⨆ k ≤ n, MeasurableSpace.comap (fun ω => randTraj P (init ω) ω k) inferInstance
  mono' _ _ h := biSup_mono (fun _ => ge_trans h)
  le' n := by
    apply iSup₂_le
    intro k _
    exact (measurable_randStep_of_measurable_init P hbad init hinit k).1.comap_le

theorem measurable_randTraj_history (P : MTProcess S ι)
    (hbad : ∀ i, MeasurableSet (P.bad i))
    (init : LogSpace S → MTState S) (hinit : Measurable init)
    (k n : ℕ) (hkn : k ≤ n) :
    Measurable[mtHistory P hbad init hinit n] (fun ω => randTraj P (init ω) ω k) := by
  intro B hB
  have hle : MeasurableSpace.comap (fun ω => randTraj P (init ω) ω k) inferInstance ≤
      mtHistory P hbad init hinit n :=
    le_iSup_of_le k (le_iSup_of_le hkn le_rfl)
  exact hle _ ⟨B, hB, rfl⟩

theorem measurableSet_MTGood (P : MTProcess S ι)
    (hbad : ∀ i, MeasurableSet (P.bad i)) :
    MeasurableSet {s : MTState S | MTGood P s} := by
  have heq : {s : MTState S | MTGood P s} = ⋂ i, (P.bad i)ᶜ := by
    ext s
    simp only [Set.mem_ofPred_eq, Set.mem_iInter, Set.mem_compl_iff, MTGood]
  rw [heq]
  exact MeasurableSet.iInter (fun i => (hbad i).compl)

theorem runningUntil_iff_no_good_before (P : MTProcess S ι) (ω0 : MTState S)
    (ω : LogSpace S) (n : ℕ) :
    RunningUntil P ω0 ω n ↔ ∀ k < n, ¬ MTGood P (randTraj P ω0 ω k) := by
  apply forall_congr'
  intro k
  apply forall_congr'
  intro _
  constructor
  · intro h hg
    exact hg (realC P ω0 ω k) h
  · intro h
    by_contra hn
    exact h ((randStep_notMem_bad_realC_iff P ω0 ω k).mp hn)

theorem measurableSet_mtRunningEvent_history (P : MTProcess S ι)
    (hbad : ∀ i, MeasurableSet (P.bad i))
    (init : LogSpace S → MTState S) (hinit : Measurable init)
    (t n : ℕ) (ht : t ≤ n + 1) :
    MeasurableSet[mtHistory P hbad init hinit n] (mtRunningEvent P init t) := by
  have heq : mtRunningEvent P init t =
      ⋂ k ∈ Finset.range t,
        (fun ω => randTraj P (init ω) ω k) ⁻¹' {s : MTState S | MTGood P s}ᶜ := by
    ext ω
    simp only [mtRunningEvent, Set.mem_ofPred_eq, Set.mem_iInter, Finset.mem_range,
      Set.mem_preimage, Set.mem_compl_iff, runningUntil_iff_no_good_before]
  rw [heq]
  apply Finset.measurableSet_biInter
  intro k hk
  exact (measurable_randTraj_history P hbad init hinit k n (by
    have := Finset.mem_range.mp hk
    omega)) (measurableSet_MTGood P hbad).compl

/-- Zero after stopping; at an active state, evaluate the supplied state potential. -/
noncomputable def mtStoppedPotential (P : MTProcess S ι)
    (init : LogSpace S → MTState S) (potential : MTState S → ℝ≥0)
    (n : ℕ) : LogSpace S → ℝ :=
  (mtRunningEvent P init n).indicator (fun ω => (potential (randTraj P (init ω) ω n) : ℝ))

theorem mtStoppedPotential_nonneg (P : MTProcess S ι)
    (init : LogSpace S → MTState S) (potential : MTState S → ℝ≥0)
    (n : ℕ) (ω : LogSpace S) : 0 ≤ mtStoppedPotential P init potential n ω := by
  exact Set.indicator_nonneg (fun _ _ => NNReal.coe_nonneg _) _

theorem measurable_mtStoppedPotential_history (P : MTProcess S ι)
    (hbad : ∀ i, MeasurableSet (P.bad i))
    (init : LogSpace S → MTState S) (hinit : Measurable init)
    (potential : MTState S → ℝ≥0) (hpotential : Measurable potential) (n : ℕ) :
    Measurable[mtHistory P hbad init hinit n] (mtStoppedPotential P init potential n) := by
  exact (NNReal.continuous_coe.measurable.comp (hpotential.comp
    (measurable_randTraj_history P hbad init hinit n n le_rfl))).indicator
    (measurableSet_mtRunningEvent_history P hbad init hinit n n (by omega))

theorem mtStoppedPotential_le (P : MTProcess S ι)
    (init : LogSpace S → MTState S) (potential : MTState S → ℝ≥0)
    (M : ℝ≥0) (hM : ∀ s, potential s ≤ M) (n : ℕ) (ω : LogSpace S) :
    mtStoppedPotential P init potential n ω ≤ (M : ℝ) := by
  unfold mtStoppedPotential
  by_cases h : ω ∈ mtRunningEvent P init n
  · rw [Set.indicator_of_mem h]
    exact_mod_cast hM _
  · rw [Set.indicator_of_notMem h]
    exact M.coe_nonneg

/-- Bounded measurable state potentials are automatically integrable at every time. -/
theorem integrable_mtStoppedPotential_of_bounded (P : MTProcess S ι)
    (hbad : ∀ i, MeasurableSet (P.bad i))
    (init : LogSpace S → MTState S) (hinit : Measurable init)
    (potential : MTState S → ℝ≥0) (hpotential : Measurable potential)
    (M : ℝ≥0) (hM : ∀ s, potential s ≤ M) (n : ℕ) :
    Integrable (mtStoppedPotential P init potential n) (logMeasure S) := by
  have hm := (measurable_mtStoppedPotential_history P hbad init hinit
    potential hpotential n).mono ((mtHistory P hbad init hinit).le n) le_rfl
  apply (integrable_const (M : ℝ)).mono_nonneg hm.aestronglyMeasurable
    (Filter.Eventually.of_forall (mtStoppedPotential_nonneg P init potential n))
  exact Filter.Eventually.of_forall (mtStoppedPotential_le P init potential M hM n)

@[simp] theorem mtStoppedPotential_zero (P : MTProcess S ι)
    (init : LogSpace S → MTState S) (potential : MTState S → ℝ≥0)
    (ω : LogSpace S) :
    mtStoppedPotential P init potential 0 ω = (potential (init ω) : ℝ) := by
  simp [mtStoppedPotential, mtRunningEvent, RunningUntil, randTraj, randStep]

/-- A genuine state-potential certificate for the actual MT law. -/
structure MTCertificate (P : MTProcess S ι)
    (hbad : ∀ i, MeasurableSet (P.bad i))
    (init : LogSpace S → MTState S) (hinit : Measurable init)
    (potential : MTState S → ℝ≥0) (δ : ℝ≥0) : Prop where
  integrable : ∀ n, Integrable (mtStoppedPotential P init potential n) (logMeasure S)
  decrease : ∀ n, ∀ᵐ ω ∂logMeasure S,
    ((logMeasure S)[mtStoppedPotential P init potential (n + 1) |
      mtHistory P hbad init hinit n]) ω +
      (mtRunningEvent P init (n + 1)).indicator (fun _ => (δ : ℝ)) ω ≤
      mtStoppedPotential P init potential n ω

theorem mtCertificate_of_bounded (P : MTProcess S ι)
    (hbad : ∀ i, MeasurableSet (P.bad i))
    (init : LogSpace S → MTState S) (hinit : Measurable init)
    (potential : MTState S → ℝ≥0) (hpotential : Measurable potential)
    (M : ℝ≥0) (hM : ∀ s, potential s ≤ M) (δ : ℝ≥0)
    (hdecrease : ∀ n, ∀ᵐ ω ∂logMeasure S,
      ((logMeasure S)[mtStoppedPotential P init potential (n + 1) |
        mtHistory P hbad init hinit n]) ω +
        (mtRunningEvent P init (n + 1)).indicator (fun _ => (δ : ℝ)) ω ≤
        mtStoppedPotential P init potential n ω) :
    MTCertificate P hbad init hinit potential δ := by
  exact ⟨integrable_mtStoppedPotential_of_bounded P hbad init hinit
    potential hpotential M hM, hdecrease⟩

noncomputable def MTCertificate.toConditional (P : MTProcess S ι)
    (hbad : ∀ i, MeasurableSet (P.bad i))
    (init : LogSpace S → MTState S) (hinit : Measurable init)
    (potential : MTState S → ℝ≥0) (hpotential : Measurable potential) (δ : ℝ≥0)
    (C : MTCertificate P hbad init hinit potential δ) :
    ConditionalCertificate (logMeasure S) (fun n => mtRunningEvent P init (n + 1))
      (mtHistory P hbad init hinit) δ where
  value := mtStoppedPotential P init potential
  integrable := C.integrable
  nonnegative := fun n => Filter.Eventually.of_forall (mtStoppedPotential_nonneg P init potential n)
  adapted := fun n => (measurable_mtStoppedPotential_history P hbad init hinit
    potential hpotential n).stronglyMeasurable
  active_measurable := fun n => measurableSet_mtRunningEvent_history P hbad init hinit
    (n + 1) n le_rfl
  decrease := C.decrease

theorem activeCount_mt_eq_TLog (P : MTProcess S ι)
    (init : LogSpace S → MTState S) (ω : LogSpace S) :
    activeCount (fun n => mtRunningEvent P init (n + 1)) ω = TLog P (init ω) ω := by
  unfold activeCount TLog
  apply tsum_congr
  intro n
  simp only [mtRunningEvent, Set.indicator_apply, Set.mem_ofPred_eq]

theorem expectedActiveCount_fixed_eq (P : MTProcess S ι) (ω0 : MTState S) :
    expectedActiveCount (logMeasure S) (fun n => mtRunningEvent P (fun _ => ω0) (n + 1)) =
      ETLog P ω0 := by
  unfold expectedActiveCount ETLog
  exact lintegral_congr (activeCount_mt_eq_TLog P (fun _ => ω0))

theorem expectedActiveCount_randomInit_eq (P : MTProcess S ι) :
    expectedActiveCount (logMeasure S) (fun n => mtRunningEvent P initialStateFromLog (n + 1)) =
      randomInitETLog P := by
  unfold expectedActiveCount randomInitETLog randomInitTLog
  exact lintegral_congr (activeCount_mt_eq_TLog P initialStateFromLog)

theorem ETLog_le_of_drift (P : MTProcess S ι) (hbad : ∀ i, MeasurableSet (P.bad i))
    (ω0 : MTState S) (potential : MTState S → ℝ≥0) (hpotential : Measurable potential)
    (δ : ℝ≥0) (hδ : 0 < δ)
    (C : MTCertificate P hbad (fun _ => ω0) measurable_const potential δ) :
    ETLog P ω0 ≤ (potential ω0 : ℝ≥0∞) / (δ : ℝ≥0∞) := by
  have h := (C.toConditional P hbad (fun _ => ω0) measurable_const
    potential hpotential δ).expectedActiveCount_le hδ
  rw [expectedActiveCount_fixed_eq] at h
  simpa [MTCertificate.toConditional] using h

theorem ETLog_lt_top_of_drift (P : MTProcess S ι) (hbad : ∀ i, MeasurableSet (P.bad i))
    (ω0 : MTState S) (potential : MTState S → ℝ≥0) (hpotential : Measurable potential)
    (δ : ℝ≥0) (hδ : 0 < δ)
    (C : MTCertificate P hbad (fun _ => ω0) measurable_const potential δ) :
    ETLog P ω0 < ⊤ := by
  rw [← expectedActiveCount_fixed_eq]
  exact (C.toConditional P hbad (fun _ => ω0) measurable_const
    potential hpotential δ).expectedActiveCount_lt_top hδ

theorem ae_exists_good_of_drift (P : MTProcess S ι) (hbad : ∀ i, MeasurableSet (P.bad i))
    (ω0 : MTState S) (potential : MTState S → ℝ≥0) (hpotential : Measurable potential)
    (δ : ℝ≥0) (hδ : 0 < δ)
    (C : MTCertificate P hbad (fun _ => ω0) measurable_const potential δ) :
    ∀ᵐ ω ∂logMeasure S, ∃ T, MTGood P (randTraj P ω0 ω T) := by
  have hfinite : ∀ᵐ ω ∂logMeasure S, TLog P ω0 ω < ⊤ :=
    MeasureTheory.ae_lt_top (measurable_TLog P hbad ω0)
      (ETLog_lt_top_of_drift P hbad ω0 potential hpotential δ hδ C).ne
  filter_upwards [hfinite] with ω hω
  exact (TLog_lt_top_iff_exists_good P ω0 ω).mp hω

theorem randomInitETLog_le_of_drift (P : MTProcess S ι)
    (hbad : ∀ i, MeasurableSet (P.bad i))
    (potential : MTState S → ℝ≥0) (hpotential : Measurable potential)
    (δ : ℝ≥0) (hδ : 0 < δ)
    (C : MTCertificate P hbad initialStateFromLog measurable_initialStateFromLog potential δ) :
    randomInitETLog P ≤
      ENNReal.ofReal (∫ ω : LogSpace S, (potential (initialStateFromLog ω) : ℝ) ∂logMeasure S) /
        (δ : ℝ≥0∞) := by
  have h := (C.toConditional P hbad initialStateFromLog measurable_initialStateFromLog
    potential hpotential δ).expectedActiveCount_le hδ
  rw [expectedActiveCount_randomInit_eq] at h
  simpa only [MTCertificate.toConditional, mtStoppedPotential_zero] using h

theorem randomInitETLog_lt_top_of_drift (P : MTProcess S ι)
    (hbad : ∀ i, MeasurableSet (P.bad i))
    (potential : MTState S → ℝ≥0) (hpotential : Measurable potential)
    (δ : ℝ≥0) (hδ : 0 < δ)
    (C : MTCertificate P hbad initialStateFromLog measurable_initialStateFromLog potential δ) :
    randomInitETLog P < ⊤ := by
  rw [← expectedActiveCount_randomInit_eq]
  exact (C.toConditional P hbad initialStateFromLog measurable_initialStateFromLog
    potential hpotential δ).expectedActiveCount_lt_top hδ

theorem ae_randomInit_exists_good_of_drift (P : MTProcess S ι)
    (hbad : ∀ i, MeasurableSet (P.bad i))
    (potential : MTState S → ℝ≥0) (hpotential : Measurable potential)
    (δ : ℝ≥0) (hδ : 0 < δ)
    (C : MTCertificate P hbad initialStateFromLog measurable_initialStateFromLog potential δ) :
    ∀ᵐ ω ∂logMeasure S,
      ∃ T, MTGood P (randTraj P (initialStateFromLog ω) ω T) := by
  exact ae_randomInit_exists_good P hbad
    (randomInitETLog_lt_top_of_drift P hbad potential hpotential δ hδ C)

theorem mtRepairGraph_globally_repairable_of_drift [Fintype V]
    (P : MTProcess S ι) (edges : MTState S → MTState S → Prop)
    (hbad : ∀ i, MeasurableSet (P.bad i))
    (potential : MTState S → ℝ≥0) (hpotential : Measurable potential)
    (δ : ℝ≥0) (hδ : 0 < δ)
    (C : MTCertificate P hbad initialStateFromLog measurable_initialStateFromLog potential δ) :
    globally_repairable (mtRepairGraph P edges) := by
  exact mtRepairGraph_globally_repairable_of_randomInitETLog_lt_top P edges hbad
    (randomInitETLog_lt_top_of_drift P hbad potential hpotential δ hδ C)

end RepairDrift

#check @RepairDrift.measurable_randTraj_history
#check @RepairDrift.measurableSet_MTGood
#check @RepairDrift.runningUntil_iff_no_good_before
#check @RepairDrift.measurableSet_mtRunningEvent_history
#check @RepairDrift.mtStoppedPotential_nonneg
#check @RepairDrift.measurable_mtStoppedPotential_history
#check @RepairDrift.mtStoppedPotential_le
#check @RepairDrift.integrable_mtStoppedPotential_of_bounded
#check @RepairDrift.mtStoppedPotential_zero
#check @RepairDrift.mtCertificate_of_bounded
#check @RepairDrift.activeCount_mt_eq_TLog
#check @RepairDrift.expectedActiveCount_fixed_eq
#check @RepairDrift.expectedActiveCount_randomInit_eq
#check @RepairDrift.ETLog_le_of_drift
#check @RepairDrift.ETLog_lt_top_of_drift
#check @RepairDrift.ae_exists_good_of_drift
#check @RepairDrift.randomInitETLog_le_of_drift
#check @RepairDrift.randomInitETLog_lt_top_of_drift
#check @RepairDrift.ae_randomInit_exists_good_of_drift
#check @RepairDrift.mtRepairGraph_globally_repairable_of_drift
