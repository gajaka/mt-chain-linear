/-
  A process-based MT convergence criterion for full-footprint resampling.

  When every event reads/resamples all variables, the existing local-counter
  trajectory reads a new independent row of its table at each step. The
  probability of a good state, rather than a graph-based LLL criterion,
  controls its geometric running tail and its expected work.

  This is the standard geometric waiting-time argument (Mitzenmacher--Upfal,
  Probability and Computing, geometric distribution), applied to the actual
  MT policy and table, not to an alternative algorithm.

  A measurable product box contained in the good states gives a sufficient
  positive-probability certificate without exhaustive state enumeration.
  No numerical example or additional axiom is introduced.
-/

module

public import PPGraph.MoserTardos.Bounds.Drift
public import PPGraph.MoserTardos.Probability.Probability
public import Mathlib.Analysis.SpecificLimits.Basic

@[expose] public section

set_option linter.unusedSectionVars false

open MeasureTheory Classical
open scoped ENNReal NNReal

namespace RepairDrift

variable {V : Type} [Fintype V] [DecidableEq V] {S : VarSpaces V} {ι : Type}
    [Fintype ι] [DecidableEq ι] [Nonempty ι]

def mtGoodSet (P : MTProcess S ι) : Set (∀ v, S.space v) := {s | MTGood P s}

noncomputable def mtBadProbability (P : MTProcess S ι) : ℝ≥0∞ :=
  Measure.pi (fun v => S.measure v) (mtGoodSet P)ᶜ

noncomputable def mtGoodProbability (P : MTProcess S ι) : ℝ≥0∞ :=
  Measure.pi (fun v => S.measure v) (mtGoodSet P)

theorem mtGoodProbability_add_bad (P : MTProcess S ι)
    (hbad : ∀ i, MeasurableSet (P.bad i)) :
    mtGoodProbability P + mtBadProbability P = 1 := by
  have : ∀ v, IsProbabilityMeasure (S.measure v) := S.isProb
  have hg : MeasurableSet (mtGoodSet P) := measurableSet_MTGood P hbad
  simpa only [mtGoodProbability, mtBadProbability, measure_univ] using
    (measure_add_measure_compl (μ := Measure.pi (fun v => S.measure v))
      hg)

theorem one_sub_mtBadProbability (P : MTProcess S ι)
    (hbad : ∀ i, MeasurableSet (P.bad i)) :
    1 - mtBadProbability P = mtGoodProbability P := by
  have : ∀ v, IsProbabilityMeasure (S.measure v) := S.isProb
  have hg : MeasurableSet (mtGoodSet P) := measurableSet_MTGood P hbad
  symm
  simpa only [mtGoodProbability, mtBadProbability, compl_compl, measure_univ]
    using (measure_compl (μ := Measure.pi (fun v => S.measure v))
      hg.compl (measure_ne_top _ _))

theorem fullResampling_count (P : MTProcess S ι)
    (hfull : ∀ i, P.footprint i = Finset.univ)
    (ω0 : MTState S) (ω : LogSpace S) (n : ℕ) (v : V) :
    (randStep P ω0 ω n).2 v = n := by
  induction n with
  | zero => rfl
  | succ n ih =>
    change (if v ∈ P.footprint (pickFirstViolated P (randStep P ω0 ω n).1)
      then (randStep P ω0 ω n).2 v + 1 else (randStep P ω0 ω n).2 v) = n + 1
    simp only [hfull, Finset.mem_univ, ite_true, ih]

theorem fullResampling_randTraj_randomInit (P : MTProcess S ι)
    (hfull : ∀ i, P.footprint i = Finset.univ)
    (ω : LogSpace S) (n : ℕ) :
    randTraj P (initialStateFromLog ω) ω n = freshState ω n := by
  cases n with
  | zero => rfl
  | succ n =>
    funext v
    change resample (P.footprint (pickFirstViolated P
      (randStep P (initialStateFromLog ω) ω n).1))
      (randStep P (initialStateFromLog ω) ω n).1
      (drawFrom ω (fun w => (randStep P (initialStateFromLog ω) ω n).2 w + 1)) v = _
    simp only [hfull, resample, Finset.mem_univ, ite_true, drawFrom, atIdx]
    rw [fullResampling_count P hfull (initialStateFromLog ω) ω n v]
    rfl

def mtBadSlotEvent (P : MTProcess S ι) (n : ℕ) : Set (LogSpace S) :=
  (fun ω : LogSpace S => freshState ω n) ⁻¹' (mtGoodSet P)ᶜ

def mtSlotBlock (n : ℕ) : Finset (ℕ × V) := Finset.univ.image (fun v : V => (n, v))

theorem measurableSet_mtBadSlotEvent (P : MTProcess S ι)
    (hbad : ∀ i, MeasurableSet (P.bad i)) (n : ℕ) :
    MeasurableSet (mtBadSlotEvent P n) :=
  (measurable_freshState n) (measurableSet_MTGood P hbad).compl

theorem mtBadSlotEvent_dependsOn (P : MTProcess S ι) (n : ℕ)
    (ω₁ ω₂ : LogSpace S)
    (hagree : ∀ p ∈ mtSlotBlock (V := V) n, ω₁ p = ω₂ p) :
    ω₁ ∈ mtBadSlotEvent P n ↔ ω₂ ∈ mtBadSlotEvent P n := by
  have heq : freshState ω₁ n = freshState ω₂ n := by
    funext v
    exact hagree (n, v) (Finset.mem_image_of_mem _ (Finset.mem_univ v))
  change freshState ω₁ n ∈ (mtGoodSet P)ᶜ ↔ freshState ω₂ n ∈ (mtGoodSet P)ᶜ
  rw [heq]

theorem mtSlotBlock_disjoint {n k : ℕ} (hne : n ≠ k) :
    Disjoint (mtSlotBlock (V := V) n) (mtSlotBlock (V := V) k) := by
  apply Finset.disjoint_left.mpr
  intro p hn hk
  obtain ⟨v, _, hv⟩ := Finset.mem_image.mp hn
  obtain ⟨w, _, hw⟩ := Finset.mem_image.mp hk
  exact hne (congrArg Prod.fst (hv.trans hw.symm))

theorem logMeasure_mtBadSlotEvent (P : MTProcess S ι)
    (hbad : ∀ i, MeasurableSet (P.bad i)) (n : ℕ) :
    logMeasure S (mtBadSlotEvent P n) = mtBadProbability P := by
  have hm := measurable_readAt (S := S) (fun _ => n)
  have hset : MeasurableSet (mtGoodSet P)ᶜ := (measurableSet_MTGood P hbad).compl
  calc
    logMeasure S (mtBadSlotEvent P n) =
        (logMeasure S).map (readAt (fun _ => n)) (mtGoodSet P)ᶜ := by
      rw [Measure.map_apply hm hset]
      rfl
    _ = mtBadProbability P := by rw [logMeasure_map_readAt_eq_pi]; rfl

theorem fullResampling_runningEvent_eq (P : MTProcess S ι)
    (hfull : ∀ i, P.footprint i = Finset.univ) (N : ℕ) :
    randomInitRunningEvent P N = ⋂ n ∈ Finset.range N, mtBadSlotEvent P n := by
  ext ω
  simp only [randomInitRunningEvent, Set.mem_ofPred_eq, runningUntil_iff_no_good_before,
    Set.mem_iInter, Finset.mem_range, mtBadSlotEvent, Set.mem_preimage,
    mtGoodSet, fullResampling_randTraj_randomInit P hfull]
  rfl

/-- Exact survival probability for the actual stopped log. -/
theorem fullResampling_running_probability (P : MTProcess S ι)
    (hbad : ∀ i, MeasurableSet (P.bad i))
    (hfull : ∀ i, P.footprint i = Finset.univ) (N : ℕ) :
    logMeasure S (randomInitRunningEvent P N) = (mtBadProbability P) ^ N := by
  rw [fullResampling_runningEvent_eq P hfull N]
  have hprod := infinitePi_iInter_eq_prod_of_dependsOn (μCoin S) (Finset.range N)
    (mtSlotBlock (V := V)) (mtBadSlotEvent P)
    (fun _ _ _ _ hne => mtSlotBlock_disjoint hne)
    (fun n _ => mtBadSlotEvent_dependsOn P n)
    (fun n _ => measurableSet_mtBadSlotEvent P hbad n)
  change logMeasure S (⋂ n ∈ Finset.range N, mtBadSlotEvent P n) = _ at hprod
  rw [hprod]
  change (∏ n ∈ Finset.range N, logMeasure S (mtBadSlotEvent P n)) = _
  simp only [logMeasure_mtBadSlotEvent P hbad, Finset.prod_const, Finset.card_range]

/-- The expectation is the geometric tail sum, even if it is infinite. -/
theorem fullResampling_expected_work_eq (P : MTProcess S ι)
    (hbad : ∀ i, MeasurableSet (P.bad i))
    (hfull : ∀ i, P.footprint i = Finset.univ) :
    randomInitETLog P = mtBadProbability P * (1 - mtBadProbability P)⁻¹ := by
  rw [randomInitETLog_eq_tsum P hbad]
  simp_rw [fullResampling_running_probability P hbad hfull]
  exact ENNReal.tsum_geometric_add_one _

/-- Positive good-state mass gives finite expected work without any LLL test. -/
theorem fullResampling_expected_work_lt_top (P : MTProcess S ι)
    (hbad : ∀ i, MeasurableSet (P.bad i))
    (hfull : ∀ i, P.footprint i = Finset.univ)
    (hgood : 0 < mtGoodProbability P) : randomInitETLog P < ⊤ := by
  have : ∀ v, IsProbabilityMeasure (S.measure v) := S.isProb
  rw [fullResampling_expected_work_eq P hbad hfull, one_sub_mtBadProbability P hbad]
  simpa only [ENNReal.div_eq_inv_mul, mul_comm] using
    (ENNReal.div_lt_top (x := mtBadProbability P) (measure_ne_top _ _) hgood.ne')

theorem fullResampling_ae_exists_good (P : MTProcess S ι)
    (hbad : ∀ i, MeasurableSet (P.bad i))
    (hfull : ∀ i, P.footprint i = Finset.univ)
    (hgood : 0 < mtGoodProbability P) :
    ∀ᵐ ω ∂logMeasure S, ∃ T, MTGood P (randTraj P (initialStateFromLog ω) ω T) := by
  exact ae_randomInit_exists_good P hbad
    (fullResampling_expected_work_lt_top P hbad hfull hgood)

/-- A safe product box supplies a good-state probability lower bound. -/
theorem mtGoodProbability_ge_box (P : MTProcess S ι)
    (box : ∀ v, Set (S.space v)) (_hmeas : ∀ v, MeasurableSet (box v))
    (hsafe : ∀ s : MTState S, (∀ v, s v ∈ box v) → MTGood P s) :
    (∏ v, S.measure v (box v)) ≤ mtGoodProbability P := by
  have : ∀ v, IsProbabilityMeasure (S.measure v) := S.isProb
  have hsubset : Set.pi Set.univ box ⊆ mtGoodSet P := by
    intro s hs
    exact hsafe s (fun v => hs v (Set.mem_univ v))
  rw [← Measure.pi_pi (fun v => S.measure v) box]
  exact measure_mono hsubset

theorem mtGoodProbability_pos_of_box (P : MTProcess S ι)
    (box : ∀ v, Set (S.space v)) (hmeas : ∀ v, MeasurableSet (box v))
    (hpos : ∀ v, 0 < S.measure v (box v))
    (hsafe : ∀ s : MTState S, (∀ v, s v ∈ box v) → MTGood P s) :
    0 < mtGoodProbability P := by
  have hp : (∏ v, S.measure v (box v)) ≠ 0 :=
    Finset.prod_ne_zero_iff.mpr (fun v _ => (hpos v).ne')
  exact lt_of_lt_of_le (lt_of_le_of_ne zero_le hp.symm)
    (mtGoodProbability_ge_box P box hmeas hsafe)

/-- A finite analytic box certificate gives an explicit work bound. -/
theorem fullResampling_expected_work_le_of_box (P : MTProcess S ι)
    (hbad : ∀ i, MeasurableSet (P.bad i))
    (hfull : ∀ i, P.footprint i = Finset.univ)
    (box : ∀ v, Set (S.space v)) (hmeas : ∀ v, MeasurableSet (box v))
    (hsafe : ∀ s : MTState S, (∀ v, s v ∈ box v) → MTGood P s) :
    randomInitETLog P ≤ (∏ v, S.measure v (box v))⁻¹ := by
  have : ∀ v, IsProbabilityMeasure (S.measure v) := S.isProb
  rw [fullResampling_expected_work_eq P hbad hfull, one_sub_mtBadProbability P hbad]
  calc
    mtBadProbability P * (mtGoodProbability P)⁻¹ ≤ 1 * (mtGoodProbability P)⁻¹ :=
      mul_le_mul prob_le_one le_rfl zero_le zero_le
    _ ≤ (∏ v, S.measure v (box v))⁻¹ := by
      rw [one_mul]
      exact ENNReal.inv_le_inv.mpr (mtGoodProbability_ge_box P box hmeas hsafe)

theorem fullResampling_box_expected_work_lt_top (P : MTProcess S ι)
    (hbad : ∀ i, MeasurableSet (P.bad i))
    (hfull : ∀ i, P.footprint i = Finset.univ)
    (box : ∀ v, Set (S.space v)) (hmeas : ∀ v, MeasurableSet (box v))
    (hpos : ∀ v, 0 < S.measure v (box v))
    (hsafe : ∀ s : MTState S, (∀ v, s v ∈ box v) → MTGood P s) :
    randomInitETLog P < ⊤ := by
  exact fullResampling_expected_work_lt_top P hbad hfull
    (mtGoodProbability_pos_of_box P box hmeas hpos hsafe)

theorem fullResampling_globally_repairable (P : MTProcess S ι)
    (edges : MTState S → MTState S → Prop)
    (hbad : ∀ i, MeasurableSet (P.bad i))
    (hfull : ∀ i, P.footprint i = Finset.univ)
    (hgood : 0 < mtGoodProbability P) : globally_repairable (mtRepairGraph P edges) := by
  exact mtRepairGraph_globally_repairable_of_randomInitETLog_lt_top P edges hbad
    (fullResampling_expected_work_lt_top P hbad hfull hgood)

end RepairDrift

#check @RepairDrift.mtGoodProbability_add_bad
#check @RepairDrift.one_sub_mtBadProbability
#check @RepairDrift.fullResampling_count
#check @RepairDrift.fullResampling_randTraj_randomInit
#check @RepairDrift.measurableSet_mtBadSlotEvent
#check @RepairDrift.mtBadSlotEvent_dependsOn
#check @RepairDrift.mtSlotBlock_disjoint
#check @RepairDrift.logMeasure_mtBadSlotEvent
#check @RepairDrift.fullResampling_runningEvent_eq
#check @RepairDrift.fullResampling_running_probability
#check @RepairDrift.fullResampling_expected_work_eq
#check @RepairDrift.fullResampling_expected_work_lt_top
#check @RepairDrift.fullResampling_ae_exists_good
#check @RepairDrift.mtGoodProbability_ge_box
#check @RepairDrift.mtGoodProbability_pos_of_box
#check @RepairDrift.fullResampling_expected_work_le_of_box
#check @RepairDrift.fullResampling_box_expected_work_lt_top
#check @RepairDrift.fullResampling_globally_repairable
