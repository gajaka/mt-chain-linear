/-
  He--Li--Sun intersection LLL with arbitrary admissible selection rules.
  The selection schedule is a parameter: it may use the entire execution
  history, and is not restricted to pickFirstViolated. Its only semantic
  obligation is to select a violated event whenever the state is not good.
  Measurability is explicit; the random initial state is drawn from slot 0,
  exactly as in HLS Algorithm 1. No termination hypothesis is used.

  Source: https://arxiv.org/abs/2111.06527, Theorem 1.6,
  Algorithm 1/footnote 2, and Sections 3.1--3.3.
-/
module

public import PPGraph.HLS.Probability.RefinedProbability
public import PPGraph.Integration.Policy.HLSCounting
public import PPGraph.Integration.Policy.History

@[expose] public section

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option backward.isDefEq.respectTransparency false

open Classical MeasureTheory MTPolicy
open scoped ENNReal

namespace HLS.Policy

open WitnessDAG

variable {V : Type} [DecidableEq V] [Fintype V] {S : VarSpaces V}
  {ι : Type} [Fintype ι] [DecidableEq ι] [Nonempty ι]

theorem eventProbability_le_one (P : MTProcess S ι) (p : ι → ℝ)
    (hprob : ∀ i, (Measure.pi (fun a => S.measure a)).real (P.bad i) = p i) : ∀ i, p i ≤ 1 := by
  have : ∀ a, IsProbabilityMeasure (S.measure a) := S.isProb
  intro i
  rw [← hprob i]
  exact measureReal_le_one

theorem expectedCount_le_tsum_refinedWeight
    (P : MTProcess S ι) (σ : MTPolicy.Schedule P) (hbad : ∀ i, MeasurableSet (P.bad i)) (p : ι → ℝ)
    (hprob : ∀ i, (Measure.pi (fun a => S.measure a)).real (P.bad i) = p i)
    (hp : ∀ i, 0 < p i) (O : OverlapBounds (Shearer.dependencyGraph P.footprint) p)
    (hInt : ∀ i, O.delta i ≤ (Measure.pi (fun a => S.measure a)).real
      (P.bad i ∩ P.bad (O.matching.mate i))) (α : ι) :
    expectedCount P σ α ≤
      ∑' D : ProperFamily (Shearer.dependencyGraph P.footprint) Finset.univ α, refinedWeight O D.val := by
  calc
    _ = ∑' r : ℕ, logMeasure S (ordinalOccurrence P σ α r) :=
      expectedCount_eq_tsum_ordinalOccurrence P σ hbad α
    _ ≤ ∑' r : ℕ, logMeasure S (rootUnion P α r) :=
      ENNReal.tsum_le_tsum (fun r => measure_mono (MTPolicy.ordinalOccurrence_subset_rootUnion P σ α r))
    _ ≤ ∑' r : ℕ, ∑' D : RootFamily (Shearer.dependencyGraph P.footprint) α r,
        logMeasure (augmentedSpaces S) (unitCheck P O.matching D.val) :=
      ENNReal.tsum_le_tsum (fun r => measure_rootUnion_le_tsum_unitCheck P hbad O.matching α r)
    _ ≤ ∑' r : ℕ, ∑' D : RootFamily (Shearer.dependencyGraph P.footprint) α r,
        refinedWeight O D.val :=
      ENNReal.tsum_le_tsum (fun r => ENNReal.tsum_le_tsum (fun D =>
        logMeasure_unitCheck_le_refinedWeight P hbad p hprob hp O hInt D.val D.property.1))
    _ ≤ _ := tsum_rootFamily_weight_le _ α (refinedWeight O)

/-- Intersection-sensitive expected resampling bound for each event. -/
theorem expectedCount_le_stableBudget
    (P : MTProcess S ι) (σ : MTPolicy.Schedule P) (hbad : ∀ i, MeasurableSet (P.bad i)) (p : ι → ℝ)
    (hprob : ∀ i, (Measure.pi (fun a => S.measure a)).real (P.bad i) = p i)
    (hp : ∀ i, 0 < p i) (O : OverlapBounds (Shearer.dependencyGraph P.footprint) p)
    (hInt : ∀ i, O.delta i ≤ (Measure.pi (fun a => S.measure a)).real
      (P.bad i ∩ P.bad (O.matching.mate i)))
    (hc : Shearer.StrictCriterion (Shearer.dependencyGraph P.footprint) O.reduced Finset.univ) (α : ι) :
    expectedCount P σ α ≤
      ENNReal.ofReal (Shearer.stableBudget (Shearer.dependencyGraph P.footprint) O.reduced Finset.univ {α}) :=
  (expectedCount_le_tsum_refinedWeight P σ hbad p hprob hp O hInt α).trans
    (tsum_refinedWeight_le_stableBudget O hp (eventProbability_le_one P p hprob) α hc)

/-- The HLS p^- criterion bounds every admissible schedule's expected work, with no termination premise. -/
theorem expectedWork_le_sum_stableBudget
    (P : MTProcess S ι) (σ : MTPolicy.Schedule P) (hbad : ∀ i, MeasurableSet (P.bad i)) (p : ι → ℝ)
    (hprob : ∀ i, (Measure.pi (fun a => S.measure a)).real (P.bad i) = p i)
    (hp : ∀ i, 0 < p i) (O : OverlapBounds (Shearer.dependencyGraph P.footprint) p)
    (hInt : ∀ i, O.delta i ≤ (Measure.pi (fun a => S.measure a)).real
      (P.bad i ∩ P.bad (O.matching.mate i)))
    (hc : Shearer.StrictCriterion (Shearer.dependencyGraph P.footprint) O.reduced Finset.univ) :
    expectedWork P σ ≤ ENNReal.ofReal
      (∑ α : ι, Shearer.stableBudget (Shearer.dependencyGraph P.footprint) O.reduced Finset.univ {α}) := by
  have hp1 := eventProbability_le_one P p hprob
  calc
    expectedWork P σ = ∑ α : ι, expectedCount P σ α :=
      expectedWork_eq_sum_expectedCount P σ hbad
    _ ≤ ∑ α : ι, ENNReal.ofReal
        (Shearer.stableBudget (Shearer.dependencyGraph P.footprint) O.reduced Finset.univ {α}) :=
      Finset.sum_le_sum (fun α _ => expectedCount_le_stableBudget P σ hbad p hprob hp O hInt hc α)
    _ = _ := (ENNReal.ofReal_sum_of_nonneg (fun α _ =>
      Shearer.stableBudget_nonneg _ O.reduced Finset.univ {α}
        (fun i _ => (O.reduced_pos hp hp1 i).le) hc)).symm

theorem expectedWork_lt_top
    (P : MTProcess S ι) (σ : MTPolicy.Schedule P) (hbad : ∀ i, MeasurableSet (P.bad i)) (p : ι → ℝ)
    (hprob : ∀ i, (Measure.pi (fun a => S.measure a)).real (P.bad i) = p i)
    (hp : ∀ i, 0 < p i) (O : OverlapBounds (Shearer.dependencyGraph P.footprint) p)
    (hInt : ∀ i, O.delta i ≤ (Measure.pi (fun a => S.measure a)).real
      (P.bad i ∩ P.bad (O.matching.mate i)))
    (hc : Shearer.StrictCriterion (Shearer.dependencyGraph P.footprint) O.reduced Finset.univ) :
    expectedWork P σ < ⊤ :=
  (expectedWork_le_sum_stableBudget P σ hbad p hprob hp O hInt hc).trans_lt ENNReal.ofReal_lt_top

/-- HLS Theorem 1.6 with arbitrary admissible selection: positive multiplicative slack gives E[T] <= m/epsilon. -/
theorem expectedWork_le_card_div_slack
    (P : MTProcess S ι) (σ : MTPolicy.Schedule P) (hbad : ∀ i, MeasurableSet (P.bad i)) (p : ι → ℝ)
    (hprob : ∀ i, (Measure.pi (fun a => S.measure a)).real (P.bad i) = p i)
    (hp : ∀ i, 0 < p i) (O : OverlapBounds (Shearer.dependencyGraph P.footprint) p)
    (hInt : ∀ i, O.delta i ≤ (Measure.pi (fun a => S.measure a)).real
      (P.bad i ∩ P.bad (O.matching.mate i))) (ε : ℝ) (hε : 0 < ε)
    (hslack : Shearer.StrictCriterion (Shearer.dependencyGraph P.footprint)
      (fun i => (1 + ε) * O.reduced i) Finset.univ) :
    expectedWork P σ ≤ ENNReal.ofReal ((Fintype.card ι : ℝ) / ε) := by
  have hp1 := eventProbability_le_one P p hprob
  have hn : ∀ i, 0 ≤ O.reduced i := fun i => (O.reduced_pos hp hp1 i).le
  have hc := Shearer.strictCriterion_mono_weights (Shearer.dependencyGraph P.footprint)
    O.reduced _ Finset.univ (fun i _ => by nlinarith [hn i]) hslack
  have hsum := Shearer.sum_stableBudget_le_card_div_slack (Shearer.dependencyGraph P.footprint)
    O.reduced Finset.univ ε hε (fun i _ => hn i) hslack
  exact (expectedWork_le_sum_stableBudget P σ hbad p hprob hp O hInt hc).trans
    (ENNReal.ofReal_le_ofReal (by simpa only [Finset.card_univ] using hsum))

theorem ae_exists_good
    (P : MTProcess S ι) (σ : MTPolicy.Schedule P) (hbad : ∀ i, MeasurableSet (P.bad i)) (p : ι → ℝ)
    (hprob : ∀ i, (Measure.pi (fun a => S.measure a)).real (P.bad i) = p i)
    (hp : ∀ i, 0 < p i) (O : OverlapBounds (Shearer.dependencyGraph P.footprint) p)
    (hInt : ∀ i, O.delta i ≤ (Measure.pi (fun a => S.measure a)).real
      (P.bad i ∩ P.bad (O.matching.mate i)))
    (hc : Shearer.StrictCriterion (Shearer.dependencyGraph P.footprint) O.reduced Finset.univ) :
    ∀ᵐ ω ∂logMeasure S, ∃ T : ℕ, MTGood P (MTPolicy.state P (σ.select ω) ω T) :=
  MTPolicy.ae_exists_good_of_expectedWork_lt_top P σ hbad
    (expectedWork_lt_top P σ hbad p hprob hp O hInt hc)

theorem measure_termination_eq_one
    (P : MTProcess S ι) (σ : MTPolicy.Schedule P) (hbad : ∀ i, MeasurableSet (P.bad i)) (p : ι → ℝ)
    (hprob : ∀ i, (Measure.pi (fun a => S.measure a)).real (P.bad i) = p i)
    (hp : ∀ i, 0 < p i) (O : OverlapBounds (Shearer.dependencyGraph P.footprint) p)
    (hInt : ∀ i, O.delta i ≤ (Measure.pi (fun a => S.measure a)).real
      (P.bad i ∩ P.bad (O.matching.mate i)))
    (hc : Shearer.StrictCriterion (Shearer.dependencyGraph P.footprint) O.reduced Finset.univ) :
    logMeasure S {ω | ∃ T : ℕ, MTGood P (MTPolicy.state P (σ.select ω) ω T)} = 1 :=
  MTPolicy.measure_termination_eq_one_of_expectedWork_lt_top P σ hbad
    (expectedWork_lt_top P σ hbad p hprob hp O hInt hc)

/-- The restated paper bound for the concrete online history-policy execution. -/
theorem history_expectedWork_le_card_div_slack
    (P : MTProcess S ι) (R : MTPolicy.HistoryRule P) (hbad : ∀ i, MeasurableSet (P.bad i)) (p : ι → ℝ)
    (hprob : ∀ i, (Measure.pi (fun a => S.measure a)).real (P.bad i) = p i)
    (hp : ∀ i, 0 < p i) (O : OverlapBounds (Shearer.dependencyGraph P.footprint) p)
    (hInt : ∀ i, O.delta i ≤ (Measure.pi (fun a => S.measure a)).real
      (P.bad i ∩ P.bad (O.matching.mate i))) (ε : ℝ) (hε : 0 < ε)
    (hslack : Shearer.StrictCriterion (Shearer.dependencyGraph P.footprint)
      (fun i => (1 + ε) * O.reduced i) Finset.univ) :
    expectedWork P (MTPolicy.fromHistory P R) ≤ ENNReal.ofReal ((Fintype.card ι : ℝ) / ε) :=
  expectedWork_le_card_div_slack P (MTPolicy.fromHistory P R) hbad p hprob hp O hInt ε hε hslack

theorem history_termination_eq_one
    (P : MTProcess S ι) (R : MTPolicy.HistoryRule P) (hbad : ∀ i, MeasurableSet (P.bad i)) (p : ι → ℝ)
    (hprob : ∀ i, (Measure.pi (fun a => S.measure a)).real (P.bad i) = p i)
    (hp : ∀ i, 0 < p i) (O : OverlapBounds (Shearer.dependencyGraph P.footprint) p)
    (hInt : ∀ i, O.delta i ≤ (Measure.pi (fun a => S.measure a)).real
      (P.bad i ∩ P.bad (O.matching.mate i)))
    (hc : Shearer.StrictCriterion (Shearer.dependencyGraph P.footprint) O.reduced Finset.univ) :
    logMeasure S {ω | ∃ T : ℕ, MTGood P (MTPolicy.historyRun P R ω T).1} = 1 := by
  have h := measure_termination_eq_one P (MTPolicy.fromHistory P R) hbad p hprob hp O hInt hc
  change logMeasure S {ω | ∃ T : ℕ, MTGood P
    (MTPolicy.state P (MTPolicy.historySelect P R ω) ω T)} = 1 at h
  simpa only [← MTPolicy.historyState_eq_state] using h

/-- Independent auxiliary randomness may select the schedule. Tonelli
    transfers the uniform conditional bound to its actual product law. -/
theorem randomized_expectedWork_le_sum_stableBudget
    (P : MTProcess S ι) {A : Type} [MeasurableSpace A]
    (ν : Measure A) [IsProbabilityMeasure ν] (σ : A → MTPolicy.Schedule P)
    (hjoint : Measurable (fun z : A × LogSpace S => MTPolicy.tLog P ((σ z.1).select z.2) z.2))
    (hbad : ∀ i, MeasurableSet (P.bad i)) (p : ι → ℝ)
    (hprob : ∀ i, (Measure.pi (fun a => S.measure a)).real (P.bad i) = p i)
    (hp : ∀ i, 0 < p i) (O : OverlapBounds (Shearer.dependencyGraph P.footprint) p)
    (hInt : ∀ i, O.delta i ≤ (Measure.pi (fun a => S.measure a)).real
      (P.bad i ∩ P.bad (O.matching.mate i)))
    (hc : Shearer.StrictCriterion (Shearer.dependencyGraph P.footprint) O.reduced Finset.univ) :
    (∫⁻ z, MTPolicy.tLog P ((σ z.1).select z.2) z.2 ∂ν.prod (logMeasure S)) ≤
      ENNReal.ofReal (∑ α : ι,
        Shearer.stableBudget (Shearer.dependencyGraph P.footprint) O.reduced Finset.univ {α}) := by
  rw [lintegral_prod _ hjoint.aemeasurable]
  calc
    (∫⁻ a, expectedWork P (σ a) ∂ν) ≤ ∫⁻ _a, ENNReal.ofReal (∑ α : ι,
        Shearer.stableBudget (Shearer.dependencyGraph P.footprint) O.reduced Finset.univ {α}) ∂ν :=
      lintegral_mono (fun a => expectedWork_le_sum_stableBudget P (σ a) hbad p hprob hp O hInt hc)
    _ = _ := by simp

theorem randomized_expectedWork_le_card_div_slack
    (P : MTProcess S ι) {A : Type} [MeasurableSpace A]
    (ν : Measure A) [IsProbabilityMeasure ν] (σ : A → MTPolicy.Schedule P)
    (hjoint : Measurable (fun z : A × LogSpace S => MTPolicy.tLog P ((σ z.1).select z.2) z.2))
    (hbad : ∀ i, MeasurableSet (P.bad i)) (p : ι → ℝ)
    (hprob : ∀ i, (Measure.pi (fun a => S.measure a)).real (P.bad i) = p i)
    (hp : ∀ i, 0 < p i) (O : OverlapBounds (Shearer.dependencyGraph P.footprint) p)
    (hInt : ∀ i, O.delta i ≤ (Measure.pi (fun a => S.measure a)).real
      (P.bad i ∩ P.bad (O.matching.mate i))) (ε : ℝ) (hε : 0 < ε)
    (hslack : Shearer.StrictCriterion (Shearer.dependencyGraph P.footprint)
      (fun i => (1 + ε) * O.reduced i) Finset.univ) :
    (∫⁻ z, MTPolicy.tLog P ((σ z.1).select z.2) z.2 ∂ν.prod (logMeasure S)) ≤
      ENNReal.ofReal ((Fintype.card ι : ℝ) / ε) := by
  rw [lintegral_prod _ hjoint.aemeasurable]
  calc
    (∫⁻ a, expectedWork P (σ a) ∂ν) ≤ ∫⁻ _a, ENNReal.ofReal ((Fintype.card ι : ℝ) / ε) ∂ν :=
      lintegral_mono (fun a => expectedWork_le_card_div_slack P (σ a) hbad p hprob hp O hInt ε hε hslack)
    _ = _ := by simp

theorem randomized_ae_exists_good
    (P : MTProcess S ι) {A : Type} [MeasurableSpace A]
    (ν : Measure A) [IsProbabilityMeasure ν] (σ : A → MTPolicy.Schedule P)
    (hjoint : Measurable (fun z : A × LogSpace S => MTPolicy.tLog P ((σ z.1).select z.2) z.2))
    (hbad : ∀ i, MeasurableSet (P.bad i)) (p : ι → ℝ)
    (hprob : ∀ i, (Measure.pi (fun a => S.measure a)).real (P.bad i) = p i)
    (hp : ∀ i, 0 < p i) (O : OverlapBounds (Shearer.dependencyGraph P.footprint) p)
    (hInt : ∀ i, O.delta i ≤ (Measure.pi (fun a => S.measure a)).real
      (P.bad i ∩ P.bad (O.matching.mate i)))
    (hc : Shearer.StrictCriterion (Shearer.dependencyGraph P.footprint) O.reduced Finset.univ) :
    ∀ᵐ z ∂ν.prod (logMeasure S), ∃ T : ℕ,
      MTGood P (MTPolicy.state P ((σ z.1).select z.2) z.2 T) := by
  have hf := (randomized_expectedWork_le_sum_stableBudget P ν σ hjoint hbad p hprob hp O hInt hc).trans_lt
    ENNReal.ofReal_lt_top
  have hae := MeasureTheory.ae_lt_top hjoint hf.ne
  filter_upwards [hae] with z hz
  exact (MTPolicy.tLog_lt_top_iff_exists_good P ((σ z.1).select z.2) z.2
    ((σ z.1).admissible z.2)).mp hz

end HLS.Policy

#check @HLS.Policy.eventProbability_le_one
#check @HLS.Policy.expectedCount_le_tsum_refinedWeight
#check @HLS.Policy.expectedCount_le_stableBudget
#check @HLS.Policy.expectedWork_le_sum_stableBudget
#check @HLS.Policy.expectedWork_lt_top
#check @HLS.Policy.expectedWork_le_card_div_slack
#check @HLS.Policy.ae_exists_good
#check @HLS.Policy.measure_termination_eq_one
#check @HLS.Policy.history_expectedWork_le_card_div_slack
#check @HLS.Policy.history_termination_eq_one
#check @HLS.Policy.randomized_expectedWork_le_sum_stableBudget
#check @HLS.Policy.randomized_expectedWork_le_card_div_slack
#check @HLS.Policy.randomized_ae_exists_good
