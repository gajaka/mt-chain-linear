/-
  The pickFirstViolated specialization of He--Li--Sun Theorem 1.6.
  The arbitrary-selection theorem is in PPGraphHLSPolicyExpectation.lean.
  Actual intersection lower bounds on a dependency matching allow the
  smaller vector p^- = p - delta^2 / 17 in the Shearer convergence test.
  The expectation bound precedes, and implies, termination.
  Source: https://arxiv.org/abs/2111.06527, Sections 3.1--3.3.
-/
module

public import PPGraph.HLS.Probability.RefinedProbability
public import PPGraph.HLS.Probability.RootUnion
public import PPGraph.MoserTardos.Bounds.Termination

@[expose] public section

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option backward.isDefEq.respectTransparency false

open Classical MeasureTheory
open scoped ENNReal

namespace HLS

open WitnessDAG

variable {V : Type} [DecidableEq V] [Fintype V] {S : VarSpaces V}
  {ι : Type} [Fintype ι] [DecidableEq ι] [Nonempty ι]

theorem eventProbability_le_one (P : MTProcess S ι) (p : ι → ℝ)
    (hprob : ∀ i, (Measure.pi (fun a => S.measure a)).real (P.bad i) = p i) : ∀ i, p i ≤ 1 := by
  have : ∀ a, IsProbabilityMeasure (S.measure a) := S.isProb
  intro i
  rw [← hprob i]
  exact measureReal_le_one

theorem randomInitExpectedResamplingCount_le_tsum_refinedWeight
    (P : MTProcess S ι) (hbad : ∀ i, MeasurableSet (P.bad i)) (p : ι → ℝ)
    (hprob : ∀ i, (Measure.pi (fun a => S.measure a)).real (P.bad i) = p i)
    (hp : ∀ i, 0 < p i) (O : OverlapBounds (Shearer.dependencyGraph P.footprint) p)
    (hInt : ∀ i, O.delta i ≤ (Measure.pi (fun a => S.measure a)).real
      (P.bad i ∩ P.bad (O.matching.mate i))) (α : ι) :
    randomInitExpectedResamplingCount P α ≤
      ∑' D : ProperFamily (Shearer.dependencyGraph P.footprint) Finset.univ α, refinedWeight O D.val := by
  calc
    _ = ∑' r : ℕ, logMeasure S (ordinalOccurrence P α r) :=
      randomInitExpectedResamplingCount_eq_tsum_ordinalOccurrence P hbad α
    _ ≤ ∑' r : ℕ, logMeasure S (rootUnion P α r) :=
      ENNReal.tsum_le_tsum (fun r => measure_mono (ordinalOccurrence_subset_rootUnion P α r))
    _ ≤ ∑' r : ℕ, ∑' D : RootFamily (Shearer.dependencyGraph P.footprint) α r,
        logMeasure (augmentedSpaces S) (unitCheck P O.matching D.val) :=
      ENNReal.tsum_le_tsum (fun r => measure_rootUnion_le_tsum_unitCheck P hbad O.matching α r)
    _ ≤ ∑' r : ℕ, ∑' D : RootFamily (Shearer.dependencyGraph P.footprint) α r,
        refinedWeight O D.val :=
      ENNReal.tsum_le_tsum (fun r => ENNReal.tsum_le_tsum (fun D =>
        logMeasure_unitCheck_le_refinedWeight P hbad p hprob hp O hInt D.val D.property.1))
    _ ≤ _ := tsum_rootFamily_weight_le _ α (refinedWeight O)

/-- Intersection-sensitive expected resampling bound for each event. -/
theorem randomInitExpectedResamplingCount_le_stableBudget
    (P : MTProcess S ι) (hbad : ∀ i, MeasurableSet (P.bad i)) (p : ι → ℝ)
    (hprob : ∀ i, (Measure.pi (fun a => S.measure a)).real (P.bad i) = p i)
    (hp : ∀ i, 0 < p i) (O : OverlapBounds (Shearer.dependencyGraph P.footprint) p)
    (hInt : ∀ i, O.delta i ≤ (Measure.pi (fun a => S.measure a)).real
      (P.bad i ∩ P.bad (O.matching.mate i)))
    (hc : Shearer.StrictCriterion (Shearer.dependencyGraph P.footprint) O.reduced Finset.univ) (α : ι) :
    randomInitExpectedResamplingCount P α ≤
      ENNReal.ofReal (Shearer.stableBudget (Shearer.dependencyGraph P.footprint) O.reduced Finset.univ {α}) :=
  (randomInitExpectedResamplingCount_le_tsum_refinedWeight P hbad p hprob hp O hInt α).trans
    (tsum_refinedWeight_le_stableBudget O hp (eventProbability_le_one P p hprob) α hc)

/-- The HLS p^- criterion bounds the existing MT expected work, with no termination premise. -/
theorem randomInitETLog_le_sum_stableBudget
    (P : MTProcess S ι) (hbad : ∀ i, MeasurableSet (P.bad i)) (p : ι → ℝ)
    (hprob : ∀ i, (Measure.pi (fun a => S.measure a)).real (P.bad i) = p i)
    (hp : ∀ i, 0 < p i) (O : OverlapBounds (Shearer.dependencyGraph P.footprint) p)
    (hInt : ∀ i, O.delta i ≤ (Measure.pi (fun a => S.measure a)).real
      (P.bad i ∩ P.bad (O.matching.mate i)))
    (hc : Shearer.StrictCriterion (Shearer.dependencyGraph P.footprint) O.reduced Finset.univ) :
    randomInitETLog P ≤ ENNReal.ofReal
      (∑ α : ι, Shearer.stableBudget (Shearer.dependencyGraph P.footprint) O.reduced Finset.univ {α}) := by
  have hp1 := eventProbability_le_one P p hprob
  calc
    randomInitETLog P = ∑ α : ι, randomInitExpectedResamplingCount P α :=
      randomInitETLog_eq_sum_expectedResamplingCount P hbad
    _ ≤ ∑ α : ι, ENNReal.ofReal
        (Shearer.stableBudget (Shearer.dependencyGraph P.footprint) O.reduced Finset.univ {α}) :=
      Finset.sum_le_sum (fun α _ => randomInitExpectedResamplingCount_le_stableBudget P hbad p hprob hp O hInt hc α)
    _ = _ := (ENNReal.ofReal_sum_of_nonneg (fun α _ =>
      Shearer.stableBudget_nonneg _ O.reduced Finset.univ {α}
        (fun i _ => (O.reduced_pos hp hp1 i).le) hc)).symm

theorem randomInitETLog_lt_top
    (P : MTProcess S ι) (hbad : ∀ i, MeasurableSet (P.bad i)) (p : ι → ℝ)
    (hprob : ∀ i, (Measure.pi (fun a => S.measure a)).real (P.bad i) = p i)
    (hp : ∀ i, 0 < p i) (O : OverlapBounds (Shearer.dependencyGraph P.footprint) p)
    (hInt : ∀ i, O.delta i ≤ (Measure.pi (fun a => S.measure a)).real
      (P.bad i ∩ P.bad (O.matching.mate i)))
    (hc : Shearer.StrictCriterion (Shearer.dependencyGraph P.footprint) O.reduced Finset.univ) :
    randomInitETLog P < ⊤ :=
  (randomInitETLog_le_sum_stableBudget P hbad p hprob hp O hInt hc).trans_lt ENNReal.ofReal_lt_top

/-- First-violated specialization of Theorem 1.6: E[T] <= m/epsilon. -/
theorem randomInitETLog_le_card_div_slack
    (P : MTProcess S ι) (hbad : ∀ i, MeasurableSet (P.bad i)) (p : ι → ℝ)
    (hprob : ∀ i, (Measure.pi (fun a => S.measure a)).real (P.bad i) = p i)
    (hp : ∀ i, 0 < p i) (O : OverlapBounds (Shearer.dependencyGraph P.footprint) p)
    (hInt : ∀ i, O.delta i ≤ (Measure.pi (fun a => S.measure a)).real
      (P.bad i ∩ P.bad (O.matching.mate i))) (ε : ℝ) (hε : 0 < ε)
    (hslack : Shearer.StrictCriterion (Shearer.dependencyGraph P.footprint)
      (fun i => (1 + ε) * O.reduced i) Finset.univ) :
    randomInitETLog P ≤ ENNReal.ofReal ((Fintype.card ι : ℝ) / ε) := by
  have hp1 := eventProbability_le_one P p hprob
  have hn : ∀ i, 0 ≤ O.reduced i := fun i => (O.reduced_pos hp hp1 i).le
  have hc := Shearer.strictCriterion_mono_weights (Shearer.dependencyGraph P.footprint)
    O.reduced _ Finset.univ (fun i _ => by nlinarith [hn i]) hslack
  have hsum := Shearer.sum_stableBudget_le_card_div_slack (Shearer.dependencyGraph P.footprint)
    O.reduced Finset.univ ε hε (fun i _ => hn i) hslack
  exact (randomInitETLog_le_sum_stableBudget P hbad p hprob hp O hInt hc).trans
    (ENNReal.ofReal_le_ofReal (by simpa only [Finset.card_univ] using hsum))

theorem ae_randomInit_exists_good
    (P : MTProcess S ι) (hbad : ∀ i, MeasurableSet (P.bad i)) (p : ι → ℝ)
    (hprob : ∀ i, (Measure.pi (fun a => S.measure a)).real (P.bad i) = p i)
    (hp : ∀ i, 0 < p i) (O : OverlapBounds (Shearer.dependencyGraph P.footprint) p)
    (hInt : ∀ i, O.delta i ≤ (Measure.pi (fun a => S.measure a)).real
      (P.bad i ∩ P.bad (O.matching.mate i)))
    (hc : Shearer.StrictCriterion (Shearer.dependencyGraph P.footprint) O.reduced Finset.univ) :
    ∀ᵐ ω ∂logMeasure S, ∃ T : ℕ, MTGood P (randTraj P (initialStateFromLog ω) ω T) :=
  _root_.ae_randomInit_exists_good P hbad (randomInitETLog_lt_top P hbad p hprob hp O hInt hc)

theorem logMeasure_randomInit_termination_eq_one
    (P : MTProcess S ι) (hbad : ∀ i, MeasurableSet (P.bad i)) (p : ι → ℝ)
    (hprob : ∀ i, (Measure.pi (fun a => S.measure a)).real (P.bad i) = p i)
    (hp : ∀ i, 0 < p i) (O : OverlapBounds (Shearer.dependencyGraph P.footprint) p)
    (hInt : ∀ i, O.delta i ≤ (Measure.pi (fun a => S.measure a)).real
      (P.bad i ∩ P.bad (O.matching.mate i)))
    (hc : Shearer.StrictCriterion (Shearer.dependencyGraph P.footprint) O.reduced Finset.univ) :
    logMeasure S {ω | ∃ T : ℕ, MTGood P (randTraj P (initialStateFromLog ω) ω T)} = 1 :=
  _root_.logMeasure_randomInit_termination_eq_one P hbad (randomInitETLog_lt_top P hbad p hprob hp O hInt hc)

end HLS

#check @HLS.eventProbability_le_one
#check @HLS.randomInitExpectedResamplingCount_le_tsum_refinedWeight
#check @HLS.randomInitExpectedResamplingCount_le_stableBudget
#check @HLS.randomInitETLog_le_sum_stableBudget
#check @HLS.randomInitETLog_lt_top
#check @HLS.randomInitETLog_le_card_div_slack
#check @HLS.ae_randomInit_exists_good
#check @HLS.logMeasure_randomInit_termination_eq_one
