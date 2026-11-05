/-
  PPGraphShearerExpectation.lean

  Strict Shearer positivity bounds the expected stopped log length of the
  existing MT process initialized from slot zero of its random table.
  Distinct occurrences of one event have distinct stable layer sequences;
  their probabilities are bounded by sequence weights. The stable-family
  sum is at most q_{alpha}/q_empty, so summing over events bounds E[T_LOG].

  Source: the Kolipaka--Szegedy bound, as presented in Vondrak's
  MATH233A (2018), lecture 8. The coefficient convention is the one in
  PPGraphShearerStable: stableBudget({alpha}) = q_{alpha}/q_empty.
  https://theory.stanford.edu/~jvondrak/MATH233A-2018/Math233-lec08.pdf

  Neither termination nor finiteness of the counts is assumed. Almost-sure
  termination follows from the resulting finite expectation through the
  existing stopped-log bridge.
-/

module

public import PPGraph.Shearer.SequenceProbability
public import PPGraph.MoserTardos.Bounds.Termination
public import PPGraph.LLL.General

@[expose] public section

set_option autoImplicit false
-- MTState and CertVars are aliases of the Pi state and footprint families.
set_option backward.isDefEq.respectTransparency false

open MeasureTheory Classical
open scoped ENNReal

namespace Shearer

variable {V : Type} [DecidableEq V] {S : VarSpaces V} {ι : Type}
    [Fintype ι] [DecidableEq ι] [Nonempty ι]

/-- The probability majorant vanishes outside the proper stable family. -/
theorem logMeasure_sequenceOccurrence_le_properFamilyWeight [Fintype V]
    (P : MTProcess S ι) (hbad : ∀ i, MeasurableSet (P.bad i))
    (p : ι → ℝ) (hp_nonneg : ∀ i, 0 ≤ p i)
    (hp : ∀ i, Measure.pi (fun v => S.measure v) (P.bad i) ≤ ENNReal.ofReal (p i))
    (α : ι) (L : List (Finset ι)) :
    logMeasure S (sequenceOccurrence P α L) ≤
      properFamilyWeight (dependencyGraph P.footprint) p Finset.univ {α} L := by
  by_cases hL : L ∈ properFamily (dependencyGraph P.footprint) Finset.univ {α}
  · simpa only [properFamilyWeight, Set.indicator_of_mem hL] using
      logMeasure_sequenceOccurrence_le_sequenceWeight P hbad p hp_nonneg hp α L
  · rw [sequenceOccurrence_eq_empty_of_not_mem_properFamily P α L hL, measure_empty]
    exact zero_le

/-- Reindexing the stopped event count and applying Tonelli loses no multiplicities. -/
theorem randomInitExpectedResamplingCount_le_tsum_properFamilyWeight [Fintype V]
    (P : MTProcess S ι) (hbad : ∀ i, MeasurableSet (P.bad i))
    (p : ι → ℝ) (hp_nonneg : ∀ i, 0 ≤ p i)
    (hp : ∀ i, Measure.pi (fun v => S.measure v) (P.bad i) ≤ ENNReal.ofReal (p i))
    (α : ι) :
    randomInitExpectedResamplingCount P α ≤ ∑' L : List (Finset ι),
      properFamilyWeight (dependencyGraph P.footprint) p Finset.univ {α} L := by
  rw [randomInitExpectedResamplingCount_eq_tsum_sequenceOccurrence P hbad α]
  exact ENNReal.tsum_le_tsum (fun L =>
    logMeasure_sequenceOccurrence_le_properFamilyWeight P hbad p hp_nonneg hp α L)

/-- The Shearer coefficient ratio bounds the expected number of resamplings
of each event under the original slot-zero initialization law. -/
theorem randomInitExpectedResamplingCount_le_stableBudget_of_measure_le [Fintype V]
    (P : MTProcess S ι) (hbad : ∀ i, MeasurableSet (P.bad i))
    (p : ι → ℝ) (hp_nonneg : ∀ i, 0 ≤ p i)
    (hp : ∀ i, Measure.pi (fun v => S.measure v) (P.bad i) ≤ ENNReal.ofReal (p i))
    (hcriterion : StrictCriterion (dependencyGraph P.footprint) p Finset.univ)
    (α : ι) : randomInitExpectedResamplingCount P α ≤
      ENNReal.ofReal (stableBudget (dependencyGraph P.footprint) p Finset.univ {α}) := by
  have hsingleton : Independent (dependencyGraph P.footprint) {α} := by
    intro a ha b hb
    simp only [Finset.mem_singleton] at ha hb
    subst a
    subst b
    exact (dependencyGraph P.footprint).irrefl
  exact (randomInitExpectedResamplingCount_le_tsum_properFamilyWeight
    P hbad p hp_nonneg hp α).trans
      (tsum_properFamilyWeight_le (dependencyGraph P.footprint) p Finset.univ {α}
        (Finset.subset_univ _) hsingleton (fun i _ => hp_nonneg i) hcriterion)

omit [DecidableEq V] [Fintype ι] [DecidableEq ι] [Nonempty ι] in
/-- A real upper bound on event probabilities automatically supplies both
nonnegativity and the equivalent ENNReal upper bound. -/
theorem event_prob_bounds [Fintype V] (P : MTProcess S ι) (p : ι → ℝ)
    (hp : ∀ i, event_prob P.bad (Measure.pi (fun v => S.measure v)) i ≤ p i) :
    (∀ i, 0 ≤ p i) ∧
      ∀ i, Measure.pi (fun v => S.measure v) (P.bad i) ≤ ENNReal.ofReal (p i) := by
  have : ∀ v, IsProbabilityMeasure (S.measure v) := S.isProb
  have : IsProbabilityMeasure (Measure.pi (fun v => S.measure v) : Measure (MTState S)) :=
    Measure.pi.instIsProbabilityMeasure _
  have hn (i : ι) : 0 ≤ p i := ENNReal.toReal_nonneg.trans (hp i)
  refine ⟨hn, fun i => ?_⟩
  exact (ENNReal.le_ofReal_iff_toReal_le (measure_ne_top _ _) (hn i)).mpr (hp i)

/-- Only measurable bad events, their probability upper bounds, and strict
Shearer positivity are needed for this event-wise expected-work bound. -/
theorem randomInitExpectedResamplingCount_le_stableBudget [Fintype V]
    (P : MTProcess S ι) (hbad : ∀ i, MeasurableSet (P.bad i))
    (p : ι → ℝ)
    (hp : ∀ i, event_prob P.bad (Measure.pi (fun v => S.measure v)) i ≤ p i)
    (hcriterion : StrictCriterion (dependencyGraph P.footprint) p Finset.univ)
    (α : ι) : randomInitExpectedResamplingCount P α ≤
      ENNReal.ofReal (stableBudget (dependencyGraph P.footprint) p Finset.univ {α}) := by
  obtain ⟨hn, hm⟩ := event_prob_bounds P p hp
  exact randomInitExpectedResamplingCount_le_stableBudget_of_measure_le
    P hbad p hn hm hcriterion α

/-- Summing the singleton Shearer budgets bounds the existing expected T_LOG. -/
theorem randomInitETLog_le_sum_stableBudget [Fintype V]
    (P : MTProcess S ι) (hbad : ∀ i, MeasurableSet (P.bad i))
    (p : ι → ℝ)
    (hp : ∀ i, event_prob P.bad (Measure.pi (fun v => S.measure v)) i ≤ p i)
    (hcriterion : StrictCriterion (dependencyGraph P.footprint) p Finset.univ) :
    randomInitETLog P ≤ ENNReal.ofReal
      (∑ α : ι, stableBudget (dependencyGraph P.footprint) p Finset.univ {α}) := by
  have hn := (event_prob_bounds P p hp).1
  calc
    randomInitETLog P = ∑ α : ι, randomInitExpectedResamplingCount P α :=
      randomInitETLog_eq_sum_expectedResamplingCount P hbad
    _ ≤ ∑ α : ι,
        ENNReal.ofReal (stableBudget (dependencyGraph P.footprint) p Finset.univ {α}) :=
      Finset.sum_le_sum (fun α _ =>
        randomInitExpectedResamplingCount_le_stableBudget P hbad p hp hcriterion α)
    _ = ENNReal.ofReal
        (∑ α : ι, stableBudget (dependencyGraph P.footprint) p Finset.univ {α}) :=
      (ENNReal.ofReal_sum_of_nonneg (fun α _ =>
        stableBudget_nonneg (dependencyGraph P.footprint) p Finset.univ {α}
          (fun i _ => hn i) hcriterion)).symm

/-- Strict Shearer positivity yields finite expected stopped log length. -/
theorem randomInitETLog_lt_top [Fintype V]
    (P : MTProcess S ι) (hbad : ∀ i, MeasurableSet (P.bad i))
    (p : ι → ℝ)
    (hp : ∀ i, event_prob P.bad (Measure.pi (fun v => S.measure v)) i ≤ p i)
    (hcriterion : StrictCriterion (dependencyGraph P.footprint) p Finset.univ) :
    randomInitETLog P < ⊤ :=
  (randomInitETLog_le_sum_stableBudget P hbad p hp hcriterion).trans_lt ENNReal.ofReal_lt_top

/-- Almost every random table reaches a good state, as a consequence of
the finite expected-work theorem rather than a premise of its proof. -/
theorem ae_randomInit_exists_good_of_strictCriterion [Fintype V]
    (P : MTProcess S ι) (hbad : ∀ i, MeasurableSet (P.bad i))
    (p : ι → ℝ)
    (hp : ∀ i, event_prob P.bad (Measure.pi (fun v => S.measure v)) i ≤ p i)
    (hcriterion : StrictCriterion (dependencyGraph P.footprint) p Finset.univ) :
    ∀ᵐ ω ∂logMeasure S,
      ∃ T : ℕ, MTGood P (randTraj P (initialStateFromLog ω) ω T) :=
  ae_randomInit_exists_good P hbad (randomInitETLog_lt_top P hbad p hp hcriterion)

/-- The termination event of the original random-initialized MT process
has probability one under strict Shearer positivity. -/
theorem logMeasure_randomInit_termination_eq_one_of_strictCriterion [Fintype V]
    (P : MTProcess S ι) (hbad : ∀ i, MeasurableSet (P.bad i))
    (p : ι → ℝ)
    (hp : ∀ i, event_prob P.bad (Measure.pi (fun v => S.measure v)) i ≤ p i)
    (hcriterion : StrictCriterion (dependencyGraph P.footprint) p Finset.univ) :
    logMeasure S {ω | ∃ T : ℕ,
      MTGood P (randTraj P (initialStateFromLog ω) ω T)} = 1 :=
  logMeasure_randomInit_termination_eq_one P hbad
    (randomInitETLog_lt_top P hbad p hp hcriterion)

end Shearer

#check @Shearer.logMeasure_sequenceOccurrence_le_properFamilyWeight
#check @Shearer.randomInitExpectedResamplingCount_le_tsum_properFamilyWeight
#check @Shearer.randomInitExpectedResamplingCount_le_stableBudget_of_measure_le
#check @Shearer.event_prob_bounds
#check @Shearer.randomInitExpectedResamplingCount_le_stableBudget
#check @Shearer.randomInitETLog_le_sum_stableBudget
#check @Shearer.randomInitETLog_lt_top
#check @Shearer.ae_randomInit_exists_good_of_strictCriterion
#check @Shearer.logMeasure_randomInit_termination_eq_one_of_strictCriterion
