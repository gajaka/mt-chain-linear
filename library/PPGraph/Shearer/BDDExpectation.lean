/-
  PPGraphShearerBDDExpectation.lean

  Attribute the work of the existing randomly initialized MT process to
  its full dependency components. Counts and expectations split exactly;
  each component has its own Shearer expected-work budget. The local
  budget theorem needs positivity only on that full component, even if
  another component is not certified. Almost-sure global termination is
  claimed only when every component satisfies the criterion.

  These are consequences of the stable-sequence bound and the existing
  BDD partition, with no additional probability or termination assumptions.
  The measured cost is resampling work, not elapsed scheduling time.
-/

module

public import PPGraph.Dependency.Partition
public import PPGraph.Shearer.BDDBudget
public import PPGraph.Shearer.ComponentOccurrence

@[expose] public section

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open MeasureTheory Classical
open scoped ENNReal

namespace Shearer

variable {V : Type} [DecidableEq V] {S : VarSpaces V} {ι : Type}
    [Fintype ι] [DecidableEq ι] [Nonempty ι]

/-- Work attributable to a finite set of event labels in the same global run. -/
noncomputable def randomInitSetResamplingCount (P : MTProcess S ι)
    (K : Finset ι) (ω : LogSpace S) : ℝ≥0∞ :=
  ∑ α ∈ K, randomInitResamplingCount P ω α

/-- Expected work of that label set under the original slot-zero law. -/
noncomputable def randomInitExpectedSetResamplingCount (P : MTProcess S ι)
    (K : Finset ι) : ℝ≥0∞ :=
  ∫⁻ ω, randomInitSetResamplingCount P K ω ∂logMeasure S

/-- Linearity remains valid before any finiteness or termination is known. -/
theorem randomInitExpectedSetResamplingCount_eq_sum (P : MTProcess S ι)
    (hbad : ∀ i, MeasurableSet (P.bad i)) (K : Finset ι) :
    randomInitExpectedSetResamplingCount P K =
      ∑ α ∈ K, randomInitExpectedResamplingCount P α := by
  unfold randomInitExpectedSetResamplingCount randomInitSetResamplingCount
    randomInitExpectedResamplingCount
  exact lintegral_finsetSum K
    (fun α _ => measurable_randomInitResamplingCount P hbad α)

/-- The full stopped log is the sum of work over distinct BDD components. -/
theorem randomInitTLog_eq_sum_componentCounts (P : MTProcess S ι)
    (ω : LogSpace S) :
    randomInitTLog P ω =
      ∑ K ∈ Finset.univ.image (compOf P.footprint Finset.univ),
        randomInitSetResamplingCount P K ω := by
  rw [randomInitTLog_eq_sum_resamplingCount]
  exact (sum_compOf_groups P.footprint Finset.univ
    (fun α => randomInitResamplingCount P ω α)).symm

/-- Component attribution is also exact after taking expectations. -/
theorem randomInitETLog_eq_sum_componentExpectations (P : MTProcess S ι)
    (hbad : ∀ i, MeasurableSet (P.bad i)) :
    randomInitETLog P =
      ∑ K ∈ Finset.univ.image (compOf P.footprint Finset.univ),
        randomInitExpectedSetResamplingCount P K := by
  rw [randomInitETLog_eq_sum_expectedResamplingCount P hbad]
  simp_rw [randomInitExpectedSetResamplingCount_eq_sum P hbad]
  exact (sum_compOf_groups P.footprint Finset.univ
    (randomInitExpectedResamplingCount P)).symm

/-- A certified full component has finite expected resampling work even if
other components are uncertified. This does not assert scheduling fairness
or that the component is eventually selected and repaired. -/
theorem randomInitExpectedComponentCount_le_budget [Fintype V]
    (P : MTProcess S ι) (hbad : ∀ i, MeasurableSet (P.bad i))
    (p : ι → ℝ)
    (hp : ∀ i, event_prob P.bad (Measure.pi (fun v => S.measure v)) i ≤ p i)
    (c : ι)
    (hcriterion : StrictCriterion (dependencyGraph P.footprint) p
      (compOf P.footprint Finset.univ c)) :
    randomInitExpectedSetResamplingCount P (compOf P.footprint Finset.univ c) ≤
      ENNReal.ofReal (∑ α ∈ compOf P.footprint Finset.univ c,
        stableBudget (dependencyGraph P.footprint) p
          (compOf P.footprint Finset.univ c) {α}) := by
  rw [randomInitExpectedSetResamplingCount_eq_sum P hbad]
  have hn := (event_prob_bounds P p hp).1
  calc
    _ ≤ ∑ α ∈ compOf P.footprint Finset.univ c,
        ENNReal.ofReal (stableBudget (dependencyGraph P.footprint) p
          (compOf P.footprint Finset.univ c) {α}) :=
      Finset.sum_le_sum (fun α hα =>
        randomInitExpectedResamplingCount_le_componentBudget
          P hbad p hp c α hα hcriterion)
    _ = _ := (ENNReal.ofReal_sum_of_nonneg (fun α _ =>
      stableBudget_nonneg (dependencyGraph P.footprint) p
        (compOf P.footprint Finset.univ c) {α} (fun i _ => hn i) hcriterion)).symm

theorem randomInitExpectedComponentCount_lt_top [Fintype V]
    (P : MTProcess S ι) (hbad : ∀ i, MeasurableSet (P.bad i))
    (p : ι → ℝ)
    (hp : ∀ i, event_prob P.bad (Measure.pi (fun v => S.measure v)) i ≤ p i)
    (c : ι)
    (hcriterion : StrictCriterion (dependencyGraph P.footprint) p
      (compOf P.footprint Finset.univ c)) :
    randomInitExpectedSetResamplingCount P (compOf P.footprint Finset.univ c) < ⊤ :=
  (randomInitExpectedComponentCount_le_budget P hbad p hp c hcriterion).trans_lt
    ENNReal.ofReal_lt_top

omit [Nonempty ι] in
/-- The global Shearer budget is exactly the sum of local component budgets;
the repeated copies indexed by vertices are removed by the image finset. -/
theorem sum_stableBudget_eq_sum_componentBudgets (P : MTProcess S ι)
    (p : ι → ℝ)
    (hcriterion : StrictCriterion (dependencyGraph P.footprint) p Finset.univ) :
    (∑ α : ι, stableBudget (dependencyGraph P.footprint) p Finset.univ {α}) =
      ∑ K ∈ Finset.univ.image (compOf P.footprint Finset.univ),
        ∑ α ∈ K, stableBudget (dependencyGraph P.footprint) p K {α} := by
  rw [← sum_compOf_groups P.footprint Finset.univ
    (fun α => stableBudget (dependencyGraph P.footprint) p Finset.univ {α})]
  apply Finset.sum_congr rfl
  intro K hK
  obtain ⟨c, _, rfl⟩ := Finset.mem_image.mp hK
  exact Finset.sum_congr rfl (fun α hα =>
    stableBudget_singleton_compOf P.footprint p Finset.univ c α hα hcriterion)

/-- Checking the strict criterion separately on every full component gives
an expected-work bound stated entirely in terms of those local components. -/
theorem randomInitETLog_le_sum_componentBudgets [Fintype V]
    (P : MTProcess S ι) (hbad : ∀ i, MeasurableSet (P.bad i))
    (p : ι → ℝ)
    (hp : ∀ i, event_prob P.bad (Measure.pi (fun v => S.measure v)) i ≤ p i)
    (hcomponents : ∀ c, StrictCriterion (dependencyGraph P.footprint) p
      (compOf P.footprint Finset.univ c)) :
    randomInitETLog P ≤ ENNReal.ofReal
      (∑ K ∈ Finset.univ.image (compOf P.footprint Finset.univ),
        ∑ α ∈ K, stableBudget (dependencyGraph P.footprint) p K {α}) := by
  have hc : StrictCriterion (dependencyGraph P.footprint) p Finset.univ :=
    (strictCriterion_iff_components P.footprint p Finset.univ).mpr
      (fun c _ => hcomponents c)
  rw [← sum_stableBudget_eq_sum_componentBudgets P p hc]
  exact randomInitETLog_le_sum_stableBudget P hbad p hp hc

theorem randomInitETLog_lt_top_of_components [Fintype V]
    (P : MTProcess S ι) (hbad : ∀ i, MeasurableSet (P.bad i))
    (p : ι → ℝ)
    (hp : ∀ i, event_prob P.bad (Measure.pi (fun v => S.measure v)) i ≤ p i)
    (hcomponents : ∀ c, StrictCriterion (dependencyGraph P.footprint) p
      (compOf P.footprint Finset.univ c)) : randomInitETLog P < ⊤ :=
  (randomInitETLog_le_sum_componentBudgets P hbad p hp hcomponents).trans_lt
    ENNReal.ofReal_lt_top

/-- Global termination follows once every component carries its certificate. -/
theorem ae_randomInit_exists_good_of_components [Fintype V]
    (P : MTProcess S ι) (hbad : ∀ i, MeasurableSet (P.bad i))
    (p : ι → ℝ)
    (hp : ∀ i, event_prob P.bad (Measure.pi (fun v => S.measure v)) i ≤ p i)
    (hcomponents : ∀ c, StrictCriterion (dependencyGraph P.footprint) p
      (compOf P.footprint Finset.univ c)) :
    ∀ᵐ ω ∂logMeasure S,
      ∃ T : ℕ, MTGood P (randTraj P (initialStateFromLog ω) ω T) :=
  ae_randomInit_exists_good P hbad
    (randomInitETLog_lt_top_of_components P hbad p hp hcomponents)

end Shearer

#check @Shearer.randomInitExpectedSetResamplingCount_eq_sum
#check @Shearer.randomInitTLog_eq_sum_componentCounts
#check @Shearer.randomInitETLog_eq_sum_componentExpectations
#check @Shearer.randomInitExpectedComponentCount_le_budget
#check @Shearer.randomInitExpectedComponentCount_lt_top
#check @Shearer.sum_stableBudget_eq_sum_componentBudgets
#check @Shearer.randomInitETLog_le_sum_componentBudgets
#check @Shearer.randomInitETLog_lt_top_of_components
#check @Shearer.ae_randomInit_exists_good_of_components
