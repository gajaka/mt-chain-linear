/-
  PPGraphMoserTardosOccurrenceExpectation.lean

  Step 3: assemble the witness-tree bound on the expected stopped log
  length for the process initialized from slot 0 of its random table.

  E[Nα] = sum_U Pr[U occurs]
        ≤ sum_U 1_{canonical family}(U) * weight(U)
        = sup_D mtWeight(D, α) ≤ x(α).

  Summing over labels gives E[TLOG] ≤ sum_α x(α). Here x is the MT
  resampling budget used by Convergence, not the LLL parameter q;
  in the usual LLL parametrization that budget is q/(1-q).
  All count and expectation identities use ENNReal before finiteness
  is concluded. No termination assumption is used in the argument.
-/

module

public import PPGraph.MoserTardos.Counting.OccurrenceCounting
public import PPGraph.MoserTardos.Probability.OccurrenceProbability
public import PPGraph.MoserTardos.Witness.WitnessFamily

@[expose] public section

open MeasureTheory Classical
open scoped NNReal ENNReal

variable {V : Type} [DecidableEq V] {S : VarSpaces V} {ι : Type}
    [Fintype ι] [DecidableEq ι] [Nonempty ι]

/-- Only members of the canonical enumeration can occur. -/
theorem witnessOccurrence_eq_empty_of_not_mem_family (P : MTProcess S ι)
    (α : ι) (U : WTree ι) (hU : U ∉ witnessFamily P α) :
    witnessOccurrence P α U = ∅ := by
  apply Set.eq_empty_iff_forall_notMem.mpr
  intro ω hω
  exact hU (witnessOccurrence_nonempty_mem_wtreesUpTo P α U ⟨ω, hω⟩)

/-- The probability majorant vanishes off the canonical family,
    avoiding any overcount of different sibling orderings. -/
theorem logMeasure_witnessOccurrence_le_familyWeight [Fintype V]
    (P : MTProcess S ι) (hbad : ∀ i, MeasurableSet (P.bad i))
    (p : ι → ℝ≥0)
    (hp : ∀ i, Measure.pi (fun v => S.measure v) (P.bad i) ≤ (p i : ℝ≥0∞))
    (α : ι) (U : WTree ι) :
    logMeasure S (witnessOccurrence P α U) ≤ witnessFamilyWeight P p α U := by
  classical
  by_cases hU : U ∈ witnessFamily P α
  · simpa only [witnessFamilyWeight, Set.indicator_of_mem hU] using
      logMeasure_witnessOccurrence_le_weight P hbad p hp α U
  · rw [witnessOccurrence_eq_empty_of_not_mem_family P α U hU, measure_empty]
    exact zero_le

/-- The expectation is bounded by the sum over the whole canonical
    family, rather than by a sum over all ordered rooted trees. -/
theorem randomInitExpectedResamplingCount_le_tsum_familyWeight [Fintype V]
    (P : MTProcess S ι) (hbad : ∀ i, MeasurableSet (P.bad i))
    (p : ι → ℝ≥0)
    (hp : ∀ i, Measure.pi (fun v => S.measure v) (P.bad i) ≤ (p i : ℝ≥0∞))
    (α : ι) :
    randomInitExpectedResamplingCount P α ≤ ∑' U : WTree ι,
      witnessFamilyWeight P p α U := by
  rw [randomInitExpectedResamplingCount_eq_tsum_witnessOccurrence P hbad α]
  exact ENNReal.tsum_le_tsum (fun U =>
    logMeasure_witnessOccurrence_le_familyWeight P hbad p hp α U)

theorem randomInitExpectedResamplingCount_le_iSup_mtWeight [Fintype V]
    (P : MTProcess S ι) (hbad : ∀ i, MeasurableSet (P.bad i))
    (p : ι → ℝ≥0)
    (hp : ∀ i, Measure.pi (fun v => S.measure v) (P.bad i) ≤ (p i : ℝ≥0∞))
    (α : ι) :
    randomInitExpectedResamplingCount P α ≤
      ⨆ D : ℕ, (mtWeight P p D α : ℝ≥0∞) := by
  rw [← tsum_witnessFamilyWeight_eq_iSup_mtWeight P p α]
  exact randomInitExpectedResamplingCount_le_tsum_familyWeight P hbad p hp α

/-- The probabilistic expected count is bounded by the algebraic MT
    budget, under the same self-consistency conditions as Convergence. -/
theorem randomInitExpectedResamplingCount_le [Fintype V]
    (P : MTProcess S ι) (hbad : ∀ i, MeasurableSet (P.bad i))
    (p x : ι → ℝ≥0)
    (hp : ∀ i, Measure.pi (fun v => S.measure v) (P.bad i) ≤ (p i : ℝ≥0∞))
    (h_dom : ∀ α, p α ≤ x α)
    (h_self : ∀ α, p α * ∏ β ∈ plusNeighbors P α, (1 + x β) ≤ x α)
    (α : ι) : randomInitExpectedResamplingCount P α ≤ (x α : ℝ≥0∞) := by
  exact (randomInitExpectedResamplingCount_le_tsum_familyWeight P hbad p hp α).trans
    (tsum_witnessFamilyWeight_le P p x h_dom h_self α)

/-- Moser-Tardos expected stopped log length for random initialization.
    The probability bounds and MT budget conditions are explicit. -/
theorem randomInitETLog_le_sum [Fintype V]
    (P : MTProcess S ι) (hbad : ∀ i, MeasurableSet (P.bad i))
    (p x : ι → ℝ≥0)
    (hp : ∀ i, Measure.pi (fun v => S.measure v) (P.bad i) ≤ (p i : ℝ≥0∞))
    (h_dom : ∀ α, p α ≤ x α)
    (h_self : ∀ α, p α * ∏ β ∈ plusNeighbors P α, (1 + x β) ≤ x α) :
    randomInitETLog P ≤ (↑(∑ α : ι, x α) : ℝ≥0∞) := by
  calc
    randomInitETLog P = ∑ α : ι, randomInitExpectedResamplingCount P α :=
      randomInitETLog_eq_sum_expectedResamplingCount P hbad
    _ ≤ ∑ α : ι, (x α : ℝ≥0∞) :=
      Finset.sum_le_sum (fun α _ =>
        randomInitExpectedResamplingCount_le P hbad p x hp h_dom h_self α)
    _ = (↑(∑ α : ι, x α) : ℝ≥0∞) := by
      rw [ENNReal.ofNNReal_finsetSum]

/-- Finite MT budgets imply a finite expected stopped log length. -/
theorem randomInitETLog_lt_top [Fintype V]
    (P : MTProcess S ι) (hbad : ∀ i, MeasurableSet (P.bad i))
    (p x : ι → ℝ≥0)
    (hp : ∀ i, Measure.pi (fun v => S.measure v) (P.bad i) ≤ (p i : ℝ≥0∞))
    (h_dom : ∀ α, p α ≤ x α)
    (h_self : ∀ α, p α * ∏ β ∈ plusNeighbors P α, (1 + x β) ≤ x α) :
    randomInitETLog P < ⊤ := by
  exact lt_of_le_of_lt (randomInitETLog_le_sum P hbad p x hp h_dom h_self)
    ENNReal.coe_lt_top

-- -------------------------------------------------------------------
-- Verification
-- -------------------------------------------------------------------

#check @witnessOccurrence_eq_empty_of_not_mem_family
#check @logMeasure_witnessOccurrence_le_familyWeight
#check @randomInitExpectedResamplingCount_le_tsum_familyWeight
#check @randomInitExpectedResamplingCount_le_iSup_mtWeight
#check @randomInitExpectedResamplingCount_le
#check @randomInitETLog_le_sum
#check @randomInitETLog_lt_top
