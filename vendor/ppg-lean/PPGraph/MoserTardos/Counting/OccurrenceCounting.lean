/-
  PPGraphMoserTardosOccurrenceCounting.lean

  Step 3: reindex the stopped count by canonical witness shapes.

  The map from a resampling time to its witness depends on the sampled
  log. We therefore establish the identity separately for each log,
  using injectivity on active times with the same event label. Only
  after that pointwise counting argument do we integrate and apply
  Tonelli to the measurable occurrence events.

  All identities are in ENNReal, without a termination or finiteness
  assumption. Trees which never occur contribute zero.
-/

module

public import PPGraph.MoserTardos.Witness.Occurrence

@[expose] public section

open MeasureTheory Classical
open scoped ENNReal

variable {V : Type} [DecidableEq V] {S : VarSpaces V} {ι : Type}
    [Fintype ι] [DecidableEq ι] [Nonempty ι]

/-- Count each active resampling of `α` by its distinct canonical
    witness. This is a pointwise reindexing, with the log held fixed. -/
theorem randomInitResamplingCount_eq_tsum_witnessOccurrence (P : MTProcess S ι)
    (ω : LogSpace S) (α : ι) :
    randomInitResamplingCount P ω α = ∑' U : WTree ι,
      (witnessOccurrence P α U).indicator (fun _ => (1 : ℝ≥0∞)) ω := by
  classical
  let f : WTree ι → ℝ≥0∞ := fun U =>
    (witnessOccurrence P α U).indicator (fun _ => 1) ω
  let g : ℕ → ℝ≥0∞ := fun s =>
    (randomInitResamplingEvent P α s).indicator (fun _ => 1) ω
  have hg (s : ℕ) : g s ≠ 0 ↔ ω ∈ randomInitResamplingEvent P α s := by
    by_cases hs : ω ∈ randomInitResamplingEvent P α s <;>
      simp [g, Set.indicator_apply, hs]
  let i : Function.support g → WTree ι := fun s => randomInitWitness P ω s.val
  have hi : Function.Injective i := by
    intro s t heq
    have hs := (hg s.val).mp s.property
    have ht := (hg t.val).mp t.property
    have hlabel : realC P (initialStateFromLog ω) ω s.val =
        realC P (initialStateFromLog ω) ω t.val := hs.2.trans ht.2.symm
    change resamplingWitness P (initialStateFromLog ω) ω s.val =
      resamplingWitness P (initialStateFromLog ω) ω t.val at heq
    apply Subtype.ext
    rcases lt_trichotomy s.val t.val with hst | hst | hts
    · exact False.elim ((resamplingWitness_ne_of_lt P (initialStateFromLog ω)
        ω s.val t.val hst hlabel) heq)
    · exact hst
    · exact False.elim ((resamplingWitness_ne_of_lt P (initialStateFromLog ω)
        ω t.val s.val hts hlabel.symm) heq.symm)
  have hf : Function.support f ⊆ Set.range i := by
    intro U hU
    have hocc : ω ∈ witnessOccurrence P α U := by
      by_contra hnot
      exact hU (by simp [f, Set.indicator_apply, hnot])
    rcases hocc with ⟨s, hs, heq⟩
    exact ⟨⟨s, (hg s).mpr hs⟩, heq⟩
  have hfg (s : Function.support g) : f (i s) = g s := by
    have hs := (hg s.val).mp s.property
    have hocc : ω ∈ witnessOccurrence P α (i s) := ⟨s.val, hs, rfl⟩
    simp [f, g, Set.indicator_apply, hocc, hs]
  calc
    randomInitResamplingCount P ω α = ∑' s : ℕ, g s :=
      randomInitResamplingCount_eq_tsum_indicator P ω α
    _ = ∑' U : WTree ι, f U :=
      (tsum_eq_tsum_of_ne_zero_bij i hi hf hfg).symm

/-- Tonelli turns pointwise witness counting into the sum of the
    probabilities that individual canonical shapes occur. -/
theorem randomInitExpectedResamplingCount_eq_tsum_witnessOccurrence
    (P : MTProcess S ι) (hbad : ∀ i, MeasurableSet (P.bad i)) (α : ι) :
    randomInitExpectedResamplingCount P α =
      ∑' U : WTree ι, logMeasure S (witnessOccurrence P α U) := by
  unfold randomInitExpectedResamplingCount
  simp_rw [randomInitResamplingCount_eq_tsum_witnessOccurrence]
  rw [lintegral_tsum (fun U => (measurable_const.indicator
    (measurableSet_witnessOccurrence P hbad α U)).aemeasurable)]
  apply tsum_congr
  intro U
  rw [lintegral_indicator_const (measurableSet_witnessOccurrence P hbad α U) 1,
    one_mul]

/-- The slot-zero expected log length decomposes first by event label,
    then by the distinct canonical witness shapes that occur. -/
theorem randomInitETLog_eq_sum_tsum_witnessOccurrence (P : MTProcess S ι)
    (hbad : ∀ i, MeasurableSet (P.bad i)) :
    randomInitETLog P = ∑ α : ι,
      ∑' U : WTree ι, logMeasure S (witnessOccurrence P α U) := by
  rw [randomInitETLog_eq_sum_expectedResamplingCount P hbad]
  apply Finset.sum_congr rfl
  intro α _
  exact randomInitExpectedResamplingCount_eq_tsum_witnessOccurrence P hbad α

-- -------------------------------------------------------------------
-- Verification
-- -------------------------------------------------------------------

#check @randomInitResamplingCount_eq_tsum_witnessOccurrence
#check @randomInitExpectedResamplingCount_eq_tsum_witnessOccurrence
#check @randomInitETLog_eq_sum_tsum_witnessOccurrence
