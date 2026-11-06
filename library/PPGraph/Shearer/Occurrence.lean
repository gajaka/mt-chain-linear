/-
  PPGraphShearerOccurrence.lean

  Stable-layer occurrences in the existing slot-zero-initialized MT run.
  The sequence at a fixed time is measurable because it depends on a
  finite label history. Counting is performed separately for each log,
  before integration and without a termination assumption.
-/

module

public import PPGraph.Shearer.LayerProfile
public import PPGraph.MoserTardos.Witness.Occurrence

@[expose] public section

set_option autoImplicit false

open MeasureTheory Classical
open scoped ENNReal

namespace Shearer

variable {V : Type} [DecidableEq V] {S : VarSpaces V} {ι : Type}
    [Fintype ι] [DecidableEq ι] [Nonempty ι]

/-- The depth layers of the real witness at candidate resampling time `s`.
Activity of this time is imposed separately by `sequenceOccurrence`. -/
noncomputable def randomInitSequence (P : MTProcess S ι) (ω : LogSpace S)
    (s : ℕ) : List (Finset ι) :=
  treeLayers (τC P (shiftedC P (initialStateFromLog ω) ω) (s + 1))

/-- At fixed time the sequence depends only on the finite selected-label history. -/
theorem measurable_randomInitSequence (P : MTProcess S ι)
    (hbad : ∀ i, MeasurableSet (P.bad i)) (s : ℕ) :
    letI : MeasurableSpace (List (Finset ι)) := ⊤
    Measurable (fun ω : LogSpace S => randomInitSequence P ω s) := by
  let : MeasurableSpace ι := ⊤
  let : MeasurableSpace (List (Finset ι)) := ⊤
  let history : LogSpace S → (Fin (s + 2) → ι) :=
    fun ω k => shiftedC P (initialStateFromLog ω) ω k.val
  have hhistory : Measurable history := by
    apply Measurable.of_eval
    intro k
    exact measurable_realC_of_measurable_init P hbad initialStateFromLog
      measurable_initialStateFromLog (k.val - 1)
  let decode : (Fin (s + 2) → ι) → List (Finset ι) := fun a =>
    treeLayers (τC P (fun k => a ⟨min k (s + 1), by omega⟩) (s + 1))
  have hdecode : Measurable decode := measurable_of_countable decode
  have heq : (fun ω : LogSpace S => randomInitSequence P ω s) =
      decode ∘ history := by
    funext ω
    change treeLayers (τC P (shiftedC P (initialStateFromLog ω) ω) (s + 1)) =
      treeLayers (τC P
        (fun k => shiftedC P (initialStateFromLog ω) ω (min k (s + 1))) (s + 1))
    apply congrArg treeLayers
    apply τC_congr_of_eq_upto
    intro i hi
    rw [min_eq_left hi]
  rw [heq]
  exact hdecode.comp hhistory

theorem measurableSet_randomInitSequence_eq (P : MTProcess S ι)
    (hbad : ∀ i, MeasurableSet (P.bad i)) (s : ℕ) (L : List (Finset ι)) :
    MeasurableSet {ω : LogSpace S | randomInitSequence P ω s = L} := by
  let : MeasurableSpace (List (Finset ι)) := ⊤
  exact (measurable_randomInitSequence P hbad s) (measurableSet_singleton L)

/-- A stable sequence occurs at an active resampling of its root event. -/
def sequenceOccurrence (P : MTProcess S ι) (α : ι) (L : List (Finset ι)) :
    Set (LogSpace S) :=
  {ω | ∃ s : ℕ, ω ∈ randomInitResamplingEvent P α s ∧ randomInitSequence P ω s = L}

theorem sequenceOccurrence_eq_iUnion (P : MTProcess S ι) (α : ι)
    (L : List (Finset ι)) :
    sequenceOccurrence P α L = ⋃ s : ℕ,
      (randomInitResamplingEvent P α s ∩
        {ω : LogSpace S | randomInitSequence P ω s = L}) := by
  ext ω
  simp only [sequenceOccurrence, Set.mem_ofPred_eq, Set.mem_iUnion, Set.mem_inter_iff]

theorem measurableSet_sequenceOccurrence (P : MTProcess S ι)
    (hbad : ∀ i, MeasurableSet (P.bad i)) (α : ι) (L : List (Finset ι)) :
    MeasurableSet (sequenceOccurrence P α L) := by
  rw [sequenceOccurrence_eq_iUnion]
  exact MeasurableSet.iUnion (fun s =>
    (measurableSet_randomInitResamplingEvent P hbad α s).inter
      (measurableSet_randomInitSequence_eq P hbad s L))

/-- Every occurring sequence belongs to the proper stable family for its label. -/
theorem sequenceOccurrence_nonempty_mem_properFamily (P : MTProcess S ι)
    (α : ι) (L : List (Finset ι)) (hL : (sequenceOccurrence P α L).Nonempty) :
    L ∈ properFamily (dependencyGraph P.footprint) Finset.univ {α} := by
  obtain ⟨ω, s, hs, rfl⟩ := hL
  have h := treeLayers_mem_properFamily P (shiftedC P (initialStateFromLog ω) ω) (s + 1)
  simpa only [randomInitSequence, shiftedC_succ, hs.2] using h

theorem sequenceOccurrence_eq_empty_of_not_mem_properFamily (P : MTProcess S ι)
    (α : ι) (L : List (Finset ι))
    (hL : L ∉ properFamily (dependencyGraph P.footprint) Finset.univ {α}) :
    sequenceOccurrence P α L = ∅ := by
  apply Set.eq_empty_iff_forall_notMem.mpr
  intro ω hω
  exact hL (sequenceOccurrence_nonempty_mem_properFamily P α L ⟨ω, hω⟩)

omit [Fintype ι] [Nonempty ι] in
/-- Repeated occurrences of the same label have different total label counts,
so their layer sequences differ even though general trees need not be recovered
from their layers. -/
theorem τC_treeLayers_ne_of_lt (P : MTProcess S ι) (C : ℕ → ι) (s t : ℕ)
    (hs : 0 < s) (ht : 0 < t) (hst : s < t) (hlabel : C s = C t) :
    treeLayers (τC P C s) ≠ treeLayers (τC P C t) := by
  intro heq
  apply τC_countLabel_ne_of_lt P C s t hs ht hst hlabel
  have h := countLabel_eq_of_treeLayers_eq P (τC P C s) (τC P C t)
    (τBuild_sameDepthIndependent P C s (s - 1))
    (τBuild_sameDepthIndependent P C t (t - 1)) heq (C s)
  simpa only [hlabel] using h

theorem randomInitSequence_ne_of_lt (P : MTProcess S ι) (ω : LogSpace S)
    (s t : ℕ) (hst : s < t)
    (hlabel : realC P (initialStateFromLog ω) ω s =
      realC P (initialStateFromLog ω) ω t) :
    randomInitSequence P ω s ≠ randomInitSequence P ω t := by
  apply τC_treeLayers_ne_of_lt P (shiftedC P (initialStateFromLog ω) ω)
    (s + 1) (t + 1) (by omega) (by omega) (by omega)
  simpa only [shiftedC_succ] using hlabel

/-- Each active resampling of a fixed event contributes exactly one distinct
sequence. The identity is pointwise and permits infinitely many resamplings. -/
theorem randomInitResamplingCount_eq_tsum_sequenceOccurrence (P : MTProcess S ι)
    (ω : LogSpace S) (α : ι) :
    randomInitResamplingCount P ω α = ∑' L : List (Finset ι),
      (sequenceOccurrence P α L).indicator (fun _ => (1 : ℝ≥0∞)) ω := by
  let f : List (Finset ι) → ℝ≥0∞ := fun L =>
    (sequenceOccurrence P α L).indicator (fun _ => 1) ω
  let g : ℕ → ℝ≥0∞ := fun s =>
    (randomInitResamplingEvent P α s).indicator (fun _ => 1) ω
  have hg (s : ℕ) : g s ≠ 0 ↔ ω ∈ randomInitResamplingEvent P α s := by
    by_cases hs : ω ∈ randomInitResamplingEvent P α s <;>
      simp [g, Set.indicator_apply, hs]
  let i : Function.support g → List (Finset ι) :=
    fun s => randomInitSequence P ω s.val
  have hi : Function.Injective i := by
    intro s t heq
    have hs := (hg s.val).mp s.property
    have ht := (hg t.val).mp t.property
    have hlabel : realC P (initialStateFromLog ω) ω s.val =
        realC P (initialStateFromLog ω) ω t.val := hs.2.trans ht.2.symm
    apply Subtype.ext
    rcases lt_trichotomy s.val t.val with hst | hst | hts
    · exact False.elim ((randomInitSequence_ne_of_lt P ω s.val t.val hst hlabel) heq)
    · exact hst
    · exact False.elim ((randomInitSequence_ne_of_lt P ω t.val s.val hts hlabel.symm) heq.symm)
  have hf : Function.support f ⊆ Set.range i := by
    intro L hL
    have hocc : ω ∈ sequenceOccurrence P α L := by
      by_contra hnot
      exact hL (by simp [f, Set.indicator_apply, hnot])
    obtain ⟨s, hs, heq⟩ := hocc
    exact ⟨⟨s, (hg s).mpr hs⟩, heq⟩
  have hfg (s : Function.support g) : f (i s) = g s := by
    have hs := (hg s.val).mp s.property
    have hocc : ω ∈ sequenceOccurrence P α (i s) := ⟨s.val, hs, rfl⟩
    simp [f, g, Set.indicator_apply, hocc, hs]
  calc
    randomInitResamplingCount P ω α = ∑' s : ℕ, g s :=
      randomInitResamplingCount_eq_tsum_indicator P ω α
    _ = ∑' L : List (Finset ι), f L :=
      (tsum_eq_tsum_of_ne_zero_bij i hi hf hfg).symm

/-- Tonelli converts the pointwise counting identity into occurrence probabilities. -/
theorem randomInitExpectedResamplingCount_eq_tsum_sequenceOccurrence
    (P : MTProcess S ι) (hbad : ∀ i, MeasurableSet (P.bad i)) (α : ι) :
    randomInitExpectedResamplingCount P α =
      ∑' L : List (Finset ι), logMeasure S (sequenceOccurrence P α L) := by
  unfold randomInitExpectedResamplingCount
  simp_rw [randomInitResamplingCount_eq_tsum_sequenceOccurrence]
  rw [lintegral_tsum (fun L => (measurable_const.indicator
    (measurableSet_sequenceOccurrence P hbad α L)).aemeasurable)]
  apply tsum_congr
  intro L
  rw [lintegral_indicator_const (measurableSet_sequenceOccurrence P hbad α L) 1,
    one_mul]

end Shearer

#check @Shearer.measurable_randomInitSequence
#check @Shearer.measurableSet_randomInitSequence_eq
#check @Shearer.sequenceOccurrence_eq_iUnion
#check @Shearer.measurableSet_sequenceOccurrence
#check @Shearer.sequenceOccurrence_nonempty_mem_properFamily
#check @Shearer.sequenceOccurrence_eq_empty_of_not_mem_properFamily
#check @Shearer.τC_treeLayers_ne_of_lt
#check @Shearer.randomInitSequence_ne_of_lt
#check @Shearer.randomInitResamplingCount_eq_tsum_sequenceOccurrence
#check @Shearer.randomInitExpectedResamplingCount_eq_tsum_sequenceOccurrence
