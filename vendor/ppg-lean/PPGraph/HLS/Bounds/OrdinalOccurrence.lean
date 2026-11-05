/- Count resamplings by the ordinal occurrence of their event, without termination. -/
module

public import PPGraph.HLS.DAG.RealDAGCounts
public import PPGraph.MoserTardos.Witness.Occurrence

@[expose] public section

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option backward.isDefEq.respectTransparency false

open Classical MeasureTheory
open scoped ENNReal

namespace HLS.WitnessDAG

variable {V : Type} [DecidableEq V] {S : VarSpaces V}
  {ι : Type} [Fintype ι] [DecidableEq ι] [Nonempty ι]

theorem earlierLabelCount_congr (C E : ℕ → ι) (t : ℕ)
    (h : ∀ s ≤ t, C s = E s) : earlierLabelCount C t = earlierLabelCount E t := by
  unfold earlierLabelCount
  congr 1
  apply Finset.filter_congr
  intro s hs
  rw [h s (Finset.mem_range.mp hs).le, h t le_rfl]

theorem measurable_earlierLabelCount (P : MTProcess S ι)
    (hbad : ∀ i, MeasurableSet (P.bad i)) (t : ℕ) :
    Measurable (fun ω : LogSpace S => earlierLabelCount (realSchedule P ω) t) := by
  let : MeasurableSpace ι := ⊤
  let history : LogSpace S → (Fin (t + 1) → ι) := fun ω k => realSchedule P ω k.val
  have hhistory : Measurable history := Measurable.of_eval (fun k =>
    measurable_realC_of_measurable_init P hbad initialStateFromLog measurable_initialStateFromLog k.val)
  let decode : (Fin (t + 1) → ι) → ℕ := fun a =>
    earlierLabelCount (fun k => a ⟨min k t, by omega⟩) t
  have hdecode : Measurable decode := measurable_of_countable decode
  have heq : (fun ω : LogSpace S => earlierLabelCount (realSchedule P ω) t) = decode ∘ history := by
    funext ω
    apply earlierLabelCount_congr
    intro s hs
    change realSchedule P ω s = realSchedule P ω (min s t)
    rw [min_eq_left hs]
  rw [heq]
  exact hdecode.comp hhistory

def ordinalOccurrence (P : MTProcess S ι) (α : ι) (r : ℕ) : Set (LogSpace S) :=
  {ω | ∃ t : ℕ, ω ∈ randomInitResamplingEvent P α t ∧ earlierLabelCount (realSchedule P ω) t = r}

theorem ordinalOccurrence_eq_iUnion (P : MTProcess S ι) (α : ι) (r : ℕ) :
    ordinalOccurrence P α r = ⋃ t : ℕ, randomInitResamplingEvent P α t ∩
      {ω : LogSpace S | earlierLabelCount (realSchedule P ω) t = r} := by
  ext ω
  simp only [ordinalOccurrence, Set.mem_ofPred_eq, Set.mem_iUnion, Set.mem_inter_iff]

theorem measurableSet_ordinalOccurrence (P : MTProcess S ι)
    (hbad : ∀ i, MeasurableSet (P.bad i)) (α : ι) (r : ℕ) :
    MeasurableSet (ordinalOccurrence P α r) := by
  rw [ordinalOccurrence_eq_iUnion]
  exact MeasurableSet.iUnion (fun t => (measurableSet_randomInitResamplingEvent P hbad α t).inter
    ((measurable_earlierLabelCount P hbad t) (measurableSet_singleton r)))

theorem randomInitResamplingCount_eq_tsum_ordinalOccurrence (P : MTProcess S ι)
    (ω : LogSpace S) (α : ι) :
    randomInitResamplingCount P ω α = ∑' r : ℕ,
      (ordinalOccurrence P α r).indicator (fun _ => (1 : ℝ≥0∞)) ω := by
  let f : ℕ → ℝ≥0∞ := fun r => (ordinalOccurrence P α r).indicator (fun _ => 1) ω
  let g : ℕ → ℝ≥0∞ := fun t => (randomInitResamplingEvent P α t).indicator (fun _ => 1) ω
  have hg (t : ℕ) : g t ≠ 0 ↔ ω ∈ randomInitResamplingEvent P α t := by
    by_cases ht : ω ∈ randomInitResamplingEvent P α t <;> simp [g, Set.indicator_apply, ht]
  let i : Function.support g → ℕ := fun t => earlierLabelCount (realSchedule P ω) t.val
  have hi : Function.Injective i := by
    intro s t heq
    have hs := (hg s.val).mp s.property
    have ht := (hg t.val).mp t.property
    have hl : realSchedule P ω s.val = realSchedule P ω t.val := hs.2.trans ht.2.symm
    apply Subtype.ext
    rcases lt_trichotomy s.val t.val with hst | hst | hts
    · exact False.elim ((Nat.ne_of_lt (earlierLabelCount_lt _ s.val t.val hst hl)) heq)
    · exact hst
    · exact False.elim ((Nat.ne_of_lt (earlierLabelCount_lt _ t.val s.val hts hl.symm)) heq.symm)
  have hf : Function.support f ⊆ Set.range i := by
    intro r hr
    have hocc : ω ∈ ordinalOccurrence P α r := by
      by_contra hn
      exact hr (by simp [f, Set.indicator_apply, hn])
    obtain ⟨t, ht, heq⟩ := hocc
    exact ⟨⟨t, (hg t).mpr ht⟩, heq⟩
  have hfg (t : Function.support g) : f (i t) = g t := by
    have ht := (hg t.val).mp t.property
    have hocc : ω ∈ ordinalOccurrence P α (i t) := ⟨t.val, ht, rfl⟩
    simp [f, g, Set.indicator_apply, hocc, ht]
  calc
    randomInitResamplingCount P ω α = ∑' t : ℕ, g t := randomInitResamplingCount_eq_tsum_indicator P ω α
    _ = ∑' r : ℕ, f r := (tsum_eq_tsum_of_ne_zero_bij i hi hf hfg).symm

theorem randomInitExpectedResamplingCount_eq_tsum_ordinalOccurrence
    (P : MTProcess S ι) (hbad : ∀ i, MeasurableSet (P.bad i)) (α : ι) :
    randomInitExpectedResamplingCount P α = ∑' r : ℕ, logMeasure S (ordinalOccurrence P α r) := by
  unfold randomInitExpectedResamplingCount
  simp_rw [randomInitResamplingCount_eq_tsum_ordinalOccurrence]
  rw [lintegral_tsum (fun r => (measurable_const.indicator
    (measurableSet_ordinalOccurrence P hbad α r)).aemeasurable)]
  apply tsum_congr
  intro r
  rw [lintegral_indicator_const (measurableSet_ordinalOccurrence P hbad α r) 1, one_mul]

end HLS.WitnessDAG

#check @HLS.WitnessDAG.earlierLabelCount_congr
#check @HLS.WitnessDAG.measurable_earlierLabelCount
#check @HLS.WitnessDAG.ordinalOccurrence_eq_iUnion
#check @HLS.WitnessDAG.measurableSet_ordinalOccurrence
#check @HLS.WitnessDAG.randomInitResamplingCount_eq_tsum_ordinalOccurrence
#check @HLS.WitnessDAG.randomInitExpectedResamplingCount_eq_tsum_ordinalOccurrence
