/- Stopped-log counting and termination for arbitrary admissible schedules.
   All count and expectation identities are proved before finiteness. -/
module

public import PPGraph.Integration.Policy.HLSDAG
public import PPGraph.HLS.Probability.RootUnion

@[expose] public section

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option backward.isDefEq.respectTransparency false

open Classical MeasureTheory HLS.WitnessDAG
open scoped ENNReal

namespace MTPolicy

variable {V : Type} [DecidableEq V] {S : VarSpaces V}
  {ι : Type} [Fintype ι] [DecidableEq ι] [Nonempty ι]

def resamplingEvent (P : MTProcess S ι) (σ : Schedule P) (α : ι) (t : ℕ) : Set (LogSpace S) :=
  {ω | Running P (σ.select ω) ω (t + 1) ∧ σ.select ω t = α}

theorem measurableSet_resamplingEvent (P : MTProcess S ι) (σ : Schedule P)
    (hbad : ∀ i, MeasurableSet (P.bad i)) (α : ι) (t : ℕ) :
    MeasurableSet (resamplingEvent P σ α t) := by
  let : MeasurableSpace ι := ⊤
  exact (measurableSet_running P σ hbad (t + 1)).inter
    ((σ.measurable_select t) (measurableSet_singleton α))

noncomputable def count (P : MTProcess S ι) (σ : Schedule P)
    (ω : LogSpace S) (α : ι) : ℝ≥0∞ :=
  ∑' t : ℕ, (resamplingEvent P σ α t).indicator (fun _ => 1) ω

noncomputable def expectedCount (P : MTProcess S ι) (σ : Schedule P) (α : ι) : ℝ≥0∞ :=
  ∫⁻ ω, count P σ ω α ∂logMeasure S

theorem measurable_count (P : MTProcess S ι) (σ : Schedule P)
    (hbad : ∀ i, MeasurableSet (P.bad i)) (α : ι) :
    Measurable (fun ω => count P σ ω α) := by
  apply Measurable.tsum
  intro t
  exact measurable_const.indicator (measurableSet_resamplingEvent P σ hbad α t)

theorem measurable_earlierLabelCount (P : MTProcess S ι) (σ : Schedule P)
    (_hbad : ∀ i, MeasurableSet (P.bad i)) (t : ℕ) :
    Measurable (fun ω : LogSpace S => earlierLabelCount (σ.select ω) t) := by
  let : MeasurableSpace ι := ⊤
  let history : LogSpace S → (Fin (t + 1) → ι) := fun ω k => σ.select ω k.val
  have hhistory : Measurable history := Measurable.of_eval (fun k =>
    σ.measurable_select k.val)
  let decode : (Fin (t + 1) → ι) → ℕ := fun a =>
    earlierLabelCount (fun k => a ⟨min k t, by omega⟩) t
  have hdecode : Measurable decode := measurable_of_countable decode
  have heq : (fun ω : LogSpace S => earlierLabelCount (σ.select ω) t) = decode ∘ history := by
    funext ω
    apply HLS.WitnessDAG.earlierLabelCount_congr
    intro s hs
    change σ.select ω s = σ.select ω (min s t)
    rw [min_eq_left hs]
  rw [heq]
  exact hdecode.comp hhistory

def ordinalOccurrence (P : MTProcess S ι) (σ : Schedule P) (α : ι) (r : ℕ) : Set (LogSpace S) :=
  {ω | ∃ t : ℕ, ω ∈ resamplingEvent P σ α t ∧ earlierLabelCount (σ.select ω) t = r}

theorem ordinalOccurrence_eq_iUnion (P : MTProcess S ι) (σ : Schedule P) (α : ι) (r : ℕ) :
    ordinalOccurrence P σ α r = ⋃ t : ℕ, resamplingEvent P σ α t ∩
      {ω : LogSpace S | earlierLabelCount (σ.select ω) t = r} := by
  ext ω
  simp only [ordinalOccurrence, Set.mem_ofPred_eq, Set.mem_iUnion, Set.mem_inter_iff]

theorem measurableSet_ordinalOccurrence (P : MTProcess S ι) (σ : Schedule P)
    (hbad : ∀ i, MeasurableSet (P.bad i)) (α : ι) (r : ℕ) :
    MeasurableSet (ordinalOccurrence P σ α r) := by
  rw [ordinalOccurrence_eq_iUnion]
  exact MeasurableSet.iUnion (fun t => (measurableSet_resamplingEvent P σ hbad α t).inter
    ((measurable_earlierLabelCount P σ hbad t) (measurableSet_singleton r)))

theorem count_eq_tsum_ordinalOccurrence (P : MTProcess S ι) (σ : Schedule P)
    (ω : LogSpace S) (α : ι) :
    count P σ ω α = ∑' r : ℕ,
      (ordinalOccurrence P σ α r).indicator (fun _ => (1 : ℝ≥0∞)) ω := by
  let f : ℕ → ℝ≥0∞ := fun r => (ordinalOccurrence P σ α r).indicator (fun _ => 1) ω
  let g : ℕ → ℝ≥0∞ := fun t => (resamplingEvent P σ α t).indicator (fun _ => 1) ω
  have hg (t : ℕ) : g t ≠ 0 ↔ ω ∈ resamplingEvent P σ α t := by
    by_cases ht : ω ∈ resamplingEvent P σ α t <;> simp [g, Set.indicator_apply, ht]
  let i : Function.support g → ℕ := fun t => earlierLabelCount (σ.select ω) t.val
  have hi : Function.Injective i := by
    intro s t heq
    have hs := (hg s.val).mp s.property
    have ht := (hg t.val).mp t.property
    have hl : σ.select ω s.val = σ.select ω t.val := hs.2.trans ht.2.symm
    apply Subtype.ext
    rcases lt_trichotomy s.val t.val with hst | hst | hts
    · exact False.elim ((Nat.ne_of_lt (earlierLabelCount_lt _ s.val t.val hst hl)) heq)
    · exact hst
    · exact False.elim ((Nat.ne_of_lt (earlierLabelCount_lt _ t.val s.val hts hl.symm)) heq.symm)
  have hf : Function.support f ⊆ Set.range i := by
    intro r hr
    have hocc : ω ∈ ordinalOccurrence P σ α r := by
      by_contra hn
      exact hr (by simp [f, Set.indicator_apply, hn])
    obtain ⟨t, ht, heq⟩ := hocc
    exact ⟨⟨t, (hg t).mpr ht⟩, heq⟩
  have hfg (t : Function.support g) : f (i t) = g t := by
    have ht := (hg t.val).mp t.property
    have hocc : ω ∈ ordinalOccurrence P σ α (i t) := ⟨t.val, ht, rfl⟩
    simp [f, g, Set.indicator_apply, hocc, ht]
  calc
    count P σ ω α = ∑' t : ℕ, g t := rfl
    _ = ∑' r : ℕ, f r := (tsum_eq_tsum_of_ne_zero_bij i hi hf hfg).symm

theorem expectedCount_eq_tsum_ordinalOccurrence
    (P : MTProcess S ι) (σ : Schedule P) (hbad : ∀ i, MeasurableSet (P.bad i)) (α : ι) :
    expectedCount P σ α = ∑' r : ℕ, logMeasure S (ordinalOccurrence P σ α r) := by
  unfold expectedCount
  simp_rw [count_eq_tsum_ordinalOccurrence]
  rw [lintegral_tsum (fun r => (measurable_const.indicator
    (measurableSet_ordinalOccurrence P σ hbad α r)).aemeasurable)]
  apply tsum_congr
  intro r
  rw [lintegral_indicator_const (measurableSet_ordinalOccurrence P σ hbad α r) 1, one_mul]

theorem ordinalOccurrence_subset_rootUnion (P : MTProcess S ι) (σ : Schedule P) (α : ι) (r : ℕ) :
    ordinalOccurrence P σ α r ⊆ rootUnion P α r := by
  rintro ω ⟨t, ht, hr⟩
  have hroot : DAG.realRoot P (σ.select ω) ω t = (α, r) := Prod.ext ht.2 hr
  have hD : RootedCanonical (Shearer.dependencyGraph P.footprint) (α, r)
      (DAG.realDAG P (σ.select ω) ω t) := by
    refine ⟨DAG.realDAG_valid P (σ.select ω) ω t,
      DAG.realDAG_canonical P (σ.select ω) ω t, ?_, ?_⟩
    · simpa only [hroot] using DAG.realRoot_mem P (σ.select ω) ω t
    · intro u hu
      simpa only [hroot] using DAG.realDAG_reach_root P (σ.select ω) ω t u hu
  exact Set.mem_iUnion.mpr ⟨⟨DAG.realDAG P (σ.select ω) ω t, hD⟩,
    DAG.realDAG_tableCheck_of_running P (σ.select ω) ω t ht.1⟩

theorem tLog_eq_sum_count (P : MTProcess S ι) (σ : Schedule P) (ω : LogSpace S) :
    tLog P (σ.select ω) ω = ∑ α : ι, count P σ ω α := by
  have hstep (t : ℕ) : (if Running P (σ.select ω) ω (t + 1) then (1 : ℝ≥0∞) else 0) =
      ∑ α : ι, (resamplingEvent P σ α t).indicator (fun _ => 1) ω := by
    by_cases h : Running P (σ.select ω) ω (t + 1) <;>
      simp [resamplingEvent, Set.indicator_apply, h]
  calc
    tLog P (σ.select ω) ω = ∑' t : ℕ, ∑' α : ι,
        (resamplingEvent P σ α t).indicator (fun _ => (1 : ℝ≥0∞)) ω := by
      unfold tLog
      apply tsum_congr
      intro t
      rw [tsum_fintype]
      exact hstep t
    _ = ∑' α : ι, ∑' t : ℕ,
        (resamplingEvent P σ α t).indicator (fun _ => (1 : ℝ≥0∞)) ω := ENNReal.tsum_comm
    _ = _ := by simp only [count, tsum_fintype]

theorem expectedWork_eq_sum_expectedCount (P : MTProcess S ι) (σ : Schedule P)
    (hbad : ∀ i, MeasurableSet (P.bad i)) :
    expectedWork P σ = ∑ α : ι, expectedCount P σ α := by
  unfold expectedWork expectedCount
  simp_rw [tLog_eq_sum_count]
  exact lintegral_finsetSum Finset.univ (fun α _ => measurable_count P σ hbad α)

theorem tLog_le_of_good (P : MTProcess S ι) (C : ℕ → ι) (ω : LogSpace S) (T : ℕ)
    (hgood : MTGood P (state P C ω T)) : tLog P C ω ≤ (T : ℝ≥0∞) := by
  have hstop : ∀ s, T ≤ s → ¬ Running P C ω (s + 1) := by
    intro s hs hrun
    exact hgood (C T) (hrun T (Nat.lt_succ_of_le hs))
  have hzero : ∀ s ∉ Finset.range T,
      (if Running P C ω (s + 1) then (1 : ℝ≥0∞) else 0) = 0 := by
    intro s hs
    rw [ite_eq_right (hstop s (Nat.le_of_not_gt (by simpa only [Finset.mem_range] using hs)))]
  unfold tLog
  rw [tsum_eq_sum hzero]
  calc
    (∑ s ∈ Finset.range T, if Running P C ω (s + 1) then (1 : ℝ≥0∞) else 0) ≤
        ∑ _s ∈ Finset.range T, (1 : ℝ≥0∞) := by
      apply Finset.sum_le_sum
      intro s hs
      split_ifs <;> simp
    _ = _ := by simp

theorem tLog_lt_top_iff_exists_good (P : MTProcess S ι) (C : ℕ → ι) (ω : LogSpace S)
    (hC : Admissible P C ω) : tLog P C ω < ⊤ ↔ ∃ T : ℕ, MTGood P (state P C ω T) := by
  constructor
  · intro hf
    by_contra hn
    have hrun : ∀ n, Running P C ω n := fun n t ht => hC t (fun h => hn ⟨t, h⟩)
    have hinf : tLog P C ω = ⊤ := by
      unfold tLog
      simp_rw [ite_eq_left (hrun _)]
      exact ENNReal.tsum_const_eq_top_of_ne_zero one_ne_zero
    exact hf.ne hinf
  · rintro ⟨T, hT⟩
    exact (tLog_le_of_good P C ω T hT).trans_lt (by simp)

theorem ae_exists_good_of_expectedWork_lt_top (P : MTProcess S ι) (σ : Schedule P)
    (hbad : ∀ i, MeasurableSet (P.bad i)) (hf : expectedWork P σ < ⊤) :
    ∀ᵐ ω ∂logMeasure S, ∃ T : ℕ, MTGood P (state P (σ.select ω) ω T) := by
  have hae := MeasureTheory.ae_lt_top (measurable_tLog P σ hbad) hf.ne
  filter_upwards [hae] with ω hω
  exact (tLog_lt_top_iff_exists_good P (σ.select ω) ω (σ.admissible ω)).mp hω

theorem measure_termination_eq_one_of_expectedWork_lt_top (P : MTProcess S ι) (σ : Schedule P)
    (hbad : ∀ i, MeasurableSet (P.bad i)) (hf : expectedWork P σ < ⊤) :
    logMeasure S {ω | ∃ T : ℕ, MTGood P (state P (σ.select ω) ω T)} = 1 := by
  have heq : {ω | ∃ T : ℕ, MTGood P (state P (σ.select ω) ω T)} =
      {ω | tLog P (σ.select ω) ω < ⊤} := by
    ext ω
    exact (tLog_lt_top_iff_exists_good P (σ.select ω) ω (σ.admissible ω)).symm
  rw [heq]
  exact (mem_ae_iff_prob_eq_one
    (measurableSet_lt (measurable_tLog P σ hbad) measurable_const)).mp
      (MeasureTheory.ae_lt_top (measurable_tLog P σ hbad) hf.ne)

end MTPolicy

#check @MTPolicy.measurableSet_resamplingEvent
#check @MTPolicy.measurable_count
#check @MTPolicy.measurable_earlierLabelCount
#check @MTPolicy.ordinalOccurrence_eq_iUnion
#check @MTPolicy.measurableSet_ordinalOccurrence
#check @MTPolicy.count_eq_tsum_ordinalOccurrence
#check @MTPolicy.expectedCount_eq_tsum_ordinalOccurrence
#check @MTPolicy.ordinalOccurrence_subset_rootUnion
#check @MTPolicy.tLog_eq_sum_count
#check @MTPolicy.expectedWork_eq_sum_expectedCount
#check @MTPolicy.tLog_le_of_good
#check @MTPolicy.tLog_lt_top_iff_exists_good
#check @MTPolicy.ae_exists_good_of_expectedWork_lt_top
#check @MTPolicy.measure_termination_eq_one_of_expectedWork_lt_top
