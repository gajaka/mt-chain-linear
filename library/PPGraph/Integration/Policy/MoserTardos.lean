/-
  Moser--Tardos with an arbitrary measurable selection schedule.
  A schedule may depend on the complete previous history; no ordering
  of the event labels is prescribed. Admissibility means only that a
  non-good current assignment selects a violated event. It does not
  assume termination, an expectation bound, or witness consistency.

  The state is read from the independent resampling table using the
  number of previous resamplings of each variable. The successor theorem
  proves that this is precisely the usual resampling operation. Slot 0
  supplies the random initial assignment, as in HLS Algorithm 1.
  Source: https://arxiv.org/abs/2111.06527, Algorithm 1 and footnote 2.
-/
module

public import PPGraph.HLS.DAG.RealDAGCounts
public import PPGraph.MoserTardos.Bounds.Termination
public import PPGraph.MoserTardos.Counting.Counting

@[expose] public section

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option backward.isDefEq.respectTransparency false

open Classical MeasureTheory
open scoped ENNReal

namespace MTPolicy

variable {V : Type} [DecidableEq V] {S : VarSpaces V}
  {ι : Type} [Fintype ι] [DecidableEq ι] [Nonempty ι]

noncomputable def uses (P : MTProcess S ι) (C : ℕ → ι) (t : ℕ) (v : V) : ℕ :=
  ((Finset.range t).filter (fun s => v ∈ P.footprint (C s))).card

noncomputable def state (P : MTProcess S ι) (C : ℕ → ι)
    (ω : LogSpace S) (t : ℕ) : MTState S := readAt (uses P C t) ω

theorem uses_zero (P : MTProcess S ι) (C : ℕ → ι) (v : V) : uses P C 0 v = 0 := by
  simp [uses]

theorem uses_succ (P : MTProcess S ι) (C : ℕ → ι) (t : ℕ) (v : V) :
    uses P C (t + 1) v = uses P C t v + if v ∈ P.footprint (C t) then 1 else 0 := by
  simp only [uses, Finset.range_add_one, Finset.filter_insert]
  by_cases h : v ∈ P.footprint (C t)
  · simp [h, Finset.card_insert_of_notMem, Finset.mem_filter, Finset.mem_range]
  · simp [h]

theorem uses_le (P : MTProcess S ι) (C : ℕ → ι) (t : ℕ) (v : V) : uses P C t v ≤ t := by
  exact (Finset.card_le_card (Finset.filter_subset _ _)).trans_eq (Finset.card_range t)

theorem state_zero (P : MTProcess S ι) (C : ℕ → ι) (ω : LogSpace S) :
    state P C ω 0 = initialStateFromLog ω := by
  funext v
  change atIdx ω v (uses P C 0 v) = atIdx ω v 0
  exact congrArg (atIdx ω v) (uses_zero P C v)

theorem state_succ (P : MTProcess S ι) (C : ℕ → ι) (ω : LogSpace S) (t : ℕ) :
    state P C ω (t + 1) = resample (P.footprint (C t)) (state P C ω t)
      (drawFrom ω (fun v => uses P C t v + 1)) := by
  funext v
  change atIdx ω v (uses P C (t + 1) v) =
    if v ∈ P.footprint (C t) then atIdx ω v (uses P C t v + 1) else atIdx ω v (uses P C t v)
  rw [uses_succ]
  split_ifs <;> rfl

def Running (P : MTProcess S ι) (C : ℕ → ι) (ω : LogSpace S) (n : ℕ) : Prop :=
  ∀ t < n, state P C ω t ∈ P.bad (C t)

def Admissible (P : MTProcess S ι) (C : ℕ → ι) (ω : LogSpace S) : Prop :=
  ∀ t, ¬ MTGood P (state P C ω t) → state P C ω t ∈ P.bad (C t)

/-- Any measurable decision sequence, with a proof of the algorithm's
    local selection rule. There is no convergence field. -/
structure Schedule (P : MTProcess S ι) where
  select : LogSpace S → ℕ → ι
  measurable_select : ∀ t, letI : MeasurableSpace ι := ⊤
    Measurable (fun ω => select ω t)
  admissible : ∀ ω, Admissible P (select ω) ω

theorem uses_congr (P : MTProcess S ι) (C E : ℕ → ι) (t : ℕ) (v : V)
    (h : ∀ s < t, C s = E s) : uses P C t v = uses P E t v := by
  unfold uses
  congr 1
  apply Finset.filter_congr
  intro s hs
  rw [h s (Finset.mem_range.mp hs)]

theorem measurable_uses (P : MTProcess S ι) (σ : Schedule P) (t : ℕ) (v : V) :
    Measurable (fun ω => uses P (σ.select ω) t v) := by
  let : MeasurableSpace ι := ⊤
  let history : LogSpace S → (Fin (t + 1) → ι) := fun ω k => σ.select ω k.val
  have hh : Measurable history := Measurable.of_eval (fun k => σ.measurable_select k.val)
  let decode : (Fin (t + 1) → ι) → ℕ := fun a =>
    uses P (fun k => a ⟨min k t, by omega⟩) t v
  have hd : Measurable decode := measurable_of_countable decode
  have heq : (fun ω => uses P (σ.select ω) t v) = decode ∘ history := by
    funext ω
    apply uses_congr
    intro s hs
    change σ.select ω s = σ.select ω (min s t)
    rw [min_eq_left hs.le]
  rw [heq]
  exact hd.comp hh

theorem measurable_state (P : MTProcess S ι) (σ : Schedule P) (t : ℕ) :
    Measurable (fun ω => state P (σ.select ω) ω t) := by
  apply Measurable.of_eval
  intro v
  exact measurable_eval_bounded v t (fun ω => uses P (σ.select ω) t v)
    (measurable_uses P σ t v) (fun ω => uses_le P (σ.select ω) t v)

theorem measurableSet_selected_bad (P : MTProcess S ι) (σ : Schedule P)
    (hbad : ∀ i, MeasurableSet (P.bad i)) (t : ℕ) :
    MeasurableSet {ω | state P (σ.select ω) ω t ∈ P.bad (σ.select ω t)} := by
  let : MeasurableSpace ι := ⊤
  have heq : {ω | state P (σ.select ω) ω t ∈ P.bad (σ.select ω t)} =
      ⋃ i : ι, ({ω | σ.select ω t = i} ∩ {ω | state P (σ.select ω) ω t ∈ P.bad i}) := by
    ext ω
    simp only [Set.mem_ofPred_eq, Set.mem_iUnion, Set.mem_inter_iff]
    constructor
    · intro h; exact ⟨σ.select ω t, rfl, h⟩
    · rintro ⟨i, hi, h⟩; simpa only [hi] using h
  rw [heq]
  exact MeasurableSet.iUnion (fun i =>
    ((σ.measurable_select t) (measurableSet_singleton i)).inter
      ((measurable_state P σ t) (hbad i)))

theorem measurableSet_running (P : MTProcess S ι) (σ : Schedule P)
    (hbad : ∀ i, MeasurableSet (P.bad i)) (n : ℕ) :
    MeasurableSet {ω | Running P (σ.select ω) ω n} := by
  have heq : {ω | Running P (σ.select ω) ω n} =
      ⋂ t ∈ Finset.range n, {ω | state P (σ.select ω) ω t ∈ P.bad (σ.select ω t)} := by
    ext ω
    simp only [Running, Set.mem_ofPred_eq, Set.mem_iInter, Finset.mem_range]
  rw [heq]
  exact Finset.measurableSet_biInter _ (fun t _ => measurableSet_selected_bad P σ hbad t)

noncomputable def tLog (P : MTProcess S ι) (C : ℕ → ι) (ω : LogSpace S) : ℝ≥0∞ :=
  ∑' t : ℕ, if Running P C ω (t + 1) then 1 else 0

noncomputable def expectedWork (P : MTProcess S ι) (σ : Schedule P) : ℝ≥0∞ :=
  ∫⁻ ω, tLog P (σ.select ω) ω ∂logMeasure S

theorem measurable_tLog (P : MTProcess S ι) (σ : Schedule P)
    (hbad : ∀ i, MeasurableSet (P.bad i)) : Measurable (fun ω => tLog P (σ.select ω) ω) := by
  apply Measurable.tsum
  intro t
  exact Measurable.ite (measurableSet_running P σ hbad (t + 1)) measurable_const measurable_const

theorem state_first_eq (P : MTProcess S ι) (ω : LogSpace S) (t : ℕ) :
    state P (HLS.WitnessDAG.realSchedule P ω) ω t =
      (randStep P (initialStateFromLog ω) ω t).1 := by
  funext v
  change atIdx ω v (uses P (realC P (initialStateFromLog ω) ω) t v) = _
  unfold uses
  rw [← randStep_count_eq_filter_card P (initialStateFromLog ω) ω v t]
  exact (randStep_state_eq_atIdx P (initialStateFromLog ω) ω
    (initialStateFromLog_eq_atIdx ω) t v).symm

noncomputable def first (P : MTProcess S ι) (hbad : ∀ i, MeasurableSet (P.bad i)) :
    Schedule P where
  select := HLS.WitnessDAG.realSchedule P
  measurable_select := fun t =>
    measurable_realC_of_measurable_init P hbad initialStateFromLog measurable_initialStateFromLog t
  admissible := by
    intro ω t h
    rw [state_first_eq] at h ⊢
    apply pickFirstViolated_mem_violated
    intro he
    apply h
    intro i hi
    exact Set.notMem_empty i (he ▸ hi)

theorem tLog_first_eq (P : MTProcess S ι) (hbad : ∀ i, MeasurableSet (P.bad i))
    (ω : LogSpace S) : tLog P ((first P hbad).select ω) ω = randomInitTLog P ω := by
  unfold tLog randomInitTLog TLog
  apply tsum_congr
  intro t
  have heq : Running P ((first P hbad).select ω) ω (t + 1) ↔
      RunningUntil P (initialStateFromLog ω) ω (t + 1) := by
    change Running P (HLS.WitnessDAG.realSchedule P ω) ω (t + 1) ↔ _
    unfold Running RunningUntil
    constructor
    · intro h s hs
      have hh := h s hs
      rw [state_first_eq] at hh
      exact hh
    · intro h s hs
      rw [state_first_eq]
      exact h s hs
  simp only [Set.indicator_apply, Set.mem_ofPred_eq, heq]

theorem expectedWork_first_eq (P : MTProcess S ι) (hbad : ∀ i, MeasurableSet (P.bad i)) :
    expectedWork P (first P hbad) = randomInitETLog P := by
  unfold expectedWork randomInitETLog
  simp_rw [tLog_first_eq]

end MTPolicy

#check @MTPolicy.uses_zero
#check @MTPolicy.uses_succ
#check @MTPolicy.uses_le
#check @MTPolicy.state_zero
#check @MTPolicy.state_succ
#check @MTPolicy.uses_congr
#check @MTPolicy.measurable_uses
#check @MTPolicy.measurable_state
#check @MTPolicy.measurableSet_selected_bad
#check @MTPolicy.measurableSet_running
#check @MTPolicy.measurable_tLog
#check @MTPolicy.state_first_eq
#check @MTPolicy.tLog_first_eq
#check @MTPolicy.expectedWork_first_eq
