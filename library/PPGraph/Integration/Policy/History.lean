/-
  Concrete online execution of an arbitrary measurable history policy.
  The chooser sees the current assignment, the per-variable counters,
  all earlier assignments, and all earlier choices. Future history slots
  contain fixed initial/default padding, not future samples. A policy's
  validity field is the local violated-event selection rule only.

  We prove the table-state correspondence and construct MTPolicy.Schedule;
  no trajectory correspondence or convergence is assumed by the policy.
-/
module

public import PPGraph.Integration.Policy.MoserTardos

@[expose] public section

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option backward.isDefEq.respectTransparency false

open Classical MeasureTheory

namespace MTPolicy

variable {V : Type} [DecidableEq V] {S : VarSpaces V}
  {ι : Type} [Fintype ι] [DecidableEq ι] [Nonempty ι]

abbrev HistoryConfig (S : VarSpaces V) (ι : Type) :=
  MTState S × (V → ℕ) × (ℕ → MTState S) × (ℕ → ι)

structure HistoryRule (P : MTProcess S ι) where
  choose : ℕ → HistoryConfig S ι → ι
  measurable_choose : ∀ t, letI : MeasurableSpace ι := ⊤
    Measurable (choose t)
  valid : ∀ t z, ¬ MTGood P z.1 → z.1 ∈ P.bad (choose t z)

noncomputable def historyRun (P : MTProcess S ι) (R : HistoryRule P) (ω : LogSpace S) :
    ℕ → HistoryConfig S ι
  | 0 => (initialStateFromLog ω, fun _ => 0,
      fun _ => initialStateFromLog ω, fun _ => Classical.arbitrary ι)
  | t + 1 =>
      let z := historyRun P R ω t
      let i := R.choose t z
      let F := P.footprint i
      let next := resample F z.1 (drawFrom ω (fun v => z.2.1 v + 1))
      (next, fun v => if v ∈ F then z.2.1 v + 1 else z.2.1 v,
        fun s => if s = t + 1 then next else z.2.2.1 s,
        fun s => if s = t then i else z.2.2.2 s)

noncomputable def historySelect (P : MTProcess S ι) (R : HistoryRule P)
    (ω : LogSpace S) (t : ℕ) : ι := R.choose t (historyRun P R ω t)

theorem historyCount_le (P : MTProcess S ι) (R : HistoryRule P) (ω : LogSpace S) :
    ∀ t v, (historyRun P R ω t).2.1 v ≤ t
  | 0, v => le_rfl
  | t + 1, v => by
      change (if v ∈ P.footprint (historySelect P R ω t)
        then (historyRun P R ω t).2.1 v + 1 else (historyRun P R ω t).2.1 v) ≤ t + 1
      have ih := historyCount_le P R ω t v
      split_ifs <;> omega

theorem measurable_historyRun (P : MTProcess S ι) (R : HistoryRule P) :
    ∀ t, letI : MeasurableSpace ι := ⊤
      Measurable (fun ω : LogSpace S => historyRun P R ω t)
  | 0 => by
      let : MeasurableSpace ι := ⊤
      exact measurable_initialStateFromLog.prodMk
        (measurable_const.prodMk
          ((Measurable.of_eval (fun _ => measurable_initialStateFromLog)).prodMk measurable_const))
  | t + 1 => by
      let : MeasurableSpace ι := ⊤
      have ih := measurable_historyRun P R t
      have hs := measurable_fst.comp ih
      have hc := measurable_fst.comp (measurable_snd.comp ih)
      have hh := measurable_fst.comp (measurable_snd.comp (measurable_snd.comp ih))
      have hl := measurable_snd.comp (measurable_snd.comp (measurable_snd.comp ih))
      have hi : Measurable (fun ω : LogSpace S => historySelect P R ω t) :=
        (R.measurable_choose t).comp ih
      have hF (v : V) : MeasurableSet {ω : LogSpace S | v ∈ P.footprint (historySelect P R ω t)} :=
        hi (MeasurableSet.of_discrete (s := {i : ι | v ∈ P.footprint i}))
      have hdraw (v : V) : Measurable (fun ω : LogSpace S =>
          atIdx ω v ((historyRun P R ω t).2.1 v + 1)) :=
        measurable_eval_bounded v (t + 1) _
          (((measurable_pi_apply v).comp hc).add_const 1)
          (fun ω => by have := historyCount_le P R ω t v; omega)
      have hnext : Measurable (fun ω : LogSpace S =>
          resample (P.footprint (historySelect P R ω t)) (historyRun P R ω t).1
            (drawFrom ω (fun v => (historyRun P R ω t).2.1 v + 1))) := by
        apply Measurable.of_eval
        intro v
        exact Measurable.ite (hF v) (hdraw v) ((measurable_pi_apply v).comp hs)
      have hcnt : Measurable (fun ω : LogSpace S => fun v =>
          if v ∈ P.footprint (historySelect P R ω t)
          then (historyRun P R ω t).2.1 v + 1 else (historyRun P R ω t).2.1 v) := by
        apply Measurable.of_eval
        intro v
        exact Measurable.ite (hF v) (((measurable_pi_apply v).comp hc).add_const 1)
          ((measurable_pi_apply v).comp hc)
      have hstates : Measurable (fun ω : LogSpace S => fun s => if s = t + 1 then
          resample (P.footprint (historySelect P R ω t)) (historyRun P R ω t).1
            (drawFrom ω (fun v => (historyRun P R ω t).2.1 v + 1))
          else (historyRun P R ω t).2.2.1 s) := by
        apply Measurable.of_eval
        intro s
        by_cases h : s = t + 1
        · simp only [ite_eq_left h]; exact hnext
        · simp only [ite_eq_right h]; exact (measurable_pi_apply s).comp hh
      have hlabels : Measurable (fun ω : LogSpace S => fun s => if s = t then
          historySelect P R ω t else (historyRun P R ω t).2.2.2 s) := by
        apply Measurable.of_eval
        intro s
        by_cases h : s = t
        · simp only [ite_eq_left h]; exact hi
        · simp only [ite_eq_right h]; exact (measurable_pi_apply s).comp hl
      exact hnext.prodMk (hcnt.prodMk (hstates.prodMk hlabels))

theorem historyCount_eq_uses (P : MTProcess S ι) (R : HistoryRule P) (ω : LogSpace S) :
    ∀ t v, (historyRun P R ω t).2.1 v = uses P (historySelect P R ω) t v
  | 0, v => (uses_zero P (historySelect P R ω) v).symm
  | t + 1, v => by
      change (if v ∈ P.footprint (historySelect P R ω t)
        then (historyRun P R ω t).2.1 v + 1 else (historyRun P R ω t).2.1 v) = _
      rw [historyCount_eq_uses P R ω t v, uses_succ]
      split_ifs <;> simp

theorem historyState_eq_state (P : MTProcess S ι) (R : HistoryRule P) (ω : LogSpace S) :
    ∀ t, (historyRun P R ω t).1 = state P (historySelect P R ω) ω t
  | 0 => (state_zero P (historySelect P R ω) ω).symm
  | t + 1 => by
      change resample (P.footprint (historySelect P R ω t)) (historyRun P R ω t).1
        (drawFrom ω (fun v => (historyRun P R ω t).2.1 v + 1)) = _
      rw [state_succ, historyState_eq_state P R ω t]
      congr 1
      funext v
      exact congrArg (fun n => atIdx ω v (n + 1)) (historyCount_eq_uses P R ω t v)

theorem history_admissible (P : MTProcess S ι) (R : HistoryRule P) (ω : LogSpace S) :
    Admissible P (historySelect P R ω) ω := by
  intro t h
  rw [← historyState_eq_state] at h ⊢
  exact R.valid t (historyRun P R ω t) h

noncomputable def fromHistory (P : MTProcess S ι) (R : HistoryRule P) : Schedule P where
  select := historySelect P R
  measurable_select := fun t => (R.measurable_choose t).comp (measurable_historyRun P R t)
  admissible := history_admissible P R

theorem history_states_record (P : MTProcess S ι) (R : HistoryRule P) (ω : LogSpace S) :
    ∀ t s, s ≤ t → (historyRun P R ω t).2.2.1 s = state P (historySelect P R ω) ω s
  | 0, s, hs => by
      have h : s = 0 := by omega
      subst s
      exact (state_zero P (historySelect P R ω) ω).symm
  | t + 1, s, hs => by
      change (if s = t + 1 then (historyRun P R ω (t + 1)).1
        else (historyRun P R ω t).2.2.1 s) = _
      by_cases h : s = t + 1
      · rw [ite_eq_left h, h]; exact historyState_eq_state P R ω (t + 1)
      · rw [ite_eq_right h]; exact history_states_record P R ω t s (by omega)

theorem history_labels_record (P : MTProcess S ι) (R : HistoryRule P) (ω : LogSpace S) :
    ∀ t s, s < t → (historyRun P R ω t).2.2.2 s = historySelect P R ω s
  | 0, s, hs => by omega
  | t + 1, s, hs => by
      change (if s = t then historySelect P R ω t else (historyRun P R ω t).2.2.2 s) = _
      by_cases h : s = t
      · rw [ite_eq_left h, h]
      · rw [ite_eq_right h]; exact history_labels_record P R ω t s (by omega)

theorem history_states_future_padding (P : MTProcess S ι) (R : HistoryRule P) (ω : LogSpace S) :
    ∀ t s, t < s → (historyRun P R ω t).2.2.1 s = initialStateFromLog ω
  | 0, s, hs => rfl
  | t + 1, s, hs => by
      change (if s = t + 1 then (historyRun P R ω (t + 1)).1
        else (historyRun P R ω t).2.2.1 s) = _
      rw [ite_eq_right (by omega)]
      exact history_states_future_padding P R ω t s (by omega)

theorem history_labels_future_padding (P : MTProcess S ι) (R : HistoryRule P) (ω : LogSpace S) :
    ∀ t s, t ≤ s → (historyRun P R ω t).2.2.2 s = Classical.arbitrary ι
  | 0, s, hs => rfl
  | t + 1, s, hs => by
      change (if s = t then historySelect P R ω t else (historyRun P R ω t).2.2.2 s) = _
      rw [ite_eq_right (by omega)]
      exact history_labels_future_padding P R ω t s (by omega)

end MTPolicy

#check @MTPolicy.historyCount_le
#check @MTPolicy.measurable_historyRun
#check @MTPolicy.historyCount_eq_uses
#check @MTPolicy.historyState_eq_state
#check @MTPolicy.history_admissible
#check @MTPolicy.history_states_record
#check @MTPolicy.history_labels_record
#check @MTPolicy.history_states_future_padding
#check @MTPolicy.history_labels_future_padding
