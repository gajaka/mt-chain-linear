/-
  Exact semantic invalidation scope for a fixed repair transformer and an
  explicit admissible-state domain. Unlike the footprint scope, every member
  has a counterexample for the actual predicate and transformer.

  A complete finite domain supplies an executable search, counterexamples,
  preservation certificates, and a commit checker equivalent to FullContract.
  Partial sampling is not a negative certificate. General infinite domains
  use proofs of preservation; no universal executable solver is asserted.
-/
module

public import PPGraph.Repair.Hazards

@[expose] public section

set_option autoImplicit false
set_option linter.unusedSectionVars false

namespace RepairSemanticHazard

variable {S C : Type} [DecidableEq C]

def Invalidates (sat : C → S → Prop) (run : S → S) (c : C) (s : S) : Prop :=
  sat c s ∧ ¬ sat c (run s)

instance invalidatesDecidable (sat : C → S → Prop) [∀ c, DecidablePred (sat c)]
    (run : S → S) (c : C) (s : S) : Decidable (Invalidates sat run c s) := by
  unfold Invalidates
  infer_instance

def PreservesOn (allowed : S → Prop) (sat : C → S → Prop)
    (run : S → S) (c : C) : Prop :=
  ∀ s, allowed s → sat c s → sat c (run s)

/-- Exact for this predicate, transformer, and domain, not just its footprints. -/
noncomputable def scope (allowed : S → Prop) (sat : C → S → Prop)
    (core : Finset C) (run : S → S) : Finset C := by
  classical
  exact core.filter fun c => ∃ s, allowed s ∧ Invalidates sat run c s

theorem mem_scope_iff (allowed : S → Prop) (sat : C → S → Prop)
    (core : Finset C) (run : S → S) (c : C) :
    c ∈ scope allowed sat core run ↔
      c ∈ core ∧ ∃ s, allowed s ∧ sat c s ∧ ¬ sat c (run s) := by
  classical
  unfold scope
  rw [Finset.mem_filter]
  rfl

theorem scope_subset_core (allowed : S → Prop) (sat : C → S → Prop)
    (core : Finset C) (run : S → S) : scope allowed sat core run ⊆ core := by
  intro c hc
  exact ((mem_scope_iff allowed sat core run c).mp hc).1

theorem mem_scope_iff_not_preserves (allowed : S → Prop) (sat : C → S → Prop)
    (core : Finset C) (run : S → S) (c : C) :
    c ∈ scope allowed sat core run ↔ c ∈ core ∧ ¬ PreservesOn allowed sat run c := by
  classical
  simp [mem_scope_iff, PreservesOn, not_forall]

/-- Every alarm has an actual admissible counterexample. -/
theorem scope_no_false_positives (allowed : S → Prop) (sat : C → S → Prop)
    (core : Finset C) (run : S → S) (c : C)
    (hc : c ∈ scope allowed sat core run) :
    ∃ s, allowed s ∧ Invalidates sat run c s := by
  simpa [Invalidates] using ((mem_scope_iff allowed sat core run c).mp hc).2

/-- Every actual invalidation of a core obligation is reported. -/
theorem scope_no_false_negatives (allowed : S → Prop) (sat : C → S → Prop)
    (core : Finset C) (run : S → S) (c : C) (hc : c ∈ core)
    (s : S) (ha : allowed s) (hb : sat c s) (hf : ¬ sat c (run s)) :
    c ∈ scope allowed sat core run :=
  (mem_scope_iff allowed sat core run c).mpr ⟨hc, s, ha, hb, hf⟩

theorem not_mem_scope_iff_preserves (allowed : S → Prop) (sat : C → S → Prop)
    (core : Finset C) (run : S → S) (c : C) (hc : c ∈ core) :
    c ∉ scope allowed sat core run ↔ PreservesOn allowed sat run c := by
  classical
  simp [mem_scope_iff_not_preserves, hc]

theorem preserved_outside_scope (allowed : S → Prop) (sat : C → S → Prop)
    (core : Finset C) (run : S → S) (c : C) (hc : c ∈ core)
    (hout : c ∉ scope allowed sat core run) :
    PreservesOn allowed sat run c :=
  (not_mem_scope_iff_preserves allowed sat core run c hc).mp hout

theorem not_mem_scope_of_preserves (allowed : S → Prop) (sat : C → S → Prop)
    (core : Finset C) (run : S → S) (c : C)
    (h : PreservesOn allowed sat run c) :
    c ∉ scope allowed sat core run := by
  intro hc
  exact ((mem_scope_iff_not_preserves allowed sat core run c).mp hc).2 h

/-- This is the least uniformly safe scope for the actual domain and action. -/
theorem scope_minimal (allowed : S → Prop) (sat : C → S → Prop)
    (core recheck : Finset C) (run : S → S)
    (hsafe : ∀ c ∈ core, c ∉ recheck → PreservesOn allowed sat run c) :
    scope allowed sat core run ⊆ recheck := by
  classical
  intro c hc
  by_contra hout
  obtain ⟨hcore, hbad⟩ := (mem_scope_iff_not_preserves allowed sat core run c).mp hc
  exact hbad (hsafe c hcore hout)

theorem scope_mono_domain (allowed small : S → Prop) (sat : C → S → Prop)
    (core : Finset C) (run : S → S) (hsub : ∀ s, small s → allowed s) :
    scope small sat core run ⊆ scope allowed sat core run := by
  intro c hc
  obtain ⟨hcore, s, hs, hb, hf⟩ := (mem_scope_iff small sat core run c).mp hc
  exact (mem_scope_iff allowed sat core run c).mpr ⟨hcore, s, hsub s hs, hb, hf⟩

theorem scope_eq_empty_of_preserves (allowed : S → Prop) (sat : C → S → Prop)
    (core : Finset C) (run : S → S)
    (h : ∀ c ∈ core, PreservesOn allowed sat run c) :
    scope allowed sat core run = ∅ := by
  ext c
  constructor
  · intro hc
    exact False.elim (not_mem_scope_of_preserves allowed sat core run c
      (h c ((mem_scope_iff allowed sat core run c).mp hc).1) hc)
  · simp

theorem scope_identity (allowed : S → Prop) (sat : C → S → Prop) (core : Finset C) :
    scope allowed sat core id = ∅ :=
  scope_eq_empty_of_preserves allowed sat core id (fun _ _ _ _ hb => hb)

/-- The composite scope may be strictly smaller because effects can cancel.
    The intermediate-state domain hypothesis is necessary for this bound. -/
theorem scope_comp_subset_union (allowed : S → Prop) (sat : C → S → Prop)
    (core : Finset C) (first second : S → S)
    (hclosed : ∀ s, allowed s → allowed (first s)) :
    scope allowed sat core (second ∘ first) ⊆
      scope allowed sat core first ∪ scope allowed sat core second := by
  classical
  intro c hc
  obtain ⟨hcore, s, ha, hb, hf⟩ := (mem_scope_iff allowed sat core _ c).mp hc
  by_cases hm : sat c (first s)
  · apply Finset.mem_union_right
    exact (mem_scope_iff allowed sat core second c).mpr
      ⟨hcore, first s, hclosed s ha, hm, hf⟩
  · apply Finset.mem_union_left
    exact (mem_scope_iff allowed sat core first c).mpr ⟨hcore, s, ha, hb, hm⟩

/-- Proof-based removal of known-safe footprint alarms remains sound.
    It need not be exact until all safe overlaps have been eliminated. -/
theorem scope_subset_after_safe_removal (allowed : S → Prop) (sat : C → S → Prop)
    (core candidate safe : Finset C) (run : S → S)
    (hcover : scope allowed sat core run ⊆ candidate)
    (hsafe : ∀ c ∈ safe, PreservesOn allowed sat run c) :
    scope allowed sat core run ⊆ candidate \ safe := by
  intro c hc
  apply Finset.mem_sdiff.mpr
  exact ⟨hcover hc, fun hcs =>
    not_mem_scope_of_preserves allowed sat core run c (hsafe c hcs) hc⟩

section Footprints

variable {V α : Type} [DecidableEq V]

/-- Semantic analysis refines the existing conservative footprint scope. -/
theorem scope_subset_affected (allowed : RepairHazard.State V α → Prop)
    (sat : C → RepairHazard.State V α → Prop) (vars : CertVars C V)
    (hloc : Local vars sat) (core : Finset C) (a : RepairHazard.Action V α) :
    scope allowed sat core a.run ⊆ RepairHazard.affected vars core a.writes := by
  classical
  intro c hc
  obtain ⟨hcore, s, _, hb, hf⟩ := (mem_scope_iff allowed sat core a.run c).mp hc
  by_contra hout
  exact hf ((RepairHazard.preserved_outside_affected vars sat hloc core a.writes
    s (a.run s) (a.frame s) c hcore hout).mpr hb)

end Footprints

section FiniteSearch

variable (allowed : S → Prop) (sat : C → S → Prop) (run : S → S)
variable [DecidablePred allowed] [∀ c, DecidablePred (sat c)]

/-- Absence is only meaningful as a refutation when the list covers the domain. -/
def findInvalidation (states : List S) (c : C) : Option S :=
  states.find? fun s => decide (allowed s ∧ Invalidates sat run c s)

theorem findInvalidation_sound (states : List S) (c : C) (s : S)
    (h : findInvalidation allowed sat run states c = some s) :
    allowed s ∧ Invalidates sat run c s := by
  have hs := List.find?_some
    (p := fun t => decide (allowed t ∧ Invalidates sat run c t)) h
  exact of_decide_eq_true hs

theorem findInvalidation_mem (states : List S) (c : C) (s : S)
    (h : findInvalidation allowed sat run states c = some s) : s ∈ states :=
  List.mem_of_find?_eq_some h

theorem findInvalidation_none_iff (states : List S) (c : C) :
    findInvalidation allowed sat run states c = none ↔
      ∀ s ∈ states, ¬ (allowed s ∧ Invalidates sat run c s) := by
  simp [findInvalidation]

theorem findInvalidation_isSome_iff (states : List S) (c : C) :
    (findInvalidation allowed sat run states c).isSome = true ↔
      ∃ s ∈ states, allowed s ∧ Invalidates sat run c s := by
  cases h : findInvalidation allowed sat run states c with
  | none =>
      simp only [Option.isSome_none, Bool.false_eq_true, false_iff]
      rintro ⟨s, hm, hs⟩
      exact (findInvalidation_none_iff allowed sat run states c).mp h s hm hs
  | some s =>
      simp only [Option.isSome_some, true_iff]
      exact ⟨s, findInvalidation_mem allowed sat run states c s h,
        findInvalidation_sound allowed sat run states c s h⟩

def finiteScope (states : List S) (core : Finset C) : Finset C :=
  core.filter fun c => (findInvalidation allowed sat run states c).isSome = true

theorem mem_finiteScope_iff (states : List S) (core : Finset C) (c : C) :
    c ∈ finiteScope allowed sat run states core ↔
      c ∈ core ∧ ∃ s ∈ states, allowed s ∧ Invalidates sat run c s := by
  simp [finiteScope, Finset.mem_filter, findInvalidation_isSome_iff]

/-- A checked enumeration of every admissible state, not an empirical sample. -/
structure CompleteDomain (allowed : S → Prop) where
  states : List S
  covers : ∀ s, allowed s → s ∈ states

def exactScope (domain : CompleteDomain allowed) (core : Finset C) : Finset C :=
  finiteScope allowed sat run domain.states core

theorem exactScope_eq_scope (domain : CompleteDomain allowed) (core : Finset C) :
    exactScope allowed sat run domain core = scope allowed sat core run := by
  ext c
  rw [exactScope, mem_finiteScope_iff, mem_scope_iff]
  constructor
  · rintro ⟨hc, s, _, ha, hb, hf⟩
    exact ⟨hc, s, ha, hb, hf⟩
  · rintro ⟨hc, s, ha, hb, hf⟩
    exact ⟨hc, s, domain.covers s ha, ha, hb, hf⟩

/-- Computed outcomes carry either universal preservation or a counterexample. -/
inductive HazardResult (allowed : S → Prop) (sat : C → S → Prop)
    (run : S → S) (c : C) where
  | preserved (proof : PreservesOn allowed sat run c)
  | invalidated (state : S) (admissible : allowed state)
      (failure : Invalidates sat run c state)

def HazardResult.isHazard {allowed : S → Prop} {sat : C → S → Prop}
    {run : S → S} {c : C} : HazardResult allowed sat run c → Bool
  | .preserved _ => false
  | .invalidated _ _ _ => true

def classify (domain : CompleteDomain allowed) (c : C) :
    HazardResult allowed sat run c :=
  match h : findInvalidation allowed sat run domain.states c with
  | some s => .invalidated s
      (findInvalidation_sound allowed sat run domain.states c s h).1
      (findInvalidation_sound allowed sat run domain.states c s h).2
  | none => .preserved (by
      intro s ha hb
      by_contra hf
      exact (findInvalidation_none_iff allowed sat run domain.states c).mp h s
        (domain.covers s ha) ⟨ha, hb, hf⟩)

theorem classify_isHazard_iff (domain : CompleteDomain allowed) (c : C) :
    (classify allowed sat run domain c).isHazard = true ↔
      ∃ s, allowed s ∧ Invalidates sat run c s := by
  constructor
  · intro h
    cases hr : classify allowed sat run domain c with
    | preserved hp => simp [hr, HazardResult.isHazard] at h
    | invalidated s ha hf => exact ⟨s, ha, hf⟩
  · rintro ⟨s, ha, hb, hf⟩
    cases hr : classify allowed sat run domain c with
    | preserved hp => exact False.elim (hf (hp s ha hb))
    | invalidated t ht hf => rfl

end FiniteSearch

section Commit

variable (sat : C → S → Prop) [∀ c, DecidablePred (sat c)]

/-- Every target is checked; only the supplied protected scope is rechecked. -/
def checkScope (target recheck : Finset C) (before after : S) : Bool :=
  decide ((∀ c ∈ target, sat c after) ∧
    ∀ c ∈ recheck, sat c before → sat c after)

theorem checkScope_iff (target recheck : Finset C) (before after : S) :
    checkScope sat target recheck before after = true ↔
      (∀ c ∈ target, sat c after) ∧
        ∀ c ∈ recheck, sat c before → sat c after := by
  simp [checkScope]

variable {V α : Type}

theorem checkScope_iff_fullContract
    (allowed : RepairHazard.State V α → Prop)
    (sat : C → RepairHazard.State V α → Prop) [∀ c, DecidablePred (sat c)]
    (target core recheck : Finset C) (run : RepairHazard.State V α → RepairHazard.State V α)
    (hsub : recheck ⊆ core) (hcover : scope allowed sat core run ⊆ recheck)
    (before : RepairHazard.State V α) (ha : allowed before) :
    checkScope sat target recheck before (run before) = true ↔
      RepairHazard.FullContract sat target core before (run before) := by
  rw [checkScope_iff]
  constructor
  · rintro ⟨ht, hp⟩
    refine ⟨ht, ?_⟩
    intro c hc hb
    by_cases hr : c ∈ recheck
    · exact hp c hr hb
    · have hs : c ∉ scope allowed sat core run := fun hm => hr (hcover hm)
      exact preserved_outside_scope allowed sat core run c hc hs before ha hb
  · rintro ⟨ht, hp⟩
    exact ⟨ht, fun c hc => hp c (hsub hc)⟩

variable (allowed : RepairHazard.State V α → Prop)
    (sat : C → RepairHazard.State V α → Prop)
    [DecidablePred allowed] [∀ c, DecidablePred (sat c)]

def checkExactCommit (domain : CompleteDomain allowed) (target core : Finset C)
    (run : RepairHazard.State V α → RepairHazard.State V α)
    (before : RepairHazard.State V α) : Bool :=
  checkScope sat target (exactScope allowed sat run domain core) before (run before)

theorem checkExactCommit_iff_fullContract (domain : CompleteDomain allowed)
    (target core : Finset C) (run : RepairHazard.State V α → RepairHazard.State V α)
    (before : RepairHazard.State V α) (ha : allowed before) :
    checkExactCommit allowed sat domain target core run before = true ↔
      RepairHazard.FullContract sat target core before (run before) := by
  unfold checkExactCommit
  apply checkScope_iff_fullContract allowed sat target core _ run
  · rw [exactScope_eq_scope]
    exact scope_subset_core allowed sat core run
  · rw [exactScope_eq_scope]
  · exact ha

/-- Atomic model-state commit; this does not roll back a physical action. -/
def checkedExactStep (domain : CompleteDomain allowed) (target core : Finset C)
    (run : RepairHazard.State V α → RepairHazard.State V α)
    (before : RepairHazard.State V α) : RepairHazard.State V α :=
  if checkExactCommit allowed sat domain target core run before = true
    then run before else before

theorem checkedExactStep_preserves (domain : CompleteDomain allowed)
    (target core : Finset C) (run : RepairHazard.State V α → RepairHazard.State V α)
    (before : RepairHazard.State V α) (ha : allowed before) :
    ∀ c ∈ core, sat c before →
      sat c (checkedExactStep allowed sat domain target core run before) := by
  by_cases h : checkExactCommit allowed sat domain target core run before = true
  · simp only [checkedExactStep, ite_eq_left h]
    exact ((checkExactCommit_iff_fullContract allowed sat domain target core run before ha).mp h).2
  · simp only [checkedExactStep, ite_eq_right h]
    exact fun _ _ hb => hb

theorem checkedExactStep_target_of_accepted (domain : CompleteDomain allowed)
    (target core : Finset C) (run : RepairHazard.State V α → RepairHazard.State V α)
    (before : RepairHazard.State V α) (ha : allowed before)
    (h : checkExactCommit allowed sat domain target core run before = true) :
    ∀ c ∈ target, sat c (checkedExactStep allowed sat domain target core run before) := by
  simp only [checkedExactStep, ite_eq_left h]
  exact ((checkExactCommit_iff_fullContract allowed sat domain target core run before ha).mp h).1

end Commit

end RepairSemanticHazard

#check @RepairSemanticHazard.Invalidates
#check @RepairSemanticHazard.invalidatesDecidable
#check @RepairSemanticHazard.PreservesOn
#check @RepairSemanticHazard.scope
#check @RepairSemanticHazard.mem_scope_iff
#check @RepairSemanticHazard.scope_subset_core
#check @RepairSemanticHazard.mem_scope_iff_not_preserves
#check @RepairSemanticHazard.scope_no_false_positives
#check @RepairSemanticHazard.scope_no_false_negatives
#check @RepairSemanticHazard.not_mem_scope_iff_preserves
#check @RepairSemanticHazard.preserved_outside_scope
#check @RepairSemanticHazard.not_mem_scope_of_preserves
#check @RepairSemanticHazard.scope_minimal
#check @RepairSemanticHazard.scope_mono_domain
#check @RepairSemanticHazard.scope_eq_empty_of_preserves
#check @RepairSemanticHazard.scope_identity
#check @RepairSemanticHazard.scope_comp_subset_union
#check @RepairSemanticHazard.scope_subset_after_safe_removal
#check @RepairSemanticHazard.scope_subset_affected
#check @RepairSemanticHazard.findInvalidation
#check @RepairSemanticHazard.findInvalidation_sound
#check @RepairSemanticHazard.findInvalidation_mem
#check @RepairSemanticHazard.findInvalidation_none_iff
#check @RepairSemanticHazard.findInvalidation_isSome_iff
#check @RepairSemanticHazard.finiteScope
#check @RepairSemanticHazard.mem_finiteScope_iff
#check @RepairSemanticHazard.CompleteDomain
#check @RepairSemanticHazard.exactScope
#check @RepairSemanticHazard.exactScope_eq_scope
#check @RepairSemanticHazard.HazardResult
#check @RepairSemanticHazard.HazardResult.isHazard
#check @RepairSemanticHazard.classify
#check @RepairSemanticHazard.classify_isHazard_iff
#check @RepairSemanticHazard.checkScope
#check @RepairSemanticHazard.checkScope_iff
#check @RepairSemanticHazard.checkScope_iff_fullContract
#check @RepairSemanticHazard.checkExactCommit
#check @RepairSemanticHazard.checkExactCommit_iff_fullContract
#check @RepairSemanticHazard.checkedExactStep
#check @RepairSemanticHazard.checkedExactStep_preserves
#check @RepairSemanticHazard.checkedExactStep_target_of_accepted
