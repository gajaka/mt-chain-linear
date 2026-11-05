/-
  Semantic scope boundaries: the user's integer increment example, a complete
  two-state executable model, partial-sample failure, and cancellation in an
  atomic composite. All examples are mathematical models, not measurements.
-/
module

public import PPGraph.Repair.SemanticHazards

@[expose] public section

set_option autoImplicit false

namespace RepairSemanticHazardExamples

open RepairHazard RepairSemanticHazard

abbrev IntSnapshot := State Unit Int

abbrev IntCert := Fin 2

def intVars : CertVars IntCert Unit := fun _ => {()}

def intSat (c : IntCert) (s : IntSnapshot) : Prop :=
  if c = 0 then 0 ≤ s () else s () = 0

instance (c : IntCert) : DecidablePred (intSat c) := fun _ => by
  unfold intSat
  infer_instance

def increment : Action Unit Int where
  reads := {()}
  writes := {()}
  run := fun s _ => s () + 1
  frame := by
    intro _ v hv
    cases v
    simp at hv
  read_local := by
    intro s t h _ _
    rw [h () (Finset.mem_singleton_self ())]

def decrement : Action Unit Int where
  reads := {()}
  writes := {()}
  run := fun s _ => s () - 1
  frame := by
    intro _ v hv
    cases v
    simp at hv
  read_local := by
    intro s t h _ _
    rw [h () (Finset.mem_singleton_self ())]

def unrestrictedInt (_ : IntSnapshot) : Prop := True

instance : DecidablePred unrestrictedInt := fun _ => inferInstanceAs (Decidable True)

theorem intSat_local : Local intVars intSat := by
  intro c s t h
  simp only [intSat]
  rw [h () (Finset.mem_singleton_self ())]

theorem increment_structural_scope :
    affected intVars Finset.univ increment.writes = Finset.univ := by
  decide

theorem increment_preserves_nonnegative :
    PreservesOn unrestrictedInt intSat increment.run (0 : IntCert) := by
  intro s _ hb
  change 0 ≤ s () at hb
  change 0 ≤ s () + 1
  omega

theorem increment_nonnegative_alarm_removed :
    (0 : IntCert) ∉ scope unrestrictedInt intSat Finset.univ increment.run :=
  not_mem_scope_of_preserves _ _ _ _ _ increment_preserves_nonnegative

theorem increment_zero_has_counterexample :
    unrestrictedInt (fun _ => (0 : Int)) ∧
      Invalidates intSat increment.run (1 : IntCert) (fun _ => (0 : Int)) := by
  decide

theorem increment_zero_alarm_retained :
    (1 : IntCert) ∈ scope unrestrictedInt intSat Finset.univ increment.run := by
  apply (mem_scope_iff _ _ _ _ _).mpr
  exact ⟨Finset.mem_univ _, (fun _ => (0 : Int)),
    increment_zero_has_counterexample⟩

theorem increment_semantic_scope_exact :
    scope unrestrictedInt intSat Finset.univ increment.run = {(1 : IntCert)} := by
  ext c
  fin_cases c
  · simp [increment_nonnegative_alarm_removed]
  · simp [increment_zero_alarm_retained]

/-- A computable exact scope for an infinite integer domain, backed by proofs. -/
theorem increment_refined_scope_exact :
    affected intVars Finset.univ increment.writes \ {(0 : IntCert)} =
      scope unrestrictedInt intSat Finset.univ increment.run := by
  rw [increment_structural_scope, increment_semantic_scope_exact]
  decide

theorem increment_refined_commit_iff_fullContract (before : IntSnapshot) :
    checkScope intSat ∅ {(1 : IntCert)} before (increment.run before) = true ↔
      FullContract intSat ∅ Finset.univ before (increment.run before) := by
  apply checkScope_iff_fullContract unrestrictedInt intSat ∅ Finset.univ _ increment.run
  · exact Finset.subset_univ _
  · rw [increment_semantic_scope_exact]
  · trivial

theorem decrement_nonnegative_alarm_retained :
    (0 : IntCert) ∈ scope unrestrictedInt intSat Finset.univ decrement.run := by
  apply (mem_scope_iff _ _ _ _ _).mpr
  refine ⟨Finset.mem_univ _, (fun _ => (0 : Int)), ?_⟩
  decide

/-- Final-state preservation does not assert preservation at intermediate steps. -/
theorem cancelling_plan_is_identity :
    runPlan [increment, decrement] = (id : IntSnapshot → IntSnapshot) := by
  funext s u
  cases u
  change s () + 1 - 1 = s ()
  omega

theorem cancelling_plan_has_empty_semantic_scope :
    scope unrestrictedInt intSat Finset.univ (runPlan [increment, decrement]) = ∅ := by
  rw [cancelling_plan_is_identity]
  exact scope_identity _ _ _

theorem cancelling_plan_still_has_structural_overlap :
    affected intVars Finset.univ (planWrites [increment, decrement]) = Finset.univ := by
  decide

abbrev BitSnapshot := State Unit Bool

abbrev BitCert := Fin 4

def bitFalse : BitSnapshot := fun _ => false

def bitTrue : BitSnapshot := fun _ => true

def unrestrictedBit (_ : BitSnapshot) : Prop := True

instance : DecidablePred unrestrictedBit := fun _ => inferInstanceAs (Decidable True)

def bitDomain : CompleteDomain unrestrictedBit where
  states := [bitFalse, bitTrue]
  covers := by
    intro s _
    simp only [List.mem_cons, List.not_mem_nil, or_false]
    cases hs : s () with
    | false =>
        left
        funext u
        cases u
        exact hs
    | true =>
        right
        funext u
        cases u
        exact hs

def bitVars : CertVars BitCert Unit := fun _ => {()}

def bitSat (c : BitCert) (s : BitSnapshot) : Prop :=
  if c = 0 then s () = true
  else if c = 1 then s () = false
  else if c = 2 then True else False

instance (c : BitCert) : DecidablePred (bitSat c) := fun _ => by
  unfold bitSat
  infer_instance

def setTrue : Action Unit Bool where
  reads := ∅
  writes := {()}
  run := fun _ => bitTrue
  frame := by
    intro _ v hv
    cases v
    simp at hv
  read_local := by intro _ _ _ _ _; rfl

theorem bitSat_local : Local bitVars bitSat := by
  intro c s t h
  simp only [bitSat]
  rw [h () (Finset.mem_singleton_self ())]

theorem bit_structural_scope_all :
    affected bitVars Finset.univ setTrue.writes = Finset.univ := by
  decide

theorem bit_exact_scope_singleton :
    exactScope unrestrictedBit bitSat setTrue.run bitDomain Finset.univ = {(1 : BitCert)} := by
  decide +kernel

theorem bit_counterexample_found :
    findInvalidation unrestrictedBit bitSat setTrue.run bitDomain.states (1 : BitCert) =
      some bitFalse := by
  decide +kernel

theorem bit_preserved_classified :
    (classify unrestrictedBit bitSat setTrue.run bitDomain (0 : BitCert)).isHazard = false := by
  decide +kernel

theorem bit_invalidated_classified :
    (classify unrestrictedBit bitSat setTrue.run bitDomain (1 : BitCert)).isHazard = true := by
  decide +kernel

/-- Sampling only the true state misses an actual invalidation elsewhere. -/
theorem partial_sample_misses_hazard :
    finiteScope unrestrictedBit bitSat setTrue.run [bitTrue] Finset.univ = ∅ ∧
      exactScope unrestrictedBit bitSat setTrue.run bitDomain Finset.univ = {(1 : BitCert)} := by
  decide +kernel

theorem partial_sample_does_not_cover :
    ¬ (∀ s : BitSnapshot, unrestrictedBit s → s ∈ [bitTrue]) := by
  intro h
  have he : bitFalse = bitTrue := by simpa using h bitFalse trivial
  have hv := congrFun he ()
  simp [bitFalse, bitTrue] at hv

/-- A potential domain-wide hazard does not imply damage at every current state. -/
theorem hazard_can_be_harmless_at_current_state :
    (1 : BitCert) ∈ exactScope unrestrictedBit bitSat setTrue.run bitDomain Finset.univ ∧
      ¬ Invalidates bitSat setTrue.run (1 : BitCert) bitTrue := by
  decide +kernel

theorem exact_commit_rejects_real_damage :
    checkExactCommit unrestrictedBit bitSat bitDomain {0} {1} setTrue.run bitFalse = false ∧
      checkedExactStep unrestrictedBit bitSat bitDomain {0} {1} setTrue.run bitFalse = bitFalse := by
  constructor
  · decide +kernel
  · rfl

theorem exact_commit_accepts_safe_core :
    exactScope unrestrictedBit bitSat setTrue.run bitDomain {0, 2} = ∅ ∧
      checkExactCommit unrestrictedBit bitSat bitDomain {0} {0, 2} setTrue.run bitFalse = true := by
  decide +kernel

theorem exact_commit_still_checks_targets :
    exactScope unrestrictedBit bitSat setTrue.run bitDomain {0, 2} = ∅ ∧
      checkExactCommit unrestrictedBit bitSat bitDomain {1} {0, 2} setTrue.run bitFalse = false := by
  decide +kernel

theorem accepted_commit_has_full_contract :
    FullContract bitSat {0} {0, 2} bitFalse (setTrue.run bitFalse) :=
  (checkExactCommit_iff_fullContract unrestrictedBit bitSat bitDomain {0} {0, 2}
    setTrue.run bitFalse trivial).mp exact_commit_accepts_safe_core.2

end RepairSemanticHazardExamples

#check @RepairSemanticHazardExamples.IntSnapshot
#check @RepairSemanticHazardExamples.IntCert
#check @RepairSemanticHazardExamples.intVars
#check @RepairSemanticHazardExamples.intSat
#check @RepairSemanticHazardExamples.increment
#check @RepairSemanticHazardExamples.decrement
#check @RepairSemanticHazardExamples.unrestrictedInt
#check @RepairSemanticHazardExamples.intSat_local
#check @RepairSemanticHazardExamples.increment_structural_scope
#check @RepairSemanticHazardExamples.increment_preserves_nonnegative
#check @RepairSemanticHazardExamples.increment_nonnegative_alarm_removed
#check @RepairSemanticHazardExamples.increment_zero_has_counterexample
#check @RepairSemanticHazardExamples.increment_zero_alarm_retained
#check @RepairSemanticHazardExamples.increment_semantic_scope_exact
#check @RepairSemanticHazardExamples.increment_refined_scope_exact
#check @RepairSemanticHazardExamples.increment_refined_commit_iff_fullContract
#check @RepairSemanticHazardExamples.decrement_nonnegative_alarm_retained
#check @RepairSemanticHazardExamples.cancelling_plan_is_identity
#check @RepairSemanticHazardExamples.cancelling_plan_has_empty_semantic_scope
#check @RepairSemanticHazardExamples.cancelling_plan_still_has_structural_overlap
#check @RepairSemanticHazardExamples.BitSnapshot
#check @RepairSemanticHazardExamples.BitCert
#check @RepairSemanticHazardExamples.bitFalse
#check @RepairSemanticHazardExamples.bitTrue
#check @RepairSemanticHazardExamples.unrestrictedBit
#check @RepairSemanticHazardExamples.bitDomain
#check @RepairSemanticHazardExamples.bitVars
#check @RepairSemanticHazardExamples.bitSat
#check @RepairSemanticHazardExamples.setTrue
#check @RepairSemanticHazardExamples.bitSat_local
#check @RepairSemanticHazardExamples.bit_structural_scope_all
#check @RepairSemanticHazardExamples.bit_exact_scope_singleton
#check @RepairSemanticHazardExamples.bit_counterexample_found
#check @RepairSemanticHazardExamples.bit_preserved_classified
#check @RepairSemanticHazardExamples.bit_invalidated_classified
#check @RepairSemanticHazardExamples.partial_sample_misses_hazard
#check @RepairSemanticHazardExamples.partial_sample_does_not_cover
#check @RepairSemanticHazardExamples.hazard_can_be_harmless_at_current_state
#check @RepairSemanticHazardExamples.exact_commit_rejects_real_damage
#check @RepairSemanticHazardExamples.exact_commit_accepts_safe_core
#check @RepairSemanticHazardExamples.exact_commit_still_checks_targets
#check @RepairSemanticHazardExamples.accepted_commit_has_full_contract
