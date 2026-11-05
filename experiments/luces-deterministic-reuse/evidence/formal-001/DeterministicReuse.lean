module

public import PPGraph.Repair.SemanticHazards
public import PPGraph.Repair.ObservableAlgebra

@[expose] public section

set_option autoImplicit false

/-!
Deterministic feature-snapshot operations for the LUCES local-plan contract.

The state has four local coupling features, signed GEN and dataset identity.
An operation replaces the local features and preserves the last two fields.
All observable claims below concern those operations on this feature model.
They do not prove that Python feature extraction or arbitrary raw-coupling
operations refine the model. Finite hazard exactness is restricted to the
explicit bank supplied as the allowed source domain. No MT law is assumed.
-/

namespace LucesDeterministicReuse

abbrev State := RepairHazard.State (Fin 6) ℚ
abbrev LocalValues := Fin 4 → ℚ
abbrev Certificate := Fin 8

def mongeThreshold : ℚ := 1553741871442821 / 2251799813685248

/-- Field order: rows, Monge, violations, nnz, signed GEN, dataset key. -/
def replaceLocal (values : LocalValues) (s : State) : State :=
  fun i => if h : i.val < 4 then values ⟨i.val, h⟩ else s i

def protectedView (s : State) : ℚ × ℚ := (s 4, s 5)

theorem protectedView_replaceLocal (values : LocalValues) (s : State) :
    protectedView (replaceLocal values s) = protectedView s := by
  simp [protectedView, replaceLocal]

/-- Every function of GEN and dataset identity is fixed, not merely stable. -/
theorem protected_projection_fixed (values : LocalValues) :
    RepairObservable.Fixed (replaceLocal values)
      (RepairObservable.projectionAlgebra (R := ℚ) protectedView) := by
  rintro f ⟨g, rfl⟩
  funext s
  change g (protectedView (replaceLocal values s)) = g (protectedView s)
  rw [protectedView_replaceLocal]

theorem protected_projection_stable :
    RepairObservable.Stable replaceLocal
      (RepairObservable.projectionAlgebra (R := ℚ) protectedView) := by
  apply RepairObservable.projection_stable_of_factor replaceLocal protectedView
    (fun _ view => view)
  exact protectedView_replaceLocal

/-- Keep all eight positions, including the repeated Monge test at position 5. -/
def sat (expectedDataset : ℚ) (c : Certificate) (s : State) : Prop :=
  match c.val with
  | 0 => s 0 > 0
  | 1 => s 1 > mongeThreshold
  | 2 => s 2 = 0
  | 3 => s 3 ≤ 19
  | 4 => s 0 > 0 ∧ s 1 > mongeThreshold ∧ s 2 = 0 ∧ s 3 ≤ 19
  | 5 => s 1 > mongeThreshold
  | 6 => s 4 > 0
  | _ => s 5 = expectedDataset

instance satDecidable (expectedDataset : ℚ) (c : Certificate) (s : State) :
    Decidable (sat expectedDataset c s) := by
  unfold sat
  split <;> infer_instance

theorem repeated_monge (expectedDataset : ℚ) (s : State) :
    sat expectedDataset 1 s ↔ sat expectedDataset 5 s := Iff.rfl

theorem protected_certificates_unchanged (expectedDataset : ℚ)
    (values : LocalValues) (s : State) :
    (sat expectedDataset 6 (replaceLocal values s) ↔ sat expectedDataset 6 s) ∧
    (sat expectedDataset 7 (replaceLocal values s) ↔ sat expectedDataset 7 s) := by
  simp [sat, replaceLocal]

def allowed (bank : List State) (s : State) : Prop := s ∈ bank

instance allowedDecidable (bank : List State) : DecidablePred (allowed bank) := by
  intro s
  unfold allowed
  infer_instance

/-- Exactness is for the explicitly supplied finite source bank only. -/
def bankDomain (bank : List State) :
    RepairSemanticHazard.CompleteDomain (allowed bank) where
  states := bank
  covers := fun _ hs => hs

theorem exact_scope_is_semantic (bank : List State) (expectedDataset : ℚ)
    (values : LocalValues) (core : Finset Certificate) :
    RepairSemanticHazard.exactScope (allowed bank) (sat expectedDataset)
      (replaceLocal values) (bankDomain bank) core =
    RepairSemanticHazard.scope (allowed bank) (sat expectedDataset)
      core (replaceLocal values) :=
  RepairSemanticHazard.exactScope_eq_scope (allowed bank) (sat expectedDataset)
    (replaceLocal values) (bankDomain bank) core

theorem protected_outside_semantic_scope (bank : List State) (expectedDataset : ℚ)
    (values : LocalValues) (core : Finset Certificate) :
    (6 : Certificate) ∉ RepairSemanticHazard.scope (allowed bank)
      (sat expectedDataset) core (replaceLocal values) ∧
    (7 : Certificate) ∉ RepairSemanticHazard.scope (allowed bank)
      (sat expectedDataset) core (replaceLocal values) := by
  constructor
  · apply RepairSemanticHazard.not_mem_scope_of_preserves
    intro s _ hs
    exact (protected_certificates_unchanged expectedDataset values s).1.mpr hs
  · apply RepairSemanticHazard.not_mem_scope_of_preserves
    intro s _ hs
    exact (protected_certificates_unchanged expectedDataset values s).2.mpr hs

/-- Failed positions must be checked as targets; passing positions form the core. -/
def failed (expectedDataset : ℚ) (before : State) : Finset Certificate :=
  Finset.univ.filter fun c => ¬ sat expectedDataset c before

theorem fullContract_iff_all_pass (expectedDataset : ℚ) (before after : State) :
    RepairHazard.FullContract (sat expectedDataset) (failed expectedDataset before)
      Finset.univ before after ↔ ∀ c, sat expectedDataset c after := by
  constructor
  · rintro ⟨ht, hp⟩ c
    by_cases hb : sat expectedDataset c before
    · exact hp c (Finset.mem_univ c) hb
    · exact ht c (Finset.mem_filter.mpr ⟨Finset.mem_univ c, hb⟩)
  · intro h
    exact ⟨fun c _ => h c, fun c _ _ => h c⟩

/-- The original exact-scope checker agrees with checking all eight positions.

This is a single-step statement requiring membership of the source bank.
Repeated use must establish membership again, or prove an explicit closure law.
-/
theorem checked_acceptance_iff_all_pass (bank : List State) (expectedDataset : ℚ)
    (values : LocalValues) (before : State) (hb : before ∈ bank) :
    RepairSemanticHazard.checkExactCommit (allowed bank) (sat expectedDataset)
      (bankDomain bank) (failed expectedDataset before) Finset.univ
      (replaceLocal values) before = true ↔
      ∀ c, sat expectedDataset c (replaceLocal values before) := by
  rw [RepairSemanticHazard.checkExactCommit_iff_fullContract
    (allowed bank) (sat expectedDataset) (bankDomain bank)
    (failed expectedDataset before) Finset.univ (replaceLocal values) before hb]
  exact fullContract_iff_all_pass expectedDataset before (replaceLocal values before)

theorem checked_step_preserves (bank : List State) (expectedDataset : ℚ)
    (values : LocalValues) (before : State) (hb : before ∈ bank) :
    ∀ c, sat expectedDataset c before →
      sat expectedDataset c
        (RepairSemanticHazard.checkedExactStep (allowed bank) (sat expectedDataset)
          (bankDomain bank) (failed expectedDataset before) Finset.univ
          (replaceLocal values) before) := by
  intro c hc
  exact RepairSemanticHazard.checkedExactStep_preserves (allowed bank)
    (sat expectedDataset) (bankDomain bank) (failed expectedDataset before)
    Finset.univ (replaceLocal values) before hb c (Finset.mem_univ c) hc

#print axioms protected_projection_fixed
#print axioms protected_projection_stable
#print axioms exact_scope_is_semantic
#print axioms protected_outside_semantic_scope
#print axioms fullContract_iff_all_pass
#print axioms checked_acceptance_iff_all_pass
#print axioms checked_step_preserves

end LucesDeterministicReuse
