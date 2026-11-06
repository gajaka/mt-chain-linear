/-
  PPGraphSelfAssessment.lean
  Formal Self-Assessment for Proof-Preserving Graphs

  Graph extension uses a fixed invariant predicate. Its preservation lemmas
  expose consequences of that model. State repair is treated separately:
  a proposed operator must restore its target and preserve the certified core.

  Builds on PPGraph.lean (Graph, pp_valid, invariant_set, violation_set,
  pp_transform, violating_isolated) and PPGraphRepair.lean (RepairGraph,
  isolated, repair_possible, repair_candidates).

  Key modeling choice: repair is a primitive operator (S → V → S) on
  system state. The specification (S → V → Prop) is an external fixed
  parameter held fixed in every before/after statement. A repair operator
  is valid (proof-preserving) if it
  satisfies two proof obligations: target restoration and core preservation.
  The later recovery results derive set inclusion and strict growth from
  those obligations; a concrete operator must establish them independently.

  Author: Dragan Stosic, 2026.
-/

module

public import Mathlib.Tactic
public import PPGraph.Core.Graph
public import PPGraph.Core.Repair

@[expose] public section

set_option linter.unusedVariables false
set_option linter.unusedSectionVars false

variable {V : Type} [DecidableEq V]

-- ═══════════════════════════════════════════════════════════════════
-- Section 1: Contamination Impossibility
-- ═══════════════════════════════════════════════════════════════════

/-- A graph extension preserves invariant-set membership under the same
    predicate. This is the graph-level helper invariant_monotone; arbitrary
    changes to system data require the separate state-repair contract below. -/
theorem contamination_impossible (G1 G2 : Graph V)
    (rr_rel : V → V → Prop) (invariant_holds : V → Prop)
    (h_transform : pp_transform G1 G2 rr_rel invariant_holds)
    (v : V) (h_inv : invariant_set G1 invariant_holds v) :
    invariant_set G2 invariant_holds v :=
  invariant_monotone G1 G2 rr_rel invariant_holds h_transform v h_inv

/-- If a vertex violates in G1, it also violates in G2 under pp_transform
    (since pp_transform preserves vertices and uses the same invariant).
    Violations propagate forward - they cannot be erased by extension. -/
theorem violations_propagate (G1 G2 : Graph V)
    (rr_rel : V → V → Prop) (invariant_holds : V → Prop)
    (h_transform : pp_transform G1 G2 rr_rel invariant_holds)
    (v : V) (h_viol1 : violation_set G1 invariant_holds v) :
    violation_set G2 invariant_holds v :=
  ⟨h_transform.1 v h_viol1.1, h_viol1.2⟩

-- ═══════════════════════════════════════════════════════════════════
-- Section 2: Silent Redefinition Impossibility
-- ═══════════════════════════════════════════════════════════════════

/-- Membership at an existing vertex is unchanged because pp_transform
    retains vertices and both graphs use the same invariant predicate. -/
theorem no_silent_redefinition (G1 G2 : Graph V)
    (rr_rel : V → V → Prop) (invariant_holds : V → Prop)
    (h_transform : pp_transform G1 G2 rr_rel invariant_holds)
    (v : V) (h_vert : G1.vertices v) :
    invariant_set G1 invariant_holds v ↔ invariant_set G2 invariant_holds v := by
  constructor
  · exact fun h => contamination_impossible G1 G2 rr_rel invariant_holds h_transform v h
  · intro ⟨_, h_inv⟩
    exact ⟨h_vert, h_inv⟩

-- ═══════════════════════════════════════════════════════════════════
-- Section 3: Assessment Completeness
-- ═══════════════════════════════════════════════════════════════════

/-- Every vertex falls into exactly one of three categories:
    certified (invariant holds), repairable (isolated with at least
    one repair candidate), or currently non-repairable (isolated
    with no candidate in the current state). -/
theorem assessment_trichotomy (G : RepairGraph V) (v : V) :
    G.invariant_holds v ∨
    (isolated G v ∧ ∃ w, repair_candidates G v w) ∨
    (isolated G v ∧ ¬ ∃ w, repair_candidates G v w) := by
  by_cases h_inv : G.invariant_holds v
  · exact Or.inl h_inv
  · right
    have h_iso : isolated G v := h_inv
    by_cases h_rep : ∃ w, repair_candidates G v w
    · exact Or.inl ⟨h_iso, h_rep⟩
    · exact Or.inr ⟨h_iso, h_rep⟩

/-- The three categories are pairwise exclusive: certified
    is definitionally ¬isolated, so no vertex is in both. -/
theorem certified_excludes_isolated (G : RepairGraph V) (v : V)
    (h_inv : G.invariant_holds v) :
    ¬ isolated G v :=
  fun h_iso => h_iso h_inv

-- ═══════════════════════════════════════════════════════════════════
-- Section 4: Monotone Recovery (repair operator model)
--
-- Three evolution modes:
--   PP evolution: G → G', Spec fixed
--   Relaxation:   θ → θ', State fixed
--   Repair:       s → s', Spec fixed
--
-- Repair is a function on states. The theorems evaluate the same external
-- specification before and after the update. A repair function can depend
-- on that specification; preserving its truth requires the obligations below.
-- ═══════════════════════════════════════════════════════════════════

variable {S : Type}

/-- Repair operator: given a state and a target vertex, produce a new state.
    This is the primitive - what the system does when it attempts to fix v. -/
def RepairOp (S V : Type) := S → V → S

/-- A specification evaluates a state at a vertex. Each repair theorem holds
    this predicate fixed while evaluating it on the old and new states. -/
def Spec (S V : Type) := S → V → Prop

/-- Target is broken in the current state. -/
def broken (spec : Spec S V) (s : S) (v : V) : Prop :=
  ¬ spec s v

/-- Proof obligation 1: repair restores the target vertex. -/
def target_restored (R : RepairOp S V) (spec : Spec S V) (s : S) (v : V) : Prop :=
  broken spec s v → spec (R s v) v

/-- Proof obligation 2: repair preserves the certified core. -/
def core_preserved (R : RepairOp S V) (spec : Spec S V) (s : S) (v : V) : Prop :=
  ∀ w, w ≠ v → spec s w → spec (R s v) w

/-- A repair operator is valid (proof-preserving) if it satisfies both obligations. -/
def valid_repair (R : RepairOp S V) (spec : Spec S V) (s : S) (v : V) : Prop :=
  target_restored R spec s v ∧ core_preserved R spec s v

/-- Expose target restoration and core preservation from the supplied repair
    contract. The following theorems derive preservation at every vertex
    and strict growth of the certified set. -/
theorem repair_monotone_recovery (R : RepairOp S V) (spec : Spec S V)
    (s : S) (v : V)
    (h_broken : broken spec s v)
    (h_valid : valid_repair R spec s v) :
    spec (R s v) v ∧ (∀ w, w ≠ v → spec s w → spec (R s v) w) :=
  ⟨h_valid.1 h_broken, h_valid.2⟩

/-- Preservation: every previously certified vertex remains certified
    after repair. This is set inclusion Certified(s) ⊆ Certified(R(s,v)). -/
theorem repair_preserves_certified (R : RepairOp S V) (spec : Spec S V)
    (s : S) (v : V)
    (h_broken : broken spec s v)
    (h_valid : valid_repair R spec s v)
    (w : V) (h_was_cert : spec s w) :
    spec (R s v) w := by
  by_cases h_eq : w = v
  · subst h_eq
    exact absurd h_was_cert h_broken
  · exact h_valid.2 w h_eq h_was_cert

/-- Strict growth: the certified set after repair is a PROPER superset.
    Certified(s) ⊊ Certified(R(s,v)):
    - v is in Certified(R(s,v)) but not in Certified(s)
    - everything in Certified(s) is in Certified(R(s,v))
    This is the key theorem: repair produces genuine monotone growth. -/
theorem repair_strict_growth (R : RepairOp S V) (spec : Spec S V)
    (s : S) (v : V)
    (h_broken : broken spec s v)
    (h_valid : valid_repair R spec s v) :
    (∀ w, spec s w → spec (R s v) w) ∧
    (spec (R s v) v ∧ ¬ spec s v) := by
  constructor
  · intro w h_cert
    exact repair_preserves_certified R spec s v h_broken h_valid w h_cert
  · exact ⟨h_valid.1 h_broken, h_broken⟩

/-- Repair restores the broken target under the same fixed specification.
    The state changes, the spec does not. -/
theorem repair_restores_broken_target (R : RepairOp S V) (spec : Spec S V)
    (s : S) (v : V)
    (h_broken : broken spec s v)
    (h_valid : valid_repair R spec s v) :
    spec (R s v) v ∧ ¬ spec s v :=
  ⟨h_valid.1 h_broken, h_broken⟩

-- ═══════════════════════════════════════════════════════════════════
-- Section 5: Failure Containment Under PP-Validity
-- ═══════════════════════════════════════════════════════════════════

/-- In a pp-valid graph, a violating vertex has no outgoing edges.
    Failure is automatically contained by the graph structure. -/
theorem failure_contained (G : Graph V) (rr_rel : V → V → Prop)
    (invariant_holds : V → Prop)
    (h_valid : pp_valid G rr_rel invariant_holds)
    (v : V) (h_viol : violating G invariant_holds v) :
    ∀ y, ¬ G.edges v y :=
  violating_isolated G rr_rel invariant_holds h_valid v h_viol

/-- In a pp-valid graph, a violating vertex has no incoming edges.
    The vertex is completely disconnected from the certified core. -/
theorem failure_fully_isolated (G : Graph V) (rr_rel : V → V → Prop)
    (invariant_holds : V → Prop)
    (h_valid : pp_valid G rr_rel invariant_holds)
    (v : V) (h_viol : violating G invariant_holds v) :
    ∀ y, ¬ G.edges y v := by
  intro y h_edge
  have h_pp := h_valid y v h_edge
  exact h_viol.2 h_pp.2.2.1

/-- Combined isolation: a violating vertex in a pp-valid graph
    has no edges in either direction. It is fully cut off. -/
theorem failure_total_isolation (G : Graph V) (rr_rel : V → V → Prop)
    (invariant_holds : V → Prop)
    (h_valid : pp_valid G rr_rel invariant_holds)
    (v : V) (h_viol : violating G invariant_holds v) :
    (∀ y, ¬ G.edges v y) ∧ (∀ y, ¬ G.edges y v) :=
  ⟨failure_contained G rr_rel invariant_holds h_valid v h_viol,
   failure_fully_isolated G rr_rel invariant_holds h_valid v h_viol⟩

-- ═══════════════════════════════════════════════════════════════════
-- Verification
-- ═══════════════════════════════════════════════════════════════════

#check @contamination_impossible
#check @violations_propagate
#check @no_silent_redefinition
#check @assessment_trichotomy
#check @certified_excludes_isolated
#check @repair_monotone_recovery
#check @repair_preserves_certified
#check @repair_strict_growth
#check @repair_restores_broken_target
#check @failure_contained
#check @failure_fully_isolated
#check @failure_total_isolation
