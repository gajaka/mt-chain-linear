/-
  PPGraphRepair.lean
  Repair Semantics for Proof-Preserving Graphs

  A local graph-state model: each vertex slot initially stores its own V value.
  Repair copies a selected healthy neighbor's value into one slot, leaving the
  other values, edges and reach_rel unchanged. The original invariant predicate
  is then evaluated on the updated values; its specification is fixed.

  The update is explicit, so locality and non-interference compare the graph
  before and after repair. Candidate existence is a hypothesis; this file does
  not provide a repair-search algorithm or model an arbitrary implementation.
-/

module

public import Mathlib.Tactic
public import PPGraph.Core.Graph

@[expose] public section

variable {V : Type}

-- Bundled PPG for repair (avoids name collision with Graph from PPGraph.lean)
structure RepairGraph (V : Type) where
  edges : V → V → Prop
  reach_rel : V → V → Prop
  invariant_holds : V → Prop

variable (G : RepairGraph V)

-- Isolation: vertex whose invariant fails
def isolated (v : V) : Prop := ¬ G.invariant_holds v

-- Active edge: both endpoints hold invariant
def active_edge (x y : V) : Prop :=
  G.edges x y ∧ G.invariant_holds x ∧ G.invariant_holds y

-- Repair is possible if there exists a valid reach_rel neighbor
def repair_possible (v : V) : Prop :=
  isolated G v ∧ ∃ w : V, w ≠ v ∧ G.reach_rel v w ∧ G.invariant_holds w

-- Repair candidates: set of valid neighbors
def repair_candidates (v : V) (w : V) : Prop :=
  w ≠ v ∧ G.reach_rel v w ∧ G.invariant_holds w

-- Relational choice: extract a concrete repair target
noncomputable def repair_target (v : V) (h : repair_possible G v) : V :=
  Classical.choose h.2

-- The chosen target satisfies the repair predicate
theorem repair_target_valid (v : V) (h : repair_possible G v) :
    repair_candidates G v (repair_target G v h) :=
  Classical.choose_spec h.2

-- Total selection leaves a vertex unchanged when no repair candidate is available.
noncomputable def repair_choice (v : V) : V := by
  classical
  exact if h : repair_possible G v then repair_target G v h else v

-- A slot stores its own value initially. Repair copies one selected V value;
-- unavailable repairs leave every stored value unchanged.
noncomputable def repair_state (v w : V) : V := by
  classical
  exact if w = v then repair_choice G v else w

-- The repaired graph view evaluates the original invariant on repaired data.
-- The predicate on V values, topology and reachability are not redefined.
noncomputable def repair_at (v : V) : RepairGraph V := by
  exact { G with invariant_holds := fun w =>
    G.invariant_holds (repair_state G v w) }

-- Route repair: bypass isolated vertex through valid neighbor
def route_repairable (x v y : V) : Prop :=
  isolated G v ∧ G.edges x v ∧ G.edges v y ∧
  ∃ w : V, w ≠ v ∧ G.invariant_holds w ∧ G.reach_rel v w ∧
    G.edges x w ∧ G.edges w y

-- Globally repairable: every isolated vertex can be repaired
def globally_repairable : Prop :=
  ∀ v : V, isolated G v → repair_possible G v

-- ═══════════════════════════════════════════════════════════════════
-- Theorems
-- ═══════════════════════════════════════════════════════════════════

-- T1: Repair possible implies candidates exist
theorem repair_candidates_exist (v : V)
    (h : repair_possible G v) :
    ∃ w : V, repair_candidates G v w := by
  obtain ⟨_, w, hw⟩ := h
  exact ⟨w, hw⟩

-- A selected healthy candidate restores the repaired vertex in the updated graph.
theorem repair_restores (v : V) (h : repair_possible G v) :
    (repair_at G v).invariant_holds v := by
  classical
  simpa [repair_at, repair_state, repair_choice, h] using
    (repair_target_valid G v h).2.2

-- T2: Updating v preserves the stored data and health of every distinct vertex.
theorem repair_locality (v w : V) (hne : v ≠ w) :
    repair_state G v w = w ∧
      ((repair_at G v).invariant_holds w ↔ G.invariant_holds w) := by
  classical
  have hframe : repair_state G v w = w := by
    simp [repair_state, Ne.symm hne]
  exact ⟨hframe, by simp [repair_at, hframe]⟩

-- T3: Healthy vertices are fixed by both total selection and graph repair.
theorem healthy_self_stable (v : V)
    (h_healthy : G.invariant_holds v) :
    repair_choice G v = v ∧ repair_at G v = G := by
  classical
  have hn : ¬ repair_possible G v := fun h => h.1 h_healthy
  have hchoice : repair_choice G v = v := by simp [repair_choice, hn]
  constructor
  · exact hchoice
  · have hstate : repair_state G v = id := by
      funext w
      by_cases hw : w = v
      · subst w
        simpa [repair_state] using hchoice
      · simp [repair_state, hw]
    change { G with invariant_holds := fun w =>
      G.invariant_holds (repair_state G v w) } = G
    rw [hstate]
    rfl

-- T4: Route repair with healthy endpoints implies active bypass
theorem route_bypass (x v y : V)
    (h : route_repairable G x v y)
    (hx : G.invariant_holds x)
    (hy : G.invariant_holds y) :
    ∃ w : V, active_edge G x w ∧ active_edge G w y := by
  obtain ⟨_, _, _, w, _, hw_inv, _, hw_xw, hw_wy⟩ := h
  exact ⟨w, ⟨hw_xw, hx, hw_inv⟩, ⟨hw_wy, hw_inv, hy⟩⟩

-- T5: Globally repairable means every isolated vertex has a candidate
theorem global_means_candidates (h : globally_repairable G) (v : V)
    (hiso : isolated G v) :
    ∃ w : V, repair_candidates G v w := by
  exact repair_candidates_exist G v (h v hiso)

-- T6: A local repair cannot isolate any previously healthy vertex.
theorem repair_no_cascade (v w : V)
    (hw : G.invariant_holds w) :
    (repair_at G v).invariant_holds w := by
  classical
  by_cases hwv : w = v
  · subst w
    by_cases h : repair_possible G v
    · exact repair_restores G v h
    · simpa [repair_at, repair_state, repair_choice, h] using hw
  · exact (repair_locality G v w (Ne.symm hwv)).2.mpr hw

-- T7: Repairing a third vertex preserves whether an edge is active.
theorem active_independent_of_isolated (x w v : V)
    (hvx : v ≠ x) (hvw : v ≠ w) :
    active_edge (repair_at G v) x w ↔ active_edge G x w := by
  classical
  have hx : repair_state G v x = x := (repair_locality G v x hvx).1
  have hw : repair_state G v w = w := (repair_locality G v w hvw).1
  simp [active_edge, repair_at, hx, hw]

-- ═══════════════════════════════════════════════════════════════════
-- Verification
-- ═══════════════════════════════════════════════════════════════════

#check @repair_candidates_exist
#check @repair_target_valid
#check @repair_restores
#check @repair_locality
#check @healthy_self_stable
#check @route_bypass
#check @global_means_candidates
#check @repair_no_cascade
#check @active_independent_of_isolated
