/-
  Proof-Preserving Graph Theory (Lean 4)
  Full port of proof_preserving_graphs.pvs (Stosic)

  Paths represented as Fin-indexed sequences (matching PVS prewalk).
-/

module

public import Mathlib.Tactic

@[expose] public section

-- ═══════════════════════════════════════════════════════════════════
-- Section 1: Graph Structure
-- ═══════════════════════════════════════════════════════════════════

structure Graph (V : Type) where
  vertices : V → Prop
  edges : V → V → Prop
  edges_in_vertices : ∀ x y, edges x y → vertices x ∧ vertices y

variable {V : Type}

-- ═══════════════════════════════════════════════════════════════════
-- Section 2: Core Definitions
-- ═══════════════════════════════════════════════════════════════════

def pp_edge (rr_rel : V → V → Prop) (invariant_holds : V → Prop) (x y : V) : Prop :=
  x ≠ y ∧ invariant_holds x ∧ invariant_holds y ∧ rr_rel x y

def pp_edge_weak (rr_rel : V → V → Prop) (x y : V) : Prop :=
  x ≠ y ∧ rr_rel x y

def pp_valid (G : Graph V) (rr_rel : V → V → Prop) (invariant_holds : V → Prop) : Prop :=
  ∀ x y, G.edges x y → pp_edge rr_rel invariant_holds x y

def pp_valid_weak (G : Graph V) (rr_rel : V → V → Prop) : Prop :=
  ∀ x y, G.edges x y → pp_edge_weak rr_rel x y

-- ═══════════════════════════════════════════════════════════════════
-- Section 3: Walks and Paths (Fin-indexed sequences)
-- ═══════════════════════════════════════════════════════════════════

-- A prewalk is a nonempty sequence of vertices indexed by Fin n
structure Prewalk (V : Type) (n : Nat) where
  len_pos : n ≥ 1
  seq : Fin n → V

-- Walk: consecutive vertices are edges in G
def is_walk (G : Graph V) {n : Nat} (pw : Prewalk V n) : Prop :=
  (∀ i : Fin n, G.vertices (pw.seq i)) ∧
  (∀ i : Fin n, (h : i.val + 1 < n) →
    G.edges (pw.seq i) (pw.seq ⟨i.val + 1, h⟩))

-- PP-walk: walk + all invariants hold + all consecutive pairs are pp-edges
def pp_walk (G : Graph V) (rr_rel : V → V → Prop) (invariant_holds : V → Prop)
    {n : Nat} (pw : Prewalk V n) : Prop :=
  is_walk G pw ∧
  (∀ i : Fin n, invariant_holds (pw.seq i)) ∧
  (∀ i : Fin n, (h : i.val + 1 < n) →
    pp_edge rr_rel invariant_holds (pw.seq i) (pw.seq ⟨i.val + 1, h⟩))

-- PP-path: pp_walk with injective vertex sequence
def pp_path (G : Graph V) (rr_rel : V → V → Prop) (invariant_holds : V → Prop)
    {n : Nat} (pw : Prewalk V n) : Prop :=
  pp_walk G rr_rel invariant_holds pw ∧
  Function.Injective pw.seq

-- Start and end of a prewalk
def pw_start {n : Nat} (pw : Prewalk V n) : V := pw.seq ⟨0, Nat.lt_of_lt_of_le Nat.zero_lt_one pw.len_pos⟩
def pw_end {n : Nat} (pw : Prewalk V n) : V := pw.seq ⟨n - 1, Nat.sub_lt (Nat.lt_of_lt_of_le Nat.zero_lt_one pw.len_pos) Nat.zero_lt_one⟩

-- ═══════════════════════════════════════════════════════════════════
-- Section 4: Fundamental Theorems
-- ═══════════════════════════════════════════════════════════════════

-- T1: valid implies weak
theorem valid_implies_weak (G : Graph V) (rr_rel : V → V → Prop)
    (invariant_holds : V → Prop)
    (h : pp_valid G rr_rel invariant_holds) :
    pp_valid_weak G rr_rel := by
  intro x y he
  exact ⟨(h x y he).1, (h x y he).2.2.2⟩

-- T2: pp-valid edge implies both endpoints satisfy invariants
theorem pp_valid_implies_invariants (G : Graph V)
    (rr_rel : V → V → Prop) (invariant_holds : V → Prop)
    (h : pp_valid G rr_rel invariant_holds)
    (x y : V) (he : G.edges x y) :
    invariant_holds x ∧ invariant_holds y := by
  exact ⟨(h x y he).2.1, (h x y he).2.2.1⟩

-- T3: pp-path implies pp-walk
theorem pp_path_is_walk (G : Graph V) (rr_rel : V → V → Prop)
    (invariant_holds : V → Prop) {n : Nat} (pw : Prewalk V n)
    (h : pp_path G rr_rel invariant_holds pw) :
    pp_walk G rr_rel invariant_holds pw :=
  h.1

-- T4: all vertices on a pp-walk satisfy invariants
theorem pp_walk_invariants (G : Graph V) (rr_rel : V → V → Prop)
    (invariant_holds : V → Prop) {n : Nat} (pw : Prewalk V n)
    (h : pp_walk G rr_rel invariant_holds pw)
    (i : Fin n) : invariant_holds (pw.seq i) :=
  h.2.1 i

-- T5: pp-path start and end satisfy invariants
theorem pp_path_endpoints_invariant (G : Graph V) (rr_rel : V → V → Prop)
    (invariant_holds : V → Prop) {n : Nat} (pw : Prewalk V n)
    (h : pp_path G rr_rel invariant_holds pw) :
    invariant_holds (pw_start pw) ∧ invariant_holds (pw_end pw) :=
  ⟨h.1.2.1 ⟨0, Nat.lt_of_lt_of_le Nat.zero_lt_one pw.len_pos⟩,
   h.1.2.1 ⟨n - 1, Nat.sub_lt (Nat.lt_of_lt_of_le Nat.zero_lt_one pw.len_pos) Nat.zero_lt_one⟩⟩

-- ═══════════════════════════════════════════════════════════════════
-- Section 5: Subgraph Validity
-- ═══════════════════════════════════════════════════════════════════

def is_subgraph (S G : Graph V) : Prop :=
  (∀ v, S.vertices v → G.vertices v) ∧
  (∀ x y, S.edges x y → G.edges x y)

-- T6: subgraph of pp-valid graph is pp-valid
theorem subgraph_valid (G S : Graph V) (rr_rel : V → V → Prop)
    (invariant_holds : V → Prop)
    (hsub : is_subgraph S G)
    (hvalid : pp_valid G rr_rel invariant_holds) :
    pp_valid S rr_rel invariant_holds :=
  fun x y he => hvalid x y (hsub.2 x y he)

-- ═══════════════════════════════════════════════════════════════════
-- Section 6: Graph Evolution
-- ═══════════════════════════════════════════════════════════════════

def pp_transform (G1 G2 : Graph V) (rr_rel : V → V → Prop)
    (invariant_holds : V → Prop) : Prop :=
  (∀ v, G1.vertices v → G2.vertices v) ∧
  (∀ x y, G1.edges x y → G2.edges x y) ∧
  pp_valid G1 rr_rel invariant_holds ∧
  pp_valid G2 rr_rel invariant_holds

-- T7: pp_transform is reflexive
theorem pp_transform_reflexive (G : Graph V) (rr_rel : V → V → Prop)
    (invariant_holds : V → Prop)
    (h : pp_valid G rr_rel invariant_holds) :
    pp_transform G G rr_rel invariant_holds :=
  ⟨fun _ hv => hv, fun _ _ he => he, h, h⟩

-- T8: pp_transform is transitive
theorem pp_transform_transitive (G1 G2 G3 : Graph V) (rr_rel : V → V → Prop)
    (invariant_holds : V → Prop)
    (h12 : pp_transform G1 G2 rr_rel invariant_holds)
    (h23 : pp_transform G2 G3 rr_rel invariant_holds) :
    pp_transform G1 G3 rr_rel invariant_holds :=
  ⟨fun v hv => h23.1 v (h12.1 v hv),
   fun x y he => h23.2.1 x y (h12.2.1 x y he),
   h12.2.2.1, h23.2.2.2⟩

-- T9: pp_transform is antisymmetric
theorem pp_transform_antisymmetric (G1 G2 : Graph V) (rr_rel : V → V → Prop)
    (invariant_holds : V → Prop)
    (h12 : pp_transform G1 G2 rr_rel invariant_holds)
    (h21 : pp_transform G2 G1 rr_rel invariant_holds) :
    (∀ v, G1.vertices v ↔ G2.vertices v) ∧
    (∀ x y, G1.edges x y ↔ G2.edges x y) :=
  ⟨fun v => ⟨h12.1 v, h21.1 v⟩, fun x y => ⟨h12.2.1 x y, h21.2.1 x y⟩⟩

-- ═══════════════════════════════════════════════════════════════════
-- Section 7: Invariant Sets and Monotonicity
-- ═══════════════════════════════════════════════════════════════════

def invariant_set (G : Graph V) (invariant_holds : V → Prop) : V → Prop :=
  fun v => G.vertices v ∧ invariant_holds v

def violation_set (G : Graph V) (invariant_holds : V → Prop) : V → Prop :=
  fun v => G.vertices v ∧ ¬ invariant_holds v

-- T10: invariant set grows monotonically
theorem invariant_monotone (G1 G2 : Graph V) (rr_rel : V → V → Prop)
    (invariant_holds : V → Prop)
    (h : pp_transform G1 G2 rr_rel invariant_holds)
    (v : V) (hv : invariant_set G1 invariant_holds v) :
    invariant_set G2 invariant_holds v :=
  ⟨h.1 v hv.1, hv.2⟩

-- T11: invariant and violation partition vertex set
theorem vertex_partition (G : Graph V) (invariant_holds : V → Prop) (x : V)
    (hx : G.vertices x) :
    invariant_set G invariant_holds x ∨ violation_set G invariant_holds x := by
  by_cases hi : invariant_holds x
  · exact Or.inl ⟨hx, hi⟩
  · exact Or.inr ⟨hx, hi⟩

-- T12: invariant and violation are disjoint
theorem invariant_violation_disjoint (G : Graph V) (invariant_holds : V → Prop) (x : V) :
    ¬ (invariant_set G invariant_holds x ∧ violation_set G invariant_holds x) :=
  fun ⟨⟨_, hi⟩, ⟨_, hni⟩⟩ => hni hi

-- ═══════════════════════════════════════════════════════════════════
-- Section 8: Connectivity
-- ═══════════════════════════════════════════════════════════════════

def pp_connected (G : Graph V) (rr_rel : V → V → Prop)
    (invariant_holds : V → Prop) (x y : V) : Prop :=
  ∃ (n : Nat) (pw : Prewalk V n), pp_path G rr_rel invariant_holds pw ∧
    pw_start pw = x ∧ pw_end pw = y

-- T13: pp-connected implies both endpoints satisfy invariants
theorem pp_connected_invariants (G : Graph V) (rr_rel : V → V → Prop)
    (invariant_holds : V → Prop) (x y : V)
    (h : pp_connected G rr_rel invariant_holds x y) :
    invariant_holds x ∧ invariant_holds y := by
  obtain ⟨n, pw, hpath, hstart, hend⟩ := h
  have hboth := pp_path_endpoints_invariant G rr_rel invariant_holds pw hpath
  rw [← hstart, ← hend]
  exact hboth

-- ═══════════════════════════════════════════════════════════════════
-- Section 9: Violation Detection
-- ═══════════════════════════════════════════════════════════════════

def violating (G : Graph V) (invariant_holds : V → Prop) (x : V) : Prop :=
  G.vertices x ∧ ¬ invariant_holds x

-- T14: violating vertices have no outgoing edges
theorem violating_isolated (G : Graph V) (rr_rel : V → V → Prop)
    (invariant_holds : V → Prop)
    (h : pp_valid G rr_rel invariant_holds)
    (x : V) (hv : violating G invariant_holds x) :
    ∀ y, ¬ G.edges x y :=
  fun y he => hv.2 (h x y he).2.1

-- T15: violating vertices have no incoming edges
theorem violating_no_incoming (G : Graph V) (rr_rel : V → V → Prop)
    (invariant_holds : V → Prop)
    (h : pp_valid G rr_rel invariant_holds)
    (x : V) (hv : violating G invariant_holds x) :
    ∀ y, ¬ G.edges y x :=
  fun y he => hv.2 (h y x he).2.2.1

-- ═══════════════════════════════════════════════════════════════════
-- Section 10: Deterministic Traversal
-- ═══════════════════════════════════════════════════════════════════

-- Each vertex has exactly one pp-successor
def deterministic (G : Graph V) (rr_rel : V → V → Prop)
    (invariant_holds : V → Prop) : Prop :=
  ∀ x, G.vertices x →
    ∃ y, (G.edges x y ∧ pp_edge rr_rel invariant_holds x y) ∧
      ∀ z, G.edges x z → z = y

-- T16: deterministic graph is pp-valid
theorem deterministic_is_valid (G : Graph V) (rr_rel : V → V → Prop)
    (invariant_holds : V → Prop)
    (h : deterministic G rr_rel invariant_holds) :
    pp_valid G rr_rel invariant_holds := by
  intro x y he
  have hx := (G.edges_in_vertices x y he).1
  obtain ⟨z, ⟨_, hppz⟩, huniq⟩ := h x hx
  have hyz := huniq y he
  subst hyz
  exact hppz

-- T17: deterministic implies inference function exists
theorem inference_function_exists (G : Graph V) (rr_rel : V → V → Prop)
    (invariant_holds : V → Prop)
    (h : deterministic G rr_rel invariant_holds) :
    ∃ f : V → V, ∀ x, G.vertices x →
      G.edges x (f x) ∧ pp_edge rr_rel invariant_holds x (f x) := by
  have choice : ∀ x, ∃ y, G.vertices x →
      G.edges x y ∧ pp_edge rr_rel invariant_holds x y := by
    intro x
    by_cases hx : G.vertices x
    · obtain ⟨y, ⟨he, hpp⟩, _⟩ := h x hx
      exact ⟨y, fun _ => ⟨he, hpp⟩⟩
    · exact ⟨x, fun hv => absurd hv hx⟩
  choose f hf using choice
  exact ⟨f, fun x hx => hf x hx⟩

-- ═══════════════════════════════════════════════════════════════════
-- Section 11: Separation
-- ═══════════════════════════════════════════════════════════════════

def pp_separates (G : Graph V) (rr_rel : V → V → Prop)
    (invariant_holds : V → Prop) (S : V → Prop) (x y : V) : Prop :=
  ∀ (n : Nat) (pw : Prewalk V n), pp_path G rr_rel invariant_holds pw →
    pw_start pw = x → pw_end pw = y →
    ∃ i : Fin n, S (pw.seq i)

-- T18: empty set separates iff not connected
theorem empty_separates_iff_disconnected (G : Graph V) (rr_rel : V → V → Prop)
    (invariant_holds : V → Prop) (x y : V) :
    pp_separates G rr_rel invariant_holds (fun _ => False) x y ↔
    ¬ pp_connected G rr_rel invariant_holds x y := by
  constructor
  · intro hsep hconn
    obtain ⟨n, pw, hpath, hstart, hend⟩ := hconn
    obtain ⟨i, hf⟩ := hsep n pw hpath hstart hend
    exact hf
  · intro hnconn n pw hpath hstart hend
    exfalso
    exact hnconn ⟨n, pw, hpath, hstart, hend⟩

-- ═══════════════════════════════════════════════════════════════════
-- Section 12: Certificate Chains
-- ═══════════════════════════════════════════════════════════════════

def certificate_chain (G : Graph V) (rr_rel : V → V → Prop)
    (invariant_holds : V → Prop) {n : Nat} (pw : Prewalk V n) : Prop :=
  pp_path G rr_rel invariant_holds pw ∧ n > 1

-- T19: certificate chain has all invariants satisfied
theorem certificate_chain_sound (G : Graph V) (rr_rel : V → V → Prop)
    (invariant_holds : V → Prop) {n : Nat} (pw : Prewalk V n)
    (h : certificate_chain G rr_rel invariant_holds pw)
    (i : Fin n) : invariant_holds (pw.seq i) :=
  h.1.1.2.1 i

-- T20: certificate chain witnesses connectivity
theorem certificate_chain_connects (G : Graph V) (rr_rel : V → V → Prop)
    (invariant_holds : V → Prop) {n : Nat} (pw : Prewalk V n)
    (h : certificate_chain G rr_rel invariant_holds pw) :
    pp_connected G rr_rel invariant_holds (pw_start pw) (pw_end pw) :=
  ⟨n, pw, h.1, rfl, rfl⟩

-- ═══════════════════════════════════════════════════════════════════
-- Section 13: Walk Resilience
-- ═══════════════════════════════════════════════════════════════════

-- T21: pp-walk persists under transformation
theorem walk_resilience (G1 G2 : Graph V) (rr_rel : V → V → Prop)
    (invariant_holds : V → Prop) {n : Nat} (pw : Prewalk V n)
    (ht : pp_transform G1 G2 rr_rel invariant_holds)
    (hw : pp_walk G1 rr_rel invariant_holds pw) :
    pp_walk G2 rr_rel invariant_holds pw :=
  ⟨⟨fun i => ht.1 _ (hw.1.1 i), fun i h => ht.2.1 _ _ (hw.1.2 i h)⟩,
   hw.2.1, hw.2.2⟩

-- T22: connectivity resilience
theorem connectivity_resilience (G1 G2 : Graph V) (rr_rel : V → V → Prop)
    (invariant_holds : V → Prop) (x y : V)
    (ht : pp_transform G1 G2 rr_rel invariant_holds)
    (hc : pp_connected G1 rr_rel invariant_holds x y) :
    pp_connected G2 rr_rel invariant_holds x y := by
  obtain ⟨n, pw, hpath, hstart, hend⟩ := hc
  exact ⟨n, pw, ⟨walk_resilience G1 G2 rr_rel invariant_holds pw ht hpath.1, hpath.2⟩,
         hstart, hend⟩

-- ═══════════════════════════════════════════════════════════════════
-- Verification
-- ═══════════════════════════════════════════════════════════════════

#check @valid_implies_weak
#check @pp_valid_implies_invariants
#check @pp_path_is_walk
#check @pp_walk_invariants
#check @pp_path_endpoints_invariant
#check @subgraph_valid
#check @pp_transform_reflexive
#check @pp_transform_transitive
#check @pp_transform_antisymmetric
#check @invariant_monotone
#check @vertex_partition
#check @invariant_violation_disjoint
#check @pp_connected_invariants
#check @violating_isolated
#check @violating_no_incoming
#check @deterministic_is_valid
#check @inference_function_exists
#check @empty_separates_iff_disconnected
#check @certificate_chain_sound
#check @certificate_chain_connects
#check @walk_resilience
#check @connectivity_resilience
