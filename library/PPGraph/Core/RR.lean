/-
  PPGraphRR.lean
  Refinement Relations - Port of sets_aux@rr_rel (NASA pvslib, Stosic)

  Faithful port of:
    - relation_extension[T, U]
    - rr_rel[T, U]

  The refinement relation RR is defined over pairs (T, U) where
  each domain is partitioned by an equivalence relation, and
  abstraction/concretization functions f : T → U, g : U → T
  connect the two domains.
-/

module

public import Mathlib.Tactic
public import PPGraph.Core.Graph

@[expose] public section

-- ═══════════════════════════════════════════════════════════════════
-- Section 1: Relation Extension (port of relation_extension.pvs)
-- ═══════════════════════════════════════════════════════════════════

variable {T U : Type}

/-- Product equivalence on pairs: (m₁,m₂) ~ (n₁,n₂) iff
    m₁ ~_T n₁ and m₂ ~_U n₂ -/
def rel_extension (le_T : T → T → Prop) (le_U : U → U → Prop)
    (m n : T × U) : Prop :=
  le_T m.1 n.1 ∧ le_U m.2 n.2

/-- rel_extension is an equivalence when both components are -/
theorem rel_extension_is_equivalence (le_T : T → T → Prop) (le_U : U → U → Prop)
    (h_T : Equivalence le_T) (h_U : Equivalence le_U) :
    Equivalence (rel_extension le_T le_U) where
  refl := fun m => ⟨h_T.refl m.1, h_U.refl m.2⟩
  symm := fun h => ⟨h_T.symm h.1, h_U.symm h.2⟩
  trans := fun h1 h2 => ⟨h_T.trans h1.1 h2.1, h_U.trans h1.2 h2.2⟩

-- ═══════════════════════════════════════════════════════════════════
-- Section 2: RR - Refinement Relation (port of rr_rel.pvs)
-- ═══════════════════════════════════════════════════════════════════

/-- The refinement relation RR on pairs (t, u):
    (t, u) ∈ RR iff one of three extension conditions holds
    between Fn=(t, f(t)), Gn=(g(u), u), GFn=(g(u), f(t)) -/
def RR (le_T : T → T → Prop) (le_U : U → U → Prop)
    (f : T → U) (g : U → T) (n : T × U) : Prop :=
  let Fn : T × U := (n.1, f n.1)
  let Gn : T × U := (g n.2, n.2)
  let GFn : T × U := (g n.2, f n.1)
  rel_extension le_T le_U Fn Gn ∨
  rel_extension le_T le_U GFn Fn ∨
  rel_extension le_T le_U GFn Gn

/-- g-consistency: if le_T(t, g(u)), then (t,u) ∈ RR
    Uses second disjunct: rel_extension(GFn, Fn) where
    GFn=(g(n.2), f(n.1)), Fn=(n.1, f(n.1))
    gives le_T (g n.2) n.1 ∧ le_U (f n.1) (f n.1) -/
theorem g_consistent_with_RR (le_T : T → T → Prop) (le_U : U → U → Prop)
    (f : T → U) (g : U → T) (n : T × U)
    (h_T_symm : ∀ a b, le_T a b → le_T b a)
    (h_U_refl : ∀ x, le_U x x)
    (h : le_T n.1 (g n.2)) :
    RR le_T le_U f g n := by
  unfold RR rel_extension
  simp only
  right; left
  exact ⟨h_T_symm _ _ h, h_U_refl _⟩

/-- f-consistency: if le_U(u, f(t)), then (t,u) ∈ RR
    Uses third disjunct: rel_extension(GFn, Gn) where
    GFn=(g(n.2), f(n.1)), Gn=(g(n.2), n.2)
    gives le_T (g n.2) (g n.2) ∧ le_U (f n.1) n.2 -/
theorem f_consistent_with_RR (le_T : T → T → Prop) (le_U : U → U → Prop)
    (f : T → U) (g : U → T) (n : T × U)
    (h_T_refl : ∀ x, le_T x x)
    (h_U_symm : ∀ a b, le_U a b → le_U b a)
    (h : le_U n.2 (f n.1)) :
    RR le_T le_U f g n := by
  unfold RR rel_extension
  simp only
  right; right
  exact ⟨h_T_refl _, h_U_symm _ _ h⟩

-- ═══════════════════════════════════════════════════════════════════
-- Section 3: Homogeneous RR (T = U, as used in proof_preserving_graphs.pvs)
-- ═══════════════════════════════════════════════════════════════════

/-- Homogeneous refinement relation: same type, same equivalence -/
def rr_rel_hom (le_T : T → T → Prop) (f_abs g_con : T → T) (x y : T) : Prop :=
  RR le_T le_T f_abs g_con (x, y)

/-- Homogeneous RR with identity functions reduces to the equivalence -/
theorem rr_rel_id (le_T : T → T → Prop)
    (_h_refl : ∀ x, le_T x x)
    (x y : T) (h : le_T x y) :
    rr_rel_hom le_T id id x y := by
  unfold rr_rel_hom RR rel_extension
  dsimp
  left
  exact ⟨h, h⟩

-- ═══════════════════════════════════════════════════════════════════
-- Section 4: PPG Configuration (bridge to PPGraph.lean)
-- ═══════════════════════════════════════════════════════════════════

variable {V : Type}

/-- Full PPG configuration matching proof_preserving_graphs.pvs -/
structure PPGConfig (V : Type) where
  le_eq : V → V → Prop
  is_equiv : Equivalence le_eq
  f_abs : V → V
  g_con : V → V
  invariant : V → Prop

/-- The rr_rel derived from a PPGConfig -/
def PPGConfig.rr_rel (cfg : PPGConfig V) (x y : V) : Prop :=
  rr_rel_hom cfg.le_eq cfg.f_abs cfg.g_con x y

/-- A graph is pp_valid under a full configuration -/
def PPGConfig.valid (cfg : PPGConfig V) (G : Graph V) : Prop :=
  pp_valid G cfg.rr_rel cfg.invariant

/-- Configuration with identity abstraction/concretization
    reduces rr_rel to the equivalence relation itself -/
theorem config_id_reduces (cfg : PPGConfig V)
    (h_id_f : cfg.f_abs = id) (h_id_g : cfg.g_con = id)
    (x y : V) (h : cfg.le_eq x y) :
    cfg.rr_rel x y := by
  unfold PPGConfig.rr_rel rr_rel_hom RR rel_extension
  simp only [h_id_f, h_id_g, id]
  left
  exact ⟨h, h⟩

-- ═══════════════════════════════════════════════════════════════════
-- Section 5: Concrete PP-Edge and Validity Bridge
-- (ported from PPGraphRefinement.lean before its removal)
-- ═══════════════════════════════════════════════════════════════════

/-- A concrete pp-edge under a PPGConfig: distinct, both invariant-holding,
    and related by the config's derived rr_rel. -/
def PPGConfig.pp_edge_concrete (cfg : PPGConfig V) (x y : V) : Prop :=
  x ≠ y ∧ cfg.invariant x ∧ cfg.invariant y ∧ cfg.rr_rel x y

/-- g-consistent edge is a valid concrete pp-edge (if invariants hold) -/
theorem PPGConfig.g_consistent_pp_edge (cfg : PPGConfig V) (x y : V)
    (hne : x ≠ y) (hix : cfg.invariant x) (hiy : cfg.invariant y)
    (hg : cfg.le_eq x (cfg.g_con y)) :
    cfg.pp_edge_concrete x y :=
  ⟨hne, hix, hiy,
   g_consistent_with_RR cfg.le_eq cfg.le_eq cfg.f_abs cfg.g_con (x, y)
     (fun _ _ h => cfg.is_equiv.symm h) (fun _ => cfg.is_equiv.refl _) hg⟩

/-- f-consistent edge is a valid concrete pp-edge (if invariants hold) -/
theorem PPGConfig.f_consistent_pp_edge (cfg : PPGConfig V) (x y : V)
    (hne : x ≠ y) (hix : cfg.invariant x) (hiy : cfg.invariant y)
    (hf : cfg.le_eq y (cfg.f_abs x)) :
    cfg.pp_edge_concrete x y :=
  ⟨hne, hix, hiy,
   f_consistent_with_RR cfg.le_eq cfg.le_eq cfg.f_abs cfg.g_con (x, y)
     (fun _ => cfg.is_equiv.refl _) (fun _ _ h => cfg.is_equiv.symm h) hf⟩

/-- Bridge: a concrete pp-edge is a pp_edge in the sense of PPGraph.lean -/
theorem PPGConfig.pp_edge_concrete_is_pp_edge (cfg : PPGConfig V) (x y : V)
    (h : cfg.pp_edge_concrete x y) :
    pp_edge cfg.rr_rel cfg.invariant x y := h

/-- Bridge: a graph whose edges all satisfy pp_edge_concrete is PPGConfig.valid -/
theorem PPGConfig.graph_valid_of_concrete_edges (cfg : PPGConfig V) (G : Graph V)
    (h : ∀ x y, G.edges x y → cfg.pp_edge_concrete x y) :
    cfg.valid G :=
  fun x y he => h x y he

-- ═══════════════════════════════════════════════════════════════════
-- Verification
-- ═══════════════════════════════════════════════════════════════════

#check @rel_extension_is_equivalence
#check @RR
#check @g_consistent_with_RR
#check @f_consistent_with_RR
#check @rr_rel_hom
#check @rr_rel_id
#check @PPGConfig.rr_rel
#check @PPGConfig.valid
#check @config_id_reduces
#check @PPGConfig.pp_edge_concrete
#check @PPGConfig.g_consistent_pp_edge
#check @PPGConfig.f_consistent_pp_edge
#check @PPGConfig.pp_edge_concrete_is_pp_edge
#check @PPGConfig.graph_valid_of_concrete_edges
#check @config_id_reduces
