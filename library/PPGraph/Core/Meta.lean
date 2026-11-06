/-
  Meta Proof-Preserving Graphs: Graphs over Refinement Relations (Lean 4)

  A PPG where nodes ARE refinement relations (rr_rel instances)
  and edges are compatibility transformations between them.

  Key idea: if an implementation is correct under rr_rel_1, and
  there exists a meta-edge to rr_rel_2, then the implementation
  remains correct under rr_rel_2. This is backward compatibility
  formalized as a proof-preserving graph.

  Structure:
    Level 0: elements related by rr_rel
    Level 1: graphs validated by pp_valid
    Level 2: meta-graph over rr_rel instances (THIS FILE)

  A specification-versioning application must supply concrete configurations
  and prove their compatibility. The results below transport correctness
  along that supplied relation inclusion.
-/

module

public import Mathlib.Tactic
public import PPGraph.Core.Graph
public import PPGraph.Core.RR

@[expose] public section

-- ═══════════════════════════════════════════════════════════════════
-- Section 1: Refinement Configuration (Node Type)
-- ═══════════════════════════════════════════════════════════════════

-- An equivalence relation
structure EquivRel (T : Type) where
  rel : T → T → Prop
  refl : ∀ x, rel x x
  symm : ∀ x y, rel x y → rel y x
  trans : ∀ x y z, rel x y → rel y z → rel x z

-- A refinement configuration: one complete rr_rel instance
-- This is a NODE in our meta-graph
structure RefinementConfig (T : Type) where
  le : EquivRel T
  f_abs : T → T
  g_con : T → T

-- The refinement relation induced by a config
def rr_of {T : Type} (cfg : RefinementConfig T) (x y : T) : Prop :=
  (cfg.le.rel x (cfg.g_con y)) ∨
  (cfg.le.rel (cfg.g_con y) x ∧ cfg.le.rel (cfg.f_abs x) (cfg.f_abs x)) ∨
  (cfg.le.rel (cfg.g_con y) (cfg.g_con y) ∧ cfg.le.rel (cfg.f_abs x) y)

/-- The meta relation and the core homogeneous RR coincide. The first meta
    disjunct is absorbed by the core's second disjunct using the bundled
    symmetry and reflexivity laws. -/
theorem rr_of_iff_rr_rel_hom {T : Type} (cfg : RefinementConfig T) (x y : T) :
    rr_of cfg x y ↔ rr_rel_hom cfg.le.rel cfg.f_abs cfg.g_con x y := by
  unfold rr_of rr_rel_hom RR rel_extension
  dsimp only
  constructor
  · rintro (h | h | h)
    · exact Or.inr (Or.inl ⟨cfg.le.symm _ _ h, cfg.le.refl _⟩)
    · exact Or.inr (Or.inl h)
    · exact Or.inr (Or.inr h)
  · rintro (h | h | h)
    · exact Or.inl h.1
    · exact Or.inr (Or.inl h)
    · exact Or.inr (Or.inr h)

-- ═══════════════════════════════════════════════════════════════════
-- Section 2: Meta-Invariant (What makes a node "valid")
-- ═══════════════════════════════════════════════════════════════════

-- The first two conjuncts record reflexivity at the image points and follow
-- from the bundled equivalence. The last conjunct separately requires the
-- induced refinement relation to be reflexive.
def config_valid {T : Type} (cfg : RefinementConfig T) : Prop :=
  -- Reflexivity at the image of g_con; no relation to y is asserted here.
  (∀ y : T, cfg.le.rel (cfg.g_con y) (cfg.g_con y)) ∧
  -- Reflexivity at the image of f_abs; no relation to x is asserted here.
  (∀ x : T, cfg.le.rel (cfg.f_abs x) (cfg.f_abs x)) ∧
  -- Reflexivity: every element is related to itself
  (∀ x : T, rr_of cfg x x)

-- ═══════════════════════════════════════════════════════════════════
-- Section 3: Meta-Edge (Compatibility between configs)
-- ═══════════════════════════════════════════════════════════════════

-- Two configs are COMPATIBLE if: any pair related under cfg1
-- is also related under cfg2. This is the meta-edge condition.
-- "Upgrading from spec v1 to spec v2 preserves all existing relations."
def configs_compatible {T : Type} (cfg1 cfg2 : RefinementConfig T) : Prop :=
  ∀ x y : T, rr_of cfg1 x y → rr_of cfg2 x y

/-- Keeping abstraction and concretization fixed while extending the underlying
    equivalence preserves every old refinement pair. This constructs
    compatibility from the base relation instead of assuming compatibility. -/
theorem configs_compatible_of_rel_inclusion {T : Type}
    (cfg1 cfg2 : RefinementConfig T)
    (h_rel : ∀ x y, cfg1.le.rel x y → cfg2.le.rel x y)
    (h_f : cfg1.f_abs = cfg2.f_abs) (h_g : cfg1.g_con = cfg2.g_con) :
    configs_compatible cfg1 cfg2 := by
  intro x y h
  unfold rr_of at h ⊢
  rw [h_f, h_g] at h
  rcases h with h | h | h
  · exact Or.inl (h_rel _ _ h)
  · exact Or.inr (Or.inl ⟨h_rel _ _ h.1, h_rel _ _ h.2⟩)
  · exact Or.inr (Or.inr ⟨h_rel _ _ h.1, h_rel _ _ h.2⟩)

-- Meta pp-edge: both configs are valid AND compatible
def meta_pp_edge {T : Type} (cfg1 cfg2 : RefinementConfig T) : Prop :=
  cfg1 ≠ cfg2 ∧ config_valid cfg1 ∧ config_valid cfg2 ∧
  configs_compatible cfg1 cfg2

-- ═══════════════════════════════════════════════════════════════════
-- Section 4: Meta-Graph
-- ═══════════════════════════════════════════════════════════════════

-- The meta-graph over refinement configurations
structure MetaPPGraph (T : Type) where
  configs : RefinementConfig T → Prop
  edges : RefinementConfig T → RefinementConfig T → Prop
  edges_in_configs : ∀ c1 c2, edges c1 c2 → configs c1 ∧ configs c2

-- Meta-graph is pp-valid if every edge is a meta_pp_edge
def meta_pp_valid {T : Type} (G : MetaPPGraph T) : Prop :=
  ∀ c1 c2, G.edges c1 c2 → meta_pp_edge c1 c2

-- ═══════════════════════════════════════════════════════════════════
-- Section 5: Theorems
-- ═══════════════════════════════════════════════════════════════════

variable {T : Type}

-- T1: Compatibility is reflexive (every config is compatible with itself)
theorem compatible_refl (cfg : RefinementConfig T) :
    configs_compatible cfg cfg :=
  fun _ _ h => h

-- T2: Compatibility is transitive (upgrade chains compose)
theorem compatible_trans (cfg1 cfg2 cfg3 : RefinementConfig T)
    (h12 : configs_compatible cfg1 cfg2)
    (h23 : configs_compatible cfg2 cfg3) :
    configs_compatible cfg1 cfg3 :=
  fun x y h => h23 x y (h12 x y h)

-- T3: If meta-edge exists, all relations in source persist in target
theorem meta_edge_preserves_relations (cfg1 cfg2 : RefinementConfig T)
    (he : meta_pp_edge cfg1 cfg2) (x y : T)
    (h : rr_of cfg1 x y) : rr_of cfg2 x y :=
  he.2.2.2 x y h

-- T4: Invalid config has no outgoing meta-edges
theorem invalid_config_isolated (cfg1 cfg2 : RefinementConfig T)
    (h_invalid : ¬ config_valid cfg1) :
    ¬ meta_pp_edge cfg1 cfg2 :=
  fun he => h_invalid he.2.1

-- T5: Invalid config has no incoming meta-edges
theorem invalid_config_no_incoming (cfg1 cfg2 : RefinementConfig T)
    (h_invalid : ¬ config_valid cfg2) :
    ¬ meta_pp_edge cfg1 cfg2 :=
  fun he => h_invalid he.2.2.1

-- T6: Meta pp-valid graph only contains valid configs at edge endpoints
theorem meta_valid_configs (G : MetaPPGraph T)
    (hv : meta_pp_valid G) (c1 c2 : RefinementConfig T)
    (he : G.edges c1 c2) :
    config_valid c1 ∧ config_valid c2 :=
  ⟨(hv c1 c2 he).2.1, (hv c1 c2 he).2.2.1⟩

-- T7: Chain of compatible upgrades preserves relations end-to-end
-- If cfg1 → cfg2 → cfg3 all via meta-edges, then rr_of cfg1 implies rr_of cfg3
theorem upgrade_chain_preserves (cfg1 cfg2 cfg3 : RefinementConfig T)
    (h12 : meta_pp_edge cfg1 cfg2) (h23 : meta_pp_edge cfg2 cfg3)
    (x y : T) (h : rr_of cfg1 x y) :
    rr_of cfg3 x y :=
  h23.2.2.2 x y (h12.2.2.2 x y h)

-- T8: Relation inclusion defines a preorder on all configurations
-- (reflexive + transitive, not necessarily antisymmetric)
theorem compatibility_preorder :
    (∀ cfg : RefinementConfig T, configs_compatible cfg cfg) ∧
    (∀ cfg1 cfg2 cfg3 : RefinementConfig T,
      configs_compatible cfg1 cfg2 → configs_compatible cfg2 cfg3 →
      configs_compatible cfg1 cfg3) :=
  ⟨compatible_refl, compatible_trans⟩

-- ═══════════════════════════════════════════════════════════════════
-- Section 6: Backward Compatibility as Meta-PPG Property
-- ═══════════════════════════════════════════════════════════════════

-- An implementation is "correct under cfg" if it satisfies rr_of for given pairs
def implementation_correct {T : Type} (cfg : RefinementConfig T)
    (impl_pairs : T → T → Prop) : Prop :=
  ∀ x y, impl_pairs x y → rr_of cfg x y

-- T9: Backward compatibility theorem:
-- If implementation is correct under cfg1, and cfg1 → cfg2 is a meta-edge,
-- then implementation is correct under cfg2
theorem backward_compatible (cfg1 cfg2 : RefinementConfig T)
    (impl_pairs : T → T → Prop)
    (he : meta_pp_edge cfg1 cfg2)
    (h_correct : implementation_correct cfg1 impl_pairs) :
    implementation_correct cfg2 impl_pairs :=
  fun x y hp => he.2.2.2 x y (h_correct x y hp)

-- T10: Contrapositive: if implementation FAILS under cfg2,
-- then either it failed under cfg1 OR cfg1→cfg2 is not a meta-edge
theorem failure_propagates (cfg1 cfg2 : RefinementConfig T)
    (impl_pairs : T → T → Prop)
    (he : meta_pp_edge cfg1 cfg2)
    (h_fail : ¬ implementation_correct cfg2 impl_pairs) :
    ¬ implementation_correct cfg1 impl_pairs := by
  intro h_correct
  exact h_fail (backward_compatible cfg1 cfg2 impl_pairs he h_correct)

-- ═══════════════════════════════════════════════════════════════════
-- Verification
-- ═══════════════════════════════════════════════════════════════════

#check @compatible_refl
#check @rr_of_iff_rr_rel_hom
#check @configs_compatible_of_rel_inclusion
#check @compatible_trans
#check @meta_edge_preserves_relations
#check @invalid_config_isolated
#check @invalid_config_no_incoming
#check @meta_valid_configs
#check @upgrade_chain_preserves
#check @compatibility_preorder
#check @backward_compatible
#check @failure_propagates
