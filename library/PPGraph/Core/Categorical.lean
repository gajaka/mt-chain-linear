/-
  Categorical Proof-Preserving Graphs (Lean 4)
  Port of categorical_pp_graphs[T, U] from pp_graphs_extended.pvs

  Morphisms between PP-graphs of potentially different types.
  Formalizes structure-preserving maps, embeddings, quotients,
  refinement between graphs, and simulation relations.

  The structure: refinement at the GRAPH level is the natural
  generalization of rr_rel at the ELEMENT level. A concrete
  graph refines an abstract graph via a quotient morphism.
-/

module

public import Mathlib.Tactic
public import PPGraph.Core.Graph

@[expose] public section

-- ═══════════════════════════════════════════════════════════════════
-- Section 1: PP-Morphism
-- ═══════════════════════════════════════════════════════════════════

variable {T U : Type}

-- PP-Morphism: map preserving vertex membership AND pp-edge structure
def pp_morphism (f : T → U) (G1 : Graph T) (G2 : Graph U)
    (rr_T : T → T → Prop) (inv_T : T → Prop)
    (rr_U : U → U → Prop) (inv_U : U → Prop) : Prop :=
  (∀ x, G1.vertices x → G2.vertices (f x)) ∧
  (∀ x y, G1.edges x y ∧ pp_edge rr_T inv_T x y →
    G2.edges (f x) (f y) ∧ pp_edge rr_U inv_U (f x) (f y))

-- ═══════════════════════════════════════════════════════════════════
-- Section 2: PP-Embedding (injective morphism)
-- ═══════════════════════════════════════════════════════════════════

def pp_embedding (f : T → U) (G1 : Graph T) (G2 : Graph U)
    (rr_T : T → T → Prop) (inv_T : T → Prop)
    (rr_U : U → U → Prop) (inv_U : U → Prop) : Prop :=
  pp_morphism f G1 G2 rr_T inv_T rr_U inv_U ∧ Function.Injective f

-- ═══════════════════════════════════════════════════════════════════
-- Section 3: PP-Quotient (surjective morphism = abstraction)
-- ═══════════════════════════════════════════════════════════════════

def pp_quotient (f : T → U) (G1 : Graph T) (G2 : Graph U)
    (rr_T : T → T → Prop) (inv_T : T → Prop)
    (rr_U : U → U → Prop) (inv_U : U → Prop) : Prop :=
  pp_morphism f G1 G2 rr_T inv_T rr_U inv_U ∧ Function.Surjective f

-- ═══════════════════════════════════════════════════════════════════
-- Section 4: Graph-Level Refinement
-- ═══════════════════════════════════════════════════════════════════

-- G1 refines G2 if there exists a quotient from G1 to G2
-- (concrete graph refines abstract graph)
def pp_refines (G1 : Graph T) (G2 : Graph U)
    (rr_T : T → T → Prop) (inv_T : T → Prop)
    (rr_U : U → U → Prop) (inv_U : U → Prop) : Prop :=
  ∃ f : T → U, pp_quotient f G1 G2 rr_T inv_T rr_U inv_U

-- ═══════════════════════════════════════════════════════════════════
-- Section 5: Simulation (Abstraction-Concretization pair)
-- ═══════════════════════════════════════════════════════════════════

-- f: concrete → abstract (abstraction)
-- g: abstract → concrete (concretization)
-- g ∘ f = id on concrete vertices (round-trip)
def simulation (f : T → U) (g : U → T) (G1 : Graph T) (G2 : Graph U)
    (rr_T : T → T → Prop) (inv_T : T → Prop)
    (rr_U : U → U → Prop) (inv_U : U → Prop) : Prop :=
  pp_morphism f G1 G2 rr_T inv_T rr_U inv_U ∧
  (∀ u, G2.vertices u → G1.vertices (g u)) ∧
  (∀ x, G1.vertices x → g (f x) = x)

-- ═══════════════════════════════════════════════════════════════════
-- Section 6: Theorems
-- ═══════════════════════════════════════════════════════════════════

-- T1: Embedding is a morphism
theorem embedding_is_morphism (f : T → U) (G1 : Graph T) (G2 : Graph U)
    (rr_T : T → T → Prop) (inv_T : T → Prop)
    (rr_U : U → U → Prop) (inv_U : U → Prop)
    (h : pp_embedding f G1 G2 rr_T inv_T rr_U inv_U) :
    pp_morphism f G1 G2 rr_T inv_T rr_U inv_U :=
  h.1

-- T2: Quotient is a morphism
theorem quotient_is_morphism (f : T → U) (G1 : Graph T) (G2 : Graph U)
    (rr_T : T → T → Prop) (inv_T : T → Prop)
    (rr_U : U → U → Prop) (inv_U : U → Prop)
    (h : pp_quotient f G1 G2 rr_T inv_T rr_U inv_U) :
    pp_morphism f G1 G2 rr_T inv_T rr_U inv_U :=
  h.1

-- T3: Morphism preserves pp-validity (edges in source map to pp-edges in target)
theorem morphism_preserves_pp_edges (f : T → U) (G1 : Graph T) (G2 : Graph U)
    (rr_T : T → T → Prop) (inv_T : T → Prop)
    (rr_U : U → U → Prop) (inv_U : U → Prop)
    (hm : pp_morphism f G1 G2 rr_T inv_T rr_U inv_U)
    (hv : pp_valid G1 rr_T inv_T)
    (x y : T) (he : G1.edges x y) :
    pp_edge rr_U inv_U (f x) (f y) :=
  (hm.2 x y ⟨he, hv x y he⟩).2

-- T4: Simulation implies morphism
theorem simulation_is_morphism (f : T → U) (g : U → T)
    (G1 : Graph T) (G2 : Graph U)
    (rr_T : T → T → Prop) (inv_T : T → Prop)
    (rr_U : U → U → Prop) (inv_U : U → Prop)
    (h : simulation f g G1 G2 rr_T inv_T rr_U inv_U) :
    pp_morphism f G1 G2 rr_T inv_T rr_U inv_U :=
  h.1

-- T5: Simulation implies refinement (when f is surjective)
theorem simulation_implies_refinement (f : T → U) (g : U → T)
    (G1 : Graph T) (G2 : Graph U)
    (rr_T : T → T → Prop) (inv_T : T → Prop)
    (rr_U : U → U → Prop) (inv_U : U → Prop)
    (hs : simulation f g G1 G2 rr_T inv_T rr_U inv_U)
    (hsurj : Function.Surjective f) :
    pp_refines G1 G2 rr_T inv_T rr_U inv_U :=
  ⟨f, hs.1, hsurj⟩

-- T6: Simulation round-trip: g(f(x)) = x for all vertices
theorem simulation_roundtrip (f : T → U) (g : U → T)
    (G1 : Graph T) (G2 : Graph U)
    (rr_T : T → T → Prop) (inv_T : T → Prop)
    (rr_U : U → U → Prop) (inv_U : U → Prop)
    (hs : simulation f g G1 G2 rr_T inv_T rr_U inv_U)
    (x : T) (hx : G1.vertices x) :
    g (f x) = x :=
  hs.2.2 x hx

-- T7: Morphism composition: if f: G1→G2 and g: G2→G3, then g∘f: G1→G3
theorem morphism_compose {W : Type}
    (f : T → U) (g : U → W)
    (G1 : Graph T) (G2 : Graph U) (G3 : Graph W)
    (rr_T : T → T → Prop) (inv_T : T → Prop)
    (rr_U : U → U → Prop) (inv_U : U → Prop)
    (rr_W : W → W → Prop) (inv_W : W → Prop)
    (hf : pp_morphism f G1 G2 rr_T inv_T rr_U inv_U)
    (hg : pp_morphism g G2 G3 rr_U inv_U rr_W inv_W) :
    pp_morphism (g ∘ f) G1 G3 rr_T inv_T rr_W inv_W := by
  constructor
  · intro x hx
    exact hg.1 (f x) (hf.1 x hx)
  · intro x y ⟨he, hpp⟩
    have h2 := hf.2 x y ⟨he, hpp⟩
    exact hg.2 (f x) (f y) h2

-- T8: Identity is always a morphism (T = U case)
theorem id_morphism (G : Graph T)
    (rr_T : T → T → Prop) (inv_T : T → Prop) :
    pp_morphism id G G rr_T inv_T rr_T inv_T :=
  ⟨fun _ hx => hx, fun _ _ h => h⟩

-- T9: Identity is an embedding
theorem id_embedding (G : Graph T)
    (rr_T : T → T → Prop) (inv_T : T → Prop) :
    pp_embedding id G G rr_T inv_T rr_T inv_T :=
  ⟨id_morphism G rr_T inv_T, Function.injective_id⟩

-- T10: Embedding composition preserves injectivity
theorem embedding_compose {W : Type}
    (f : T → U) (g : U → W)
    (G1 : Graph T) (G2 : Graph U) (G3 : Graph W)
    (rr_T : T → T → Prop) (inv_T : T → Prop)
    (rr_U : U → U → Prop) (inv_U : U → Prop)
    (rr_W : W → W → Prop) (inv_W : W → Prop)
    (hf : pp_embedding f G1 G2 rr_T inv_T rr_U inv_U)
    (hg : pp_embedding g G2 G3 rr_U inv_U rr_W inv_W) :
    pp_embedding (g ∘ f) G1 G3 rr_T inv_T rr_W inv_W :=
  ⟨morphism_compose f g G1 G2 G3 rr_T inv_T rr_U inv_U rr_W inv_W hf.1 hg.1,
   Function.Injective.comp hg.2 hf.2⟩

-- ═══════════════════════════════════════════════════════════════════
-- Verification
-- ═══════════════════════════════════════════════════════════════════

#check @embedding_is_morphism
#check @quotient_is_morphism
#check @morphism_preserves_pp_edges
#check @simulation_is_morphism
#check @simulation_implies_refinement
#check @simulation_roundtrip
#check @morphism_compose
#check @id_morphism
#check @id_embedding
#check @embedding_compose
