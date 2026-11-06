/-
  PPGraphQuotientBridge.lean
  Bridge: Spec Graph → Quotient via PP-Quotient Morphism

  A specification edge projects to a quotient edge or collapses inside a
  certification class. On certified subgraphs, an explicit noncollapse
  condition gives a genuine categorical pp_quotient carrying certification
  and the induced order. No noncollapse property is assumed implicitly.
-/

module

public import Mathlib.Tactic
public import PPGraph.Core.Graph
public import PPGraph.Certification.Parametric
public import PPGraph.Certification.ParametricQuotient
public import PPGraph.Core.Categorical

@[expose] public section

set_option linter.unusedVariables false

variable {Θ : Type} [PartialOrder Θ]
variable {D : Type}

-- ═══════════════════════════════════════════════════════════════════
-- Section 1: Quotient Graph Construction
-- ═══════════════════════════════════════════════════════════════════

/-- The quotient graph: vertices are equivalence classes,
    edges are induced by cert_le (strict) -/
def quotient_graph (F : CertFamily D Θ) : Graph (SpecQuotient F) where
  vertices := fun _ => True
  edges := fun q1 q2 => q1 ≤ q2 ∧ q1 ≠ q2
  edges_in_vertices := fun _ _ _ => ⟨trivial, trivial⟩

-- ═══════════════════════════════════════════════════════════════════
-- Section 2: Projection Preserves Edges or Collapses Them
-- ═══════════════════════════════════════════════════════════════════

/-- The projection Θ → Θ/~ maps vertices to vertices -/
theorem proj_preserves_vertices (F : CertFamily D Θ) (t : Θ)
    (h : (spec_graph Θ).vertices t) :
    (quotient_graph F).vertices (Quotient.mk (certSetoid F) t) :=
  trivial

/-- The projection preserves edge structure:
    spec_edge t1 t2 → quotient edge [t1] [t2] (or collapsed) -/
theorem proj_preserves_edges (F : CertFamily D Θ) (t1 t2 : Θ)
    (h_edge : spec_edge t1 t2) :
    (quotient_graph F).edges
      (Quotient.mk (certSetoid F) t1)
      (Quotient.mk (certSetoid F) t2) ∨
    Quotient.mk (certSetoid F) t1 = Quotient.mk (certSetoid F) t2 := by
  by_cases h_eq : Quotient.mk (certSetoid F) t1 = Quotient.mk (certSetoid F) t2
  · right; exact h_eq
  · left
    constructor
    · -- Need: [t1] ≤ [t2] in quotient, i.e., cert_le F t1 t2
      intro d h_cert
      exact master_refinement F d t1 t2 h_edge.1 h_cert
    · exact h_eq

/-- The projection is surjective (already proved) -/
theorem proj_surjective (F : CertFamily D Θ) :
    Function.Surjective (Quotient.mk (certSetoid F)) :=
  quotient_projection_surjective F

-- ═══════════════════════════════════════════════════════════════════
-- Section 3: Certification Descends to Quotient
-- ═══════════════════════════════════════════════════════════════════

/-- Certification is well-defined on the quotient graph -/
def quotient_certified (F : CertFamily D Θ) (d : D) :
    SpecQuotient F → Prop :=
  Quotient.lift (fully_certified F d)
    (fun t1 t2 h_equiv => propext (h_equiv d))

/-- Quotient certification at a class = certification at any representative -/
theorem quotient_certified_iff (F : CertFamily D Θ) (d : D) (t : Θ) :
    quotient_certified F d (Quotient.mk (certSetoid F) t) ↔
    fully_certified F d t :=
  Iff.rfl

/-- Quotient certification propagates along quotient edges -/
theorem quotient_cert_propagates (F : CertFamily D Θ) (d : D)
    (q1 q2 : SpecQuotient F)
    (h_edge : (quotient_graph F).edges q1 q2)
    (h_cert : quotient_certified F d q1) :
    quotient_certified F d q2 := by
  revert h_cert h_edge
  refine Quotient.inductionOn₂ q1 q2 ?_
  intro t1 t2 h_edge h_cert
  exact h_edge.1 d h_cert

-- ═══════════════════════════════════════════════════════════════════
-- Section 4: Categorical Quotient on Certified Subgraphs
-- ═══════════════════════════════════════════════════════════════════

/-- Restrict the quotient graph to classes certifying the fixed datum. -/
def certified_quotient_graph (F : CertFamily D Θ) (d : D) :
    Graph (SpecQuotient F) where
  vertices := quotient_certified F d
  edges := fun q1 q2 => q1 ≤ q2 ∧ q1 ≠ q2 ∧ quotient_certified F d q1
  edges_in_vertices := by
    intro q1 q2 ⟨hle, hne, hcert⟩
    exact ⟨hcert, quotient_cert_propagates F d q1 q2 ⟨hle, hne⟩ hcert⟩

/-- Certification and the quotient order make every certified quotient edge
    a pp-edge under the descended certificate predicate. -/
theorem certified_quotient_pp_valid (F : CertFamily D Θ) (d : D) :
    pp_valid (certified_quotient_graph F d) (fun q1 q2 => q1 ≤ q2)
      (quotient_certified F d) := by
  intro q1 q2 ⟨hle, hne, hcert⟩
  exact ⟨hne, hcert, quotient_cert_propagates F d q1 q2 ⟨hle, hne⟩ hcert, hle⟩

/-- No certified source edge may collapse inside a certification class. -/
def certified_edges_separate_classes (F : CertFamily D Θ) (d : D) : Prop :=
  ∀ t1 t2, (certified_subgraph Θ F d).edges t1 t2 → ¬ cert_equiv F t1 t2

/-- Under noncollapse, projection is a categorical pp_quotient between the
    certified graphs, preserving the fixed datum's certification and order. -/
theorem certified_proj_is_pp_quotient (F : CertFamily D Θ) (d : D)
    (h_sep : certified_edges_separate_classes F d) :
    pp_quotient (Quotient.mk (certSetoid F))
      (certified_subgraph Θ F d) (certified_quotient_graph F d)
      spec_rr (fully_certified F d) (fun q1 q2 : SpecQuotient F => q1 ≤ q2)
      (quotient_certified F d) := by
  refine ⟨⟨?_, ?_⟩, proj_surjective F⟩
  · intro t ht
    exact ht
  · intro t1 t2 ⟨he, hpp⟩
    have hne : Quotient.mk (certSetoid F) t1 ≠ Quotient.mk (certSetoid F) t2 := by
      intro h_eq
      exact h_sep t1 t2 he (Quotient.exact h_eq)
    have h_image : (quotient_graph F).edges
        (Quotient.mk (certSetoid F) t1) (Quotient.mk (certSetoid F) t2) :=
      (proj_preserves_edges F t1 t2 he.1).resolve_right hne
    exact ⟨⟨h_image.1, hne, hpp.2.1⟩,
      hne, hpp.2.1, hpp.2.2.1, h_image.1⟩

-- ═══════════════════════════════════════════════════════════════════
-- Verification
-- ═══════════════════════════════════════════════════════════════════

#check @quotient_graph
#check @proj_preserves_vertices
#check @proj_preserves_edges
#check @proj_surjective
#check @quotient_certified
#check @quotient_certified_iff
#check @quotient_cert_propagates
#check @certified_quotient_graph
#check @certified_quotient_pp_valid
#check @certified_edges_separate_classes
#check @certified_proj_is_pp_quotient
