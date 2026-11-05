/-
  PPGraphSelection.lean
  Hierarchical Representative Selection via Family of Morphism Pairs

  Given a family of (f_i, g_i) pairs, each inducing an equivalence
  on the codomain, the finest equivalence (intersection of all)
  gives the canonical representative selection.

  Key: ∼* = ⋂ᵢ ∼ᵢ. Element canonical w.r.t. ∼* survives all views.
-/

module

public import Mathlib.Tactic
public import PPGraph.Core.Graph
public import PPGraph.Core.Categorical
public import PPGraph.Certification.Parametric

@[expose] public section

set_option linter.unusedVariables false

variable {T U : Type}

-- ═══════════════════════════════════════════════════════════════════
-- Section 1: Single Morphism Pair Induces Equivalence (via pullback)
-- ═══════════════════════════════════════════════════════════════════

/-- A morphism pair: f abstracts (T→U), g concretizes (U→T),
    eq_T is an equivalence on the concrete domain T.
    The induced equivalence on U is the pullback of eq_T along g:
    u1 ~ u2 iff eq_T (g u1) (g u2). -/
structure MorphPair (T U : Type) where
  f : T → U
  g : U → T
  eq_T : T → T → Prop
  is_equiv : Equivalence eq_T

/-- The equivalence induced on U by pulling back eq_T along g:
    two abstract elements are equivalent if their concretizations
    are equivalent in T. -/
def induced_equiv (mp : MorphPair T U) (u1 u2 : U) : Prop :=
  mp.eq_T (mp.g u1) (mp.g u2)

/-- Pullback of an equivalence is an equivalence -/
theorem induced_equiv_is_equiv (mp : MorphPair T U) :
    Equivalence (induced_equiv mp) where
  refl := fun u => mp.is_equiv.refl (mp.g u)
  symm := fun h => mp.is_equiv.symm h
  trans := fun h1 h2 => mp.is_equiv.trans h1 h2

/-- f-g consistency: f and g are compatible with eq_T.
    Round-trip g(f(t)) is equivalent to t. -/
def fg_consistent (mp : MorphPair T U) : Prop :=
  ∀ t : T, mp.eq_T t (mp.g (mp.f t))

/-- Under fg_consistent, f(t1) and f(t2) are induced-equivalent
    whenever t1 and t2 are eq_T-equivalent -/
theorem f_preserves_equiv (mp : MorphPair T U)
    (h_fg : fg_consistent mp) (t1 t2 : T)
    (h_eq : mp.eq_T t1 t2) :
    induced_equiv mp (mp.f t1) (mp.f t2) := by
  unfold induced_equiv
  have h1 : mp.eq_T (mp.g (mp.f t1)) t1 := mp.is_equiv.symm (h_fg t1)
  have h2 : mp.eq_T t2 (mp.g (mp.f t2)) := h_fg t2
  exact mp.is_equiv.trans (mp.is_equiv.trans h1 h_eq) h2

/-- Under fg_consistent, g is a section of f up to equivalence:
    f(g(u)) is induced-equivalent to u -/
theorem g_section (mp : MorphPair T U)
    (h_fg : fg_consistent mp) (u : U) :
    induced_equiv mp (mp.f (mp.g u)) u := by
  unfold induced_equiv
  exact mp.is_equiv.symm (h_fg (mp.g u))

-- ═══════════════════════════════════════════════════════════════════
-- Section 2: Family of Morphism Pairs
-- ═══════════════════════════════════════════════════════════════════

/-- A family of morphism pairs (Set-based, matching PVS port) -/
structure MorphFamily (T U : Type) where
  pairs : Set (MorphPair T U)
  nonempty : ∃ mp, mp ∈ pairs

/-- The finest equivalence: intersection of all induced equivalences.
    u1 ~* u2 iff u1 ~ᵢ u2 for ALL pairs in the family -/
def finest_equiv (F : MorphFamily T U) (u1 u2 : U) : Prop :=
  ∀ mp ∈ F.pairs, induced_equiv mp u1 u2

/-- finest_equiv is reflexive -/
theorem finest_equiv_refl (F : MorphFamily T U) (u : U) :
    finest_equiv F u u := by
  intro mp _
  exact (induced_equiv_is_equiv mp).refl u

/-- finest_equiv is symmetric -/
theorem finest_equiv_symm (F : MorphFamily T U) (u1 u2 : U)
    (h : finest_equiv F u1 u2) :
    finest_equiv F u2 u1 := by
  intro mp hmp
  exact (induced_equiv_is_equiv mp).symm (h mp hmp)

/-- finest_equiv is transitive -/
theorem finest_equiv_trans (F : MorphFamily T U) (u1 u2 u3 : U)
    (h12 : finest_equiv F u1 u2) (h23 : finest_equiv F u2 u3) :
    finest_equiv F u1 u3 := by
  intro mp hmp
  exact (induced_equiv_is_equiv mp).trans (h12 mp hmp) (h23 mp hmp)

/-- finest_equiv is an equivalence -/
theorem finest_equiv_is_equivalence (F : MorphFamily T U) :
    Equivalence (finest_equiv F) where
  refl := finest_equiv_refl F
  symm := finest_equiv_symm F _ _
  trans := finest_equiv_trans F _ _ _

/-- Setoid from the finest equivalence -/
def finestSetoid (F : MorphFamily T U) : Setoid U where
  r := finest_equiv F
  iseqv := finest_equiv_is_equivalence F

-- ═══════════════════════════════════════════════════════════════════
-- Section 3: Finest Equivalence Refines Each Individual One
-- ═══════════════════════════════════════════════════════════════════

/-- finest_equiv refines each individual equivalence -/
theorem finest_refines_each (F : MorphFamily T U)
    (mp : MorphPair T U) (hmp : mp ∈ F.pairs)
    (u1 u2 : U) (h : finest_equiv F u1 u2) :
    induced_equiv mp u1 u2 :=
  h mp hmp

/-- finest_equiv is the coarsest equivalence that refines all -/
theorem finest_is_coarsest_refinement (F : MorphFamily T U)
    (eq_R : U → U → Prop)
    (h_refines : ∀ mp ∈ F.pairs, ∀ u1 u2, eq_R u1 u2 → induced_equiv mp u1 u2)
    (u1 u2 : U) (h : eq_R u1 u2) :
    finest_equiv F u1 u2 := by
  intro mp hmp
  exact h_refines mp hmp u1 u2 h

-- ═══════════════════════════════════════════════════════════════════
-- Section 4: Canonical Representative (survives all views)
-- ═══════════════════════════════════════════════════════════════════

/-- A property on U -/
def Property (U : Type) := U → Prop

/-- An element is canonical in the finest class if it satisfies
    a selection property that is uniform within finest classes -/
def is_finest_canonical (F : MorphFamily T U)
    (sel : Property U) (u : U) : Prop :=
  sel u ∧ ∀ u' : U, finest_equiv F u u' → sel u' → u = u'

/-- If selection property is unique within finest classes,
    canonical representative is unique -/
theorem finest_canonical_unique (F : MorphFamily T U)
    (sel : Property U) (u1 u2 : U)
    (h1 : is_finest_canonical F sel u1)
    (h2 : is_finest_canonical F sel u2)
    (h_equiv : finest_equiv F u1 u2) :
    u1 = u2 :=
  h1.2 u2 h_equiv h2.1

-- ═══════════════════════════════════════════════════════════════════
-- Section 5: Proper CertFamily Instance
-- ═══════════════════════════════════════════════════════════════════

-- Θ = Set of lenses (ordered by reverse inclusion: bigger set = stricter).
-- Certificate: "u passes all lenses in S".
-- master_refinement gives lens_superset_refines for free.

/-- Each lens defines a predicate on U: "equivalent to target" -/
def lens_pred (mp : MorphPair T U) (target : U) (u : U) : Prop :=
  induced_equiv mp u target

/-- Certificate over a set of lenses: u passes ALL lenses in S -/
def lens_family_cert (target : U) (u : U) (S : Finset (MorphPair T U)) : Prop :=
  ∀ mp ∈ S, lens_pred mp target u

/-- lens_family_cert is monotone w.r.t. reverse inclusion:
    if S1 ⊇ S2 (S1 is stricter) and u passes S1, then u passes S2.
    This IS master_refinement for the lens CertFamily. -/
theorem lens_cert_monotone [DecidableEq (MorphPair T U)]
    (target : U) (u : U) (S1 S2 : Finset (MorphPair T U))
    (h_sub : S2 ⊆ S1)
    (h_pass : lens_family_cert target u S1) :
    lens_family_cert target u S2 :=
  fun mp hmp => h_pass mp (h_sub hmp)

-- ═══════════════════════════════════════════════════════════════════
-- Section 5b: Formal CertFamily Instance via OrderDual
-- ═══════════════════════════════════════════════════════════════════

-- Θ = (Finset (MorphPair T U))ᵒᵈ with the standard dual order.
-- In OrderDual: S1 ≤ S2 in dual ↔ S2 ⊆ S1 in original.
-- So "larger in dual order" = "fewer lenses" = "weaker spec".

/-- The single certificate for the lens CertFamily:
    data u is certified at spec level S iff it passes all lenses in S -/
def lens_certificate [DecidableEq (MorphPair T U)] (target : U) :
    Certificate U (Finset (MorphPair T U))ᵒᵈ :=
  fun u S => lens_family_cert target u (OrderDual.ofDual S)

/-- The lens certificate is monotone w.r.t. the dual order -/
theorem lens_certificate_monotone [DecidableEq (MorphPair T U)] (target : U) :
    monotone_cert (lens_certificate target : Certificate U (Finset (MorphPair T U))ᵒᵈ) := by
  intro u S1 S2 h_le h_cert
  -- h_le : S1 ≤ S2 in dual, i.e., ofDual S2 ⊆ ofDual S1
  exact lens_cert_monotone target u (OrderDual.ofDual S1) (OrderDual.ofDual S2)
    h_le h_cert

/-- The lens CertFamily: one certificate, monotone over dual-ordered Finsets -/
def lensCertFamily [DecidableEq (MorphPair T U)] (target : U) :
    CertFamily U (Finset (MorphPair T U))ᵒᵈ where
  certs := [lens_certificate target]
  all_monotone := by
    intro C hC
    simp at hC
    subst hC
    exact lens_certificate_monotone target

/-- master_refinement applied to the lens CertFamily:
    S1 ≤ S2 (dual) ∧ certified at S1 → certified at S2 -/
theorem lens_master_refinement [DecidableEq (MorphPair T U)] (target : U)
    (u : U) (S1 S2 : (Finset (MorphPair T U))ᵒᵈ)
    (h_le : S1 ≤ S2)
    (h_cert : fully_certified (lensCertFamily target) u S1) :
    fully_certified (lensCertFamily target) u S2 :=
  master_refinement (lensCertFamily target) u S1 S2 h_le h_cert

/-- Conjunction of all lenses in the family = finest_equiv -/
theorem all_lenses_iff_finest (F : MorphFamily T U) (target : U) (u : U) :
    (∀ mp ∈ F.pairs, lens_pred mp target u) ↔ finest_equiv F u target :=
  Iff.rfl

/-- Each lens predicate is reflexive at target -/
theorem lens_pred_refl (mp : MorphPair T U) (target : U) :
    lens_pred mp target target :=
  (induced_equiv_is_equiv mp).refl target

/-- If u passes all lenses and u' is finest-equivalent to u,
    then u' also passes all lenses (certification propagates) -/
theorem lens_propagates (F : MorphFamily T U) (target : U) (u u' : U)
    (h_finest : finest_equiv F u u')
    (h_pass : ∀ mp ∈ F.pairs, lens_pred mp target u) :
    ∀ mp ∈ F.pairs, lens_pred mp target u' := by
  intro mp hmp
  unfold lens_pred induced_equiv
  have h_u : mp.eq_T (mp.g u) (mp.g target) := h_pass mp hmp
  have h_uu' : mp.eq_T (mp.g u) (mp.g u') := (h_finest mp hmp)
  exact mp.is_equiv.trans (mp.is_equiv.symm h_uu') h_u

-- ═══════════════════════════════════════════════════════════════════
-- Section 6: PPG Validity on Finest Quotient
-- ═══════════════════════════════════════════════════════════════════

/-- The finest quotient type -/
def FinestQuotient (F : MorphFamily T U) := Quotient (finestSetoid F)

/-- Graph on the finest quotient: edges from refinement between classes -/
def finest_graph (F : MorphFamily T U) (edge_rel : U → U → Prop) :
    Graph (FinestQuotient F) where
  vertices := fun _ => True
  edges := fun q1 q2 =>
    q1 ≠ q2 ∧ ∃ u1 u2 : U,
      Quotient.mk (finestSetoid F) u1 = q1 ∧
      Quotient.mk (finestSetoid F) u2 = q2 ∧
      edge_rel u1 u2
  edges_in_vertices := fun _ _ _ => ⟨trivial, trivial⟩

/-- An invariant on U that respects finest_equiv descends to quotient -/
def quotient_invariant (F : MorphFamily T U)
    (inv : U → Prop) (h_resp : ∀ u1 u2, finest_equiv F u1 u2 → (inv u1 ↔ inv u2)) :
    FinestQuotient F → Prop :=
  Quotient.lift inv (fun u1 u2 h => propext (h_resp u1 u2 h))

/-- A relation respected in both arguments descends to the finest quotient.
    The reverse implication uses symmetry of the finest equivalence. -/
def quotient_rr (F : MorphFamily T U) (rr_rel : U → U → Prop)
    (h_resp : ∀ u1 u1' u2 u2',
      finest_equiv F u1 u1' → finest_equiv F u2 u2' →
      rr_rel u1 u2 → rr_rel u1' u2')
    (q1 q2 : FinestQuotient F) : Prop :=
  Quotient.lift₂ rr_rel
    (fun u1 u2 u1' u2' h1 h2 => propext
      ⟨h_resp u1 u1' u2 u2' h1 h2,
       h_resp u1' u1 u2' u2 (finest_equiv_symm F u1 u1' h1)
         (finest_equiv_symm F u2 u2' h2)⟩) q1 q2

/-- Quotient edge endpoints satisfy the descended invariant. -/
theorem finest_quotient_invariant (F : MorphFamily T U)
    (G : Graph U) (rr_rel : U → U → Prop) (inv : U → Prop)
    (h_valid : pp_valid G rr_rel inv)
    (h_inv_resp : ∀ u1 u2, finest_equiv F u1 u2 → (inv u1 ↔ inv u2))
    (q1 q2 : FinestQuotient F)
    (h_edge : (finest_graph F G.edges).edges q1 q2) :
    quotient_invariant F inv h_inv_resp q1 ∧
      quotient_invariant F inv h_inv_resp q2 := by
  obtain ⟨_, u1, u2, hq1, hq2, h_orig_edge⟩ := h_edge
  subst q1
  subst q2
  exact ⟨(h_valid u1 u2 h_orig_edge).2.1,
    (h_valid u1 u2 h_orig_edge).2.2.1⟩

/-- Stronger: the quotient graph inherits full pp_valid.
    If the original graph is pp_valid and rr_rel + inv both respect
    finest_equiv, then the quotient graph is pp_valid with the
    descended invariant and a descended rr_rel. -/
theorem finest_quotient_inherits_pp_valid (F : MorphFamily T U)
    (G : Graph U) (rr_rel : U → U → Prop) (inv : U → Prop)
    (h_valid : pp_valid G rr_rel inv)
    (h_inv_resp : ∀ u1 u2, finest_equiv F u1 u2 → (inv u1 ↔ inv u2))
    (h_rr_resp : ∀ u1 u1' u2 u2',
      finest_equiv F u1 u1' → finest_equiv F u2 u2' →
      rr_rel u1 u2 → rr_rel u1' u2') :
    pp_valid (finest_graph F G.edges) (quotient_rr F rr_rel h_rr_resp)
      (quotient_invariant F inv h_inv_resp) := by
  intro q1 q2 h_edge
  obtain ⟨hne, u1, u2, hq1, hq2, h_orig_edge⟩ := h_edge
  subst q1
  subst q2
  have h_pp := h_valid u1 u2 h_orig_edge
  exact ⟨hne, h_pp.2.1, h_pp.2.2.1, h_pp.2.2.2⟩

/-- Selection preserves invariant: if canonical representative satisfies
    inv, all elements in its finest class also satisfy inv -/
theorem canonical_preserves_invariant (F : MorphFamily T U)
    (inv : U → Prop)
    (h_resp : ∀ u1 u2, finest_equiv F u1 u2 → (inv u1 ↔ inv u2))
    (u_can u' : U) (h_equiv : finest_equiv F u_can u')
    (h_inv : inv u_can) :
    inv u' :=
  (h_resp u_can u' h_equiv).mp h_inv

-- ═══════════════════════════════════════════════════════════════════
-- Verification
-- ═══════════════════════════════════════════════════════════════════

#check @induced_equiv_is_equiv
#check @fg_consistent
#check @f_preserves_equiv
#check @g_section
#check @finest_equiv_is_equivalence
#check @finest_refines_each
#check @finest_is_coarsest_refinement
#check @finest_canonical_unique
#check @lens_pred
#check @lens_family_cert
#check @lens_cert_monotone
#check @lens_certificate
#check @lens_certificate_monotone
#check @lensCertFamily
#check @lens_master_refinement
#check @all_lenses_iff_finest
#check @lens_pred_refl
#check @lens_propagates
#check @finest_graph
#check @quotient_invariant
#check @quotient_rr
#check @finest_quotient_invariant
#check @finest_quotient_inherits_pp_valid
#check @canonical_preserves_invariant

-- ═══════════════════════════════════════════════════════════════════
-- Section 7: Bridge to pp_quotient (PPGraphCategorical)
-- ═══════════════════════════════════════════════════════════════════

/-- The projection Quotient.mk is surjective -/
theorem proj_mk_surjective (F : MorphFamily T U) :
    Function.Surjective (Quotient.mk (finestSetoid F)) :=
  fun q => Quotient.inductionOn q (fun u => ⟨u, rfl⟩)

/-- Edges separate classes: if there is an edge between x and y,
    they are NOT in the same finest class.
    This is the condition under which projection is a pp_morphism. -/
def edges_separate_classes (F : MorphFamily T U) (G : Graph U) : Prop :=
  ∀ x y, G.edges x y → ¬ finest_equiv F x y

/-- Under edges_separate_classes, the projection preserves edges -/
theorem proj_preserves_edges_sep (F : MorphFamily T U) (G : Graph U)
    (h_sep : edges_separate_classes F G)
    (x y : U) (h_edge : G.edges x y) :
    (finest_graph F G.edges).edges
      (Quotient.mk (finestSetoid F) x)
      (Quotient.mk (finestSetoid F) y) := by
  constructor
  · intro h_eq
    exact h_sep x y h_edge (Quotient.exact h_eq)
  · exact ⟨x, y, rfl, rfl, h_edge⟩

/-- Noncollapsing edges and well-defined descended predicates give a genuine
    categorical pp_morphism. Each supplied source pp-edge yields a target
    pp-edge with the descended invariant and refinement relation. -/
theorem proj_is_pp_morphism (F : MorphFamily T U)
    (G : Graph U) (rr_rel : U → U → Prop) (inv : U → Prop)
    (h_sep : edges_separate_classes F G)
    (h_inv_resp : ∀ u1 u2, finest_equiv F u1 u2 → (inv u1 ↔ inv u2))
    (h_rr_resp : ∀ u1 u1' u2 u2',
      finest_equiv F u1 u1' → finest_equiv F u2 u2' →
      rr_rel u1 u2 → rr_rel u1' u2') :
    pp_morphism (Quotient.mk (finestSetoid F)) G (finest_graph F G.edges)
      rr_rel inv (quotient_rr F rr_rel h_rr_resp)
      (quotient_invariant F inv h_inv_resp) := by
  constructor
  · intro _ _; exact trivial
  · intro x y ⟨h_edge, h_pp⟩
    have h_image := proj_preserves_edges_sep F G h_sep x y h_edge
    exact ⟨h_image, h_image.1, h_pp.2.1, h_pp.2.2.1, h_pp.2.2.2⟩

/-- The projection gives a pp_quotient in the sense of Categorical:
    surjective pp_morphism -/
theorem proj_is_pp_quotient (F : MorphFamily T U)
    (G : Graph U) (rr_rel : U → U → Prop) (inv : U → Prop)
    (h_sep : edges_separate_classes F G)
    (h_inv_resp : ∀ u1 u2, finest_equiv F u1 u2 → (inv u1 ↔ inv u2))
    (h_rr_resp : ∀ u1 u1' u2 u2',
      finest_equiv F u1 u1' → finest_equiv F u2 u2' →
      rr_rel u1 u2 → rr_rel u1' u2') :
    pp_quotient (Quotient.mk (finestSetoid F)) G (finest_graph F G.edges)
      rr_rel inv (quotient_rr F rr_rel h_rr_resp)
      (quotient_invariant F inv h_inv_resp) :=
  ⟨proj_is_pp_morphism F G rr_rel inv h_sep h_inv_resp h_rr_resp,
   proj_mk_surjective F⟩

-- ═══════════════════════════════════════════════════════════════════
-- Final Verification
-- ═══════════════════════════════════════════════════════════════════

#check @proj_mk_surjective
#check @edges_separate_classes
#check @proj_preserves_edges_sep
#check @proj_is_pp_morphism
#check @proj_is_pp_quotient

-- Explicit checks for all remaining helper theorems.
#check @finest_equiv_refl
#check @finest_equiv_symm
#check @finest_equiv_trans
