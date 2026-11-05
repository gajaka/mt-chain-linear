/-
  PPGraphParametricQuotient.lean
  Quotient Structure on Specification Space

  Two specifications are certification-equivalent if they certify
  exactly the same data. The quotient Θ/~ gives the effective
  specification space. Certification-set inclusion induces a partial
  order on this quotient. The graph projection is developed separately
  in PPGraph.Certification.QuotientBridge.
-/

module

public import Mathlib.Tactic
public import PPGraph.Core.Graph
public import PPGraph.Certification.Parametric
public import PPGraph.Core.Categorical

@[expose] public section

variable {Θ : Type} [PartialOrder Θ]
variable {D : Type}

-- ═══════════════════════════════════════════════════════════════════
-- Section 1: Certification Equivalence
-- ═══════════════════════════════════════════════════════════════════

/-- Two specifications are certification-equivalent if they certify
    exactly the same data -/
def cert_equiv (F : CertFamily D Θ) (t1 t2 : Θ) : Prop :=
  ∀ d : D, fully_certified F d t1 ↔ fully_certified F d t2

theorem cert_equiv_refl (F : CertFamily D Θ) (t : Θ) :
    cert_equiv F t t :=
  fun _ => Iff.rfl

theorem cert_equiv_symm (F : CertFamily D Θ) (t1 t2 : Θ)
    (h : cert_equiv F t1 t2) :
    cert_equiv F t2 t1 :=
  fun d => (h d).symm

theorem cert_equiv_trans (F : CertFamily D Θ) (t1 t2 t3 : Θ)
    (h12 : cert_equiv F t1 t2) (h23 : cert_equiv F t2 t3) :
    cert_equiv F t1 t3 :=
  fun d => (h12 d).trans (h23 d)

-- ═══════════════════════════════════════════════════════════════════
-- Section 2: Order Compatibility
-- ═══════════════════════════════════════════════════════════════════

/-- If t1 ≤ t2 and they are cert-equivalent, then they certify
    the same data despite being ordered -/
theorem equiv_and_order_implies_same_cert (F : CertFamily D Θ)
    (t1 t2 : Θ) (_h_order : t1 ≤ t2) (h_equiv : cert_equiv F t1 t2)
    (d : D) :
    fully_certified F d t1 ↔ fully_certified F d t2 :=
  h_equiv d

/-- Canonical level is unique up to certification equivalence:
    any two canonical levels for the same data are cert-equivalent -/
theorem canonical_unique_up_to_equiv (F : CertFamily D Θ)
    (d : D) (t_c1 t_c2 : Θ)
    (h1 : is_canonical F d t_c1) (h2 : is_canonical F d t_c2) :
    cert_equiv F t_c1 t_c2 := by
  intro d'
  constructor
  · intro hc1
    have h_le : t_c1 ≤ t_c2 := h1.2 t_c2 h2.1
    have h_ge : t_c2 ≤ t_c1 := h2.2 t_c1 h1.1
    have h_eq : t_c1 = t_c2 := le_antisymm h_le h_ge
    rw [h_eq] at hc1
    exact hc1
  · intro hc2
    have h_le : t_c1 ≤ t_c2 := h1.2 t_c2 h2.1
    have h_ge : t_c2 ≤ t_c1 := h2.2 t_c1 h1.1
    have h_eq : t_c1 = t_c2 := le_antisymm h_le h_ge
    rw [h_eq]
    exact hc2

/-- In a partial order, canonical is actually unique (not just up to equiv) -/
theorem canonical_unique (F : CertFamily D Θ)
    (d : D) (t_c1 t_c2 : Θ)
    (h1 : is_canonical F d t_c1) (h2 : is_canonical F d t_c2) :
    t_c1 = t_c2 :=
  le_antisymm (h1.2 t_c2 h2.1) (h2.2 t_c1 h1.1)

-- ═══════════════════════════════════════════════════════════════════
-- Section 3: Equivalence Classes and Quotient Order
-- ═══════════════════════════════════════════════════════════════════

/-- cert_equiv is a Setoid -/
def certSetoid (F : CertFamily D Θ) : Setoid Θ where
  r := cert_equiv F
  iseqv := {
    refl := cert_equiv_refl F
    symm := cert_equiv_symm F _ _
    trans := cert_equiv_trans F _ _ _
  }

/-- The quotient type: effective specification space -/
def SpecQuotient (F : CertFamily D Θ) := Quotient (certSetoid F)

/-- Certification is well-defined on the quotient -/
theorem cert_respects_equiv (F : CertFamily D Θ) (d : D) (t1 t2 : Θ)
    (h : cert_equiv F t1 t2) :
    fully_certified F d t1 ↔ fully_certified F d t2 :=
  h d

-- ═══════════════════════════════════════════════════════════════════
-- Section 4: PPG Quotient Bridge
-- ═══════════════════════════════════════════════════════════════════

/-- Certification propagates along a specification edge by monotonicity.
    This helper does not compare edges between equivalent representatives. -/
theorem spec_edge_respects_equiv (F : CertFamily D Θ)
    (t1 t2 : Θ) (d : D)
    (h_edge : spec_edge t1 t2)
    (h_cert : fully_certified F d t1) :
    fully_certified F d t2 :=
  certification_propagates F d t1 t2 h_edge h_cert

/-- Every quotient class has a representative. This is surjectivity of the
    projection as a function; its graph properties are separate obligations. -/
theorem quotient_projection_surjective (F : CertFamily D Θ) :
    Function.Surjective (Quotient.mk (certSetoid F)) :=
  fun q => Quotient.inductionOn q (fun a => ⟨a, rfl⟩)

-- ═══════════════════════════════════════════════════════════════════
-- Section 5: Certification Within an Equivalence Class
-- ═══════════════════════════════════════════════════════════════════

/-- Certification transfers backwards between certification-equivalent
    specifications. The order hypothesis is retained for this helper's API;
    certification equivalence alone supplies the implication. -/
theorem equiv_chain_collapses (F : CertFamily D Θ)
    (t1 t2 : Θ) (_h_order : t1 ≤ t2) (h_equiv : cert_equiv F t1 t2)
    (d : D) (h_cert : fully_certified F d t2) :
    fully_certified F d t1 := by
  exact (h_equiv d).mpr h_cert

/-- Nontrivial equivalence class implies no new certification boundary:
    within one class, all specs agree on every data point -/
theorem equiv_class_uniform (F : CertFamily D Θ)
    (t1 t2 : Θ) (h_equiv : cert_equiv F t1 t2)
    (d : D) :
    fully_certified F d t1 = fully_certified F d t2 := by
  exact propext (h_equiv d)

-- ═══════════════════════════════════════════════════════════════════
-- Section 6: Induced Order on the Quotient
-- ═══════════════════════════════════════════════════════════════════

/-- Induced order on representatives: t1 ≼ t2 if every data certified
    at t1 is also certified at t2.
    (This is the order that descends to the quotient.) -/
def cert_le (F : CertFamily D Θ) (t1 t2 : Θ) : Prop :=
  ∀ d : D, fully_certified F d t1 → fully_certified F d t2

theorem cert_le_refl (F : CertFamily D Θ) (t : Θ) :
    cert_le F t t := fun _ h => h

theorem cert_le_trans (F : CertFamily D Θ) (t1 t2 t3 : Θ)
    (h12 : cert_le F t1 t2) (h23 : cert_le F t2 t3) :
    cert_le F t1 t3 :=
  fun d h => h23 d (h12 d h)

/-- The induced order is compatible with certification equivalence.
    If t1 ~ t1' and t2 ~ t2', then t1 ≼ t2 ↔ t1' ≼ t2'. -/
theorem cert_le_respects_equiv (F : CertFamily D Θ)
    (t1 t1' t2 t2' : Θ)
    (h1 : cert_equiv F t1 t1') (h2 : cert_equiv F t2 t2') :
    cert_le F t1 t2 ↔ cert_le F t1' t2' := by
  constructor
  · intro h d hd'
    have hd : fully_certified F d t1 := (h1 d).mpr hd'
    have h2d : fully_certified F d t2 := h d hd
    exact (h2 d).mp h2d
  · intro h d hd
    have hd' : fully_certified F d t1' := (h1 d).mp hd
    have h2d' : fully_certified F d t2' := h d hd'
    exact (h2 d).mpr h2d'

/-- Well-defined order on the quotient -/
def SpecQuotient.le (F : CertFamily D Θ) (q1 q2 : SpecQuotient F) : Prop :=
  Quotient.lift₂ (cert_le F)
    (fun t1 t2 t1' t2' h1 h2 => propext (cert_le_respects_equiv F t1 t1' t2 t2' h1 h2))
    q1 q2

/-- The quotient carries a preorder -/
instance (F : CertFamily D Θ) : Preorder (SpecQuotient F) where
  le := SpecQuotient.le F
  le_refl := by
    intro q
    refine Quotient.inductionOn q ?_
    intro t
    exact cert_le_refl F t
  le_trans := by
    intro q1 q2 q3
    refine Quotient.inductionOn₃ q1 q2 q3 ?_
    intro t1 t2 t3 h12 h23
    exact cert_le_trans F t1 t2 t3 h12 h23

/-- Antisymmetry on the quotient (because we already quotiented by cert_equiv) -/
theorem SpecQuotient.le_antisymm (F : CertFamily D Θ)
    (q1 q2 : SpecQuotient F)
    (h12 : q1 ≤ q2) (h21 : q2 ≤ q1) : q1 = q2 := by
  refine Quotient.inductionOn₂ q1 q2 (fun t1 t2 h12 h21 => ?_) h12 h21
  apply Quotient.sound
  intro d
  constructor
  · exact h12 d
  · exact h21 d

/-- PartialOrder on the quotient -/
instance (F : CertFamily D Θ) : PartialOrder (SpecQuotient F) where
  le_antisymm := SpecQuotient.le_antisymm F

-- ═══════════════════════════════════════════════════════════════════
-- Verification
-- ═══════════════════════════════════════════════════════════════════

#check @cert_equiv_refl
#check @cert_equiv_symm
#check @cert_equiv_trans
#check @equiv_and_order_implies_same_cert
#check @canonical_unique_up_to_equiv
#check @canonical_unique
#check @cert_respects_equiv
#check @spec_edge_respects_equiv
#check @quotient_projection_surjective
#check @equiv_chain_collapses
#check @equiv_class_uniform
#check @cert_le_refl
#check @cert_le_trans
#check @cert_le_respects_equiv
#check @SpecQuotient.le_antisymm

-- ═══════════════════════════════════════════════════════════════════
-- Section 7: Meet on Quotient (under InfClosed assumption)
-- ═══════════════════════════════════════════════════════════════════

variable {Θ' : Type} [Lattice Θ']

/-- CertInfClosed: every certificate in the family is closed under meet -/
def CertInfClosed (F : CertFamily D Θ') : Prop :=
  ∀ C ∈ F.certs, ∀ (d : D) (a b : Θ'), C d a → C d b → C d (a ⊓ b)

/-- Under CertInfClosed, fully_certified is closed under meet -/
theorem certified_inf_closed' (F : CertFamily D Θ') (d : D) (t1 t2 : Θ')
    (h_ic : CertInfClosed F)
    (h1 : fully_certified F d t1) (h2 : fully_certified F d t2) :
    fully_certified F d (t1 ⊓ t2) := by
  intro C hC
  exact h_ic C hC d t1 t2 (h1 C hC) (h2 C hC)

/-- Under CertInfClosed, cert_equiv respects meet -/
theorem cert_inf_respects_equiv' (F : CertFamily D Θ')
    (h_ic : CertInfClosed F)
    (t1 t1' t2 t2' : Θ')
    (h1 : cert_equiv F t1 t1') (h2 : cert_equiv F t2 t2') :
    cert_equiv F (t1 ⊓ t2) (t1' ⊓ t2') := by
  intro d
  constructor
  · intro h_cert
    have h_t1 : fully_certified F d t1 :=
      (certified_meet_implies_both F d t1 t2 h_cert).1
    have h_t2 : fully_certified F d t2 :=
      (certified_meet_implies_both F d t1 t2 h_cert).2
    have h_t1' : fully_certified F d t1' := (h1 d).mp h_t1
    have h_t2' : fully_certified F d t2' := (h2 d).mp h_t2
    exact certified_inf_closed' F d t1' t2' h_ic h_t1' h_t2'
  · intro h_cert
    have h_t1' : fully_certified F d t1' :=
      (certified_meet_implies_both F d t1' t2' h_cert).1
    have h_t2' : fully_certified F d t2' :=
      (certified_meet_implies_both F d t1' t2' h_cert).2
    have h_t1 : fully_certified F d t1 := (h1 d).mpr h_t1'
    have h_t2 : fully_certified F d t2 := (h2 d).mpr h_t2'
    exact certified_inf_closed' F d t1 t2 h_ic h_t1 h_t2

/-- Well-defined meet on the quotient (under CertInfClosed) -/
def SpecQuotient.inf_ic (F : CertFamily D Θ') (h_ic : CertInfClosed F)
    (q1 q2 : SpecQuotient F) : SpecQuotient F :=
  Quotient.lift₂ (fun t1 t2 => Quotient.mk (certSetoid F) (t1 ⊓ t2))
    (fun t1 t2 t1' t2' h1 h2 => Quotient.sound
      (cert_inf_respects_equiv' F h_ic t1 t1' t2 t2' h1 h2))
    q1 q2

/-- For monotone certificates, certified at t implies certified at t ⊔ s -/
theorem certified_sup_left (F : CertFamily D Θ') (d : D) (t1 t2 : Θ')
    (h : fully_certified F d t1) :
    fully_certified F d (t1 ⊔ t2) := by
  intro C hC
  exact F.all_monotone C hC d t1 (t1 ⊔ t2) le_sup_left (h C hC)

theorem certified_sup_right (F : CertFamily D Θ') (d : D) (t1 t2 : Θ')
    (h : fully_certified F d t2) :
    fully_certified F d (t1 ⊔ t2) := by
  intro C hC
  exact F.all_monotone C hC d t2 (t1 ⊔ t2) le_sup_right (h C hC)

-- Upward closure preserves certification at joins, as proved above.
-- Descending join to certification-equivalence classes is a different claim:
-- changing either representative need not preserve the class of their join.
-- That construction requires a separate compatibility hypothesis. The meet
-- operation above is well-defined under CertInfClosed; no lattice instance
-- on the quotient is constructed here.

-- ═══════════════════════════════════════════════════════════════════
-- Section 8: Linear Orders and Separating Families
-- ═══════════════════════════════════════════════════════════════════

variable {Θ'' : Type} [LinearOrder Θ'']

/-- In a linear order with monotone certs, if t1 < t2 and there exists
    data certified at t2 but not t1, then they are NOT cert-equivalent -/
theorem linear_strict_not_equiv (F : CertFamily D Θ'')
    (t1 t2 : Θ'') (_h_lt : t1 < t2)
    (d : D) (h_cert2 : fully_certified F d t2)
    (h_not1 : ¬ fully_certified F d t1) :
    ¬ cert_equiv F t1 t2 := by
  intro h_equiv
  exact h_not1 ((h_equiv d).mpr h_cert2)

/-- In a linear order, cert_equiv classes are convex intervals:
    if t1 ~ t3 and t1 ≤ t2 ≤ t3, then t1 ~ t2 -/
theorem equiv_convex (F : CertFamily D Θ'')
    (t1 t2 t3 : Θ'')
    (h13 : cert_equiv F t1 t3)
    (h12 : t1 ≤ t2) (h23 : t2 ≤ t3) :
    cert_equiv F t1 t2 := by
  intro d
  constructor
  · intro h_cert1
    exact master_refinement F d t1 t2 h12 h_cert1
  · intro h_cert2
    have h_cert3 : fully_certified F d t3 := master_refinement F d t2 t3 h23 h_cert2
    exact (h13 d).mpr h_cert3

/-- The original order implies inclusion of certified data sets.
    The converse is not asserted for an arbitrary certificate family. -/
theorem linear_cert_le_of_le (F : CertFamily D Θ'')
    (t1 t2 : Θ'') (h_le : t1 ≤ t2) :
    cert_le F t1 t2 := by
  intro d h_cert
  exact master_refinement F d t1 t2 h_le h_cert

/-- In a linear order, certified at t implies certified at t ⊔ s
    (LinearOrder implies Lattice via DistribLattice) -/
theorem linear_join_preserves (F : CertFamily D Θ'')
    (d : D) (t1 t2 : Θ'')
    (h : fully_certified F d t1) :
    fully_certified F d (t1 ⊔ t2) := by
  intro C hC
  exact F.all_monotone C hC d t1 (t1 ⊔ t2) le_sup_left (h C hC)

/-- A certificate family separates points: for any t1 < t2,
    there exists data that distinguishes them -/
def separating (F : CertFamily D Θ'') : Prop :=
  ∀ t1 t2 : Θ'', t1 < t2 →
    ∃ d : D, fully_certified F d t2 ∧ ¬ fully_certified F d t1

/-- Under separating, cert_equiv implies equality -/
theorem separating_equiv_eq (F : CertFamily D Θ'')
    (h_sep : separating F) (t1 t2 : Θ'')
    (h_equiv : cert_equiv F t1 t2) :
    t1 = t2 := by
  by_contra h_ne
  cases lt_or_gt_of_ne h_ne with
  | inl h_lt =>
    obtain ⟨d, h_cert2, h_not1⟩ := h_sep t1 t2 h_lt
    exact h_not1 ((h_equiv d).mpr h_cert2)
  | inr h_gt =>
    obtain ⟨d, h_cert1, h_not2⟩ := h_sep t2 t1 h_gt
    exact h_not2 ((h_equiv d).mp h_cert1)

/-- For a separating family, equality of quotient classes implies equality
    of their representatives: the quotient projection is injective. -/
theorem separating_quotient_trivial (F : CertFamily D Θ'')
    (h_sep : separating F) (t1 t2 : Θ'')
    (h_q : Quotient.mk (certSetoid F) t1 = Quotient.mk (certSetoid F) t2) :
    t1 = t2 :=
  separating_equiv_eq F h_sep t1 t2 (Quotient.exact h_q)

-- ═══════════════════════════════════════════════════════════════════
-- Verification
-- ═══════════════════════════════════════════════════════════════════

#check @cert_equiv_refl
#check @cert_equiv_symm
#check @cert_equiv_trans
#check @equiv_and_order_implies_same_cert
#check @canonical_unique_up_to_equiv
#check @canonical_unique
#check @cert_respects_equiv
#check @spec_edge_respects_equiv
#check @quotient_projection_surjective
#check @equiv_chain_collapses
#check @equiv_class_uniform
#check @cert_le_refl
#check @cert_le_trans
#check @cert_le_respects_equiv
#check @SpecQuotient.le_antisymm
#check @certified_inf_closed'
#check @cert_inf_respects_equiv'
#check @SpecQuotient.inf_ic
#check @certified_sup_left
#check @certified_sup_right
#check @linear_strict_not_equiv
#check @equiv_convex
#check @linear_cert_le_of_le
#check @linear_join_preserves
#check @separating
#check @separating_equiv_eq
#check @separating_quotient_trivial
