/-
  PPGraphParametric.lean
  Parametric Certificate Lattice

  Core idea (Stosic, 2026):
    Certificate parameters form a lattice. One proof covers all
    instantiations. Stricter specs refine weaker ones.
-/

module

public import Mathlib.Tactic
public import Mathlib.Order.Lattice
public import PPGraph.Core.Graph

@[expose] public section

-- ═══════════════════════════════════════════════════════════════════
-- Section 1: Abstract Framework
-- ═══════════════════════════════════════════════════════════════════

variable {Θ : Type} [PartialOrder Θ]
variable {D : Type}

/-- A certificate is a predicate over data and parameters -/
def Certificate (D Θ : Type) := D → Θ → Prop

/-- A certificate is monotone: passing at stricter implies passing at weaker -/
def monotone_cert (C : Certificate D Θ) : Prop :=
  ∀ (d : D) (t1 t2 : Θ), t1 ≤ t2 → C d t1 → C d t2

/-- A certificate family: collection of monotone certificates -/
structure CertFamily (D Θ : Type) [PartialOrder Θ] where
  certs : List (Certificate D Θ)
  all_monotone : ∀ C ∈ certs, monotone_cert C

/-- Full certification: all certificates pass -/
def fully_certified (F : CertFamily D Θ) (d : D) (t : Θ) : Prop :=
  ∀ C ∈ F.certs, C d t

-- ═══════════════════════════════════════════════════════════════════
-- Section 2: Master Theorem
-- ═══════════════════════════════════════════════════════════════════

/-- Master refinement: full certification is monotone -/
theorem master_refinement (F : CertFamily D Θ)
    (d : D) (t1 t2 : Θ) (h_order : t1 ≤ t2)
    (h_cert : fully_certified F d t1) :
    fully_certified F d t2 := by
  intro C hC
  exact F.all_monotone C hC d t1 t2 h_order (h_cert C hC)

-- ═══════════════════════════════════════════════════════════════════
-- Section 3: Canonical Level
-- ═══════════════════════════════════════════════════════════════════

/-- Canonical theta: tightest level data satisfies -/
def is_canonical (F : CertFamily D Θ) (d : D) (t_c : Θ) : Prop :=
  fully_certified F d t_c ∧ ∀ t : Θ, fully_certified F d t → t_c ≤ t

/-- Certified iff canonical ≤ theta (principal upper set characterization) -/
theorem certified_iff_above_canonical (F : CertFamily D Θ)
    (d : D) (t_c t : Θ) (h_can : is_canonical F d t_c) :
    fully_certified F d t ↔ t_c ≤ t := by
  constructor
  · exact h_can.2 t
  · intro h_le
    exact master_refinement F d t_c t h_le h_can.1

-- ═══════════════════════════════════════════════════════════════════
-- Section 4: Spec Graph and PPG Bridge
-- ═══════════════════════════════════════════════════════════════════

/-- Spec edge: strict refinement between parameter levels -/
def spec_edge (t1 t2 : Θ) : Prop := t1 ≤ t2 ∧ t1 ≠ t2

/-- Certification propagates along spec edges -/
theorem certification_propagates (F : CertFamily D Θ)
    (d : D) (t1 t2 : Θ) (h_edge : spec_edge t1 t2)
    (h_cert : fully_certified F d t1) :
    fully_certified F d t2 :=
  master_refinement F d t1 t2 h_edge.1 h_cert

/-- The spec graph: vertices = all of Theta, edges = spec_edge -/
def spec_graph (Θ : Type) [PartialOrder Θ] : Graph Θ where
  vertices := fun _ => True
  edges := spec_edge
  edges_in_vertices := fun _ _ _ => ⟨trivial, trivial⟩

/-- The refinement relation for spec PPG: t1 refines t2 iff t1 ≤ t2 -/
def spec_rr (t1 t2 : Θ) : Prop := t1 ≤ t2

/-- If source is certified, the spec edge is a pp_edge -/
theorem spec_edge_is_pp (F : CertFamily D Θ) (d : D)
    (t1 t2 : Θ) (h_edge : spec_edge t1 t2)
    (h_cert : fully_certified F d t1) :
    pp_edge spec_rr (fully_certified F d) t1 t2 := by
  unfold pp_edge spec_rr
  exact ⟨h_edge.2, h_cert, certification_propagates F d t1 t2 h_edge h_cert, h_edge.1⟩

/-- The certified subgraph: only vertices where d is certified -/
def certified_subgraph (Θ : Type) [PartialOrder Θ] (F : CertFamily D Θ) (d : D) : Graph Θ where
  vertices := fun t => fully_certified F d t
  edges := fun t1 t2 => spec_edge t1 t2 ∧ fully_certified F d t1
  edges_in_vertices := by
    intro t1 t2 ⟨h_edge, h_cert⟩
    exact ⟨h_cert, certification_propagates F d t1 t2 h_edge h_cert⟩

/-- The certified subgraph is pp_valid -/
theorem certified_subgraph_pp_valid (F : CertFamily D Θ) (d : D) :
    pp_valid (certified_subgraph Θ F d) spec_rr (fully_certified F d) := by
  intro t1 t2 ⟨h_edge, h_cert⟩
  unfold pp_edge spec_rr
  exact ⟨h_edge.2, h_cert, certification_propagates F d t1 t2 h_edge h_cert, h_edge.1⟩

-- ═══════════════════════════════════════════════════════════════════
-- Section 5: Relaxation vs Repair
-- ═══════════════════════════════════════════════════════════════════

/-- Relaxation: moving to weaker spec -/
def relaxation (t_old t_new : Θ) : Prop := t_old ≤ t_new ∧ t_old ≠ t_new

/-- Repair: data changes so original spec is satisfied again -/
def repair (F : CertFamily D Θ) (d_old d_new : D) (t : Θ) : Prop :=
  ¬ fully_certified F d_old t ∧ fully_certified F d_new t

/-- Relaxation preserves certification -/
theorem relaxation_preserves (F : CertFamily D Θ)
    (d : D) (t_old t_new : Θ) (h_relax : relaxation t_old t_new)
    (h_cert : fully_certified F d t_old) :
    fully_certified F d t_new :=
  master_refinement F d t_old t_new h_relax.1 h_cert

/-- Repair raises or maintains the canonical level:
    if d_new is certified at the original spec t,
    and d_new has canonical level t_c_new,
    then t_c_new ≤ t (new canonical is at least as strict as t) -/
theorem repair_raises_canonical (F : CertFamily D Θ)
    (d_old d_new : D) (t t_c_new : Θ)
    (h_repair : repair F d_old d_new t)
    (h_can_new : is_canonical F d_new t_c_new) :
    t_c_new ≤ t :=
  h_can_new.2 t h_repair.2

/-- Repair strictly improves over relaxation:
    relaxation weakens the contract (moves up in order),
    repair restores certification at the ORIGINAL level -/
theorem repair_vs_relaxation (F : CertFamily D Θ)
    (d_old d_new : D) (t_target t_relax : Θ)
    (h_repair : repair F d_old d_new t_target)
    (h_relax : relaxation t_target t_relax)
    (_h_old_relax : fully_certified F d_old t_relax) :
    fully_certified F d_new t_target ∧ fully_certified F d_new t_relax :=
  ⟨h_repair.2, master_refinement F d_new t_target t_relax h_relax.1 h_repair.2⟩

/-- After repair, the new canonical is at least as strict as the repaired spec -/
theorem repair_canonical_below_target (F : CertFamily D Θ)
    (d_old d_new : D) (t t_c_new : Θ)
    (h_repair : repair F d_old d_new t)
    (h_can_new : is_canonical F d_new t_c_new) :
    fully_certified F d_new t ∧ t_c_new ≤ t :=
  ⟨h_repair.2, h_can_new.2 t h_repair.2⟩

/-- Repair is impossible at levels stricter than canonical -/
theorem no_repair_below_canonical (F : CertFamily D Θ)
    (d_new : D) (t t_c_new : Θ)
    (h_can_new : is_canonical F d_new t_c_new)
    (h_strict : ¬ (t_c_new ≤ t)) :
    ¬ fully_certified F d_new t := by
  intro h_cert
  exact h_strict (h_can_new.2 t h_cert)

-- ═══════════════════════════════════════════════════════════════════
-- Section 6: Lattice Operations
-- ═══════════════════════════════════════════════════════════════════

variable {Θ' : Type} [Lattice Θ']

/-- Meet certification: certified at meet implies certified at both -/
theorem certified_meet_implies_both (F : CertFamily D Θ')
    (d : D) (t1 t2 : Θ')
    (h : fully_certified F d (t1 ⊓ t2)) :
    fully_certified F d t1 ∧ fully_certified F d t2 := by
  constructor
  · intro C hC
    exact F.all_monotone C hC d _ t1 inf_le_left (h C hC)
  · intro C hC
    exact F.all_monotone C hC d _ t2 inf_le_right (h C hC)

/-- Join certification: certified at either implies certified at join -/
theorem certified_either_implies_join_left (F : CertFamily D Θ')
    (d : D) (t1 t2 : Θ')
    (h : fully_certified F d t1) :
    fully_certified F d (t1 ⊔ t2) := by
  intro C hC
  exact F.all_monotone C hC d _ _ le_sup_left (h C hC)

theorem certified_either_implies_join_right (F : CertFamily D Θ')
    (d : D) (t1 t2 : Θ')
    (h : fully_certified F d t2) :
    fully_certified F d (t1 ⊔ t2) := by
  intro C hC
  exact F.all_monotone C hC d _ _ le_sup_right (h C hC)

/-- Inf-closed certificates: certified at both implies certified at meet -/
theorem certified_both_implies_meet (F : CertFamily D Θ')
    (d : D) (t1 t2 : Θ')
    (h1 : fully_certified F d t1)
    (h2 : fully_certified F d t2)
    (h_down : ∀ C ∈ F.certs, ∀ (d : D) (a b : Θ'), C d a → C d b → C d (a ⊓ b)) :
    fully_certified F d (t1 ⊓ t2) := by
  intro C hC
  exact h_down C hC d t1 t2 (h1 C hC) (h2 C hC)

/-- Canonical level is the infimum of all satisfying levels -/
theorem canonical_is_inf (F : CertFamily D Θ')
    (d : D) (t_c : Θ') (h_can : is_canonical F d t_c)
    (t : Θ') (h_cert : fully_certified F d t) :
    t_c ⊓ t = t_c := by
  exact inf_eq_left.mpr (h_can.2 t h_cert)

-- ═══════════════════════════════════════════════════════════════════
-- Section 6b: Canonical Existence (CompleteLattice)
-- ═══════════════════════════════════════════════════════════════════

variable {Θ'' : Type} [CompleteLattice Θ'']

/-- In a complete lattice, the canonical level exists constructively
    as the infimum of all satisfying specifications -/
def canonical_spec (F : CertFamily D Θ'') (d : D) : Θ'' :=
  sInf { t : Θ'' | fully_certified F d t }

/-- Canonical spec is below all satisfying levels -/
theorem canonical_spec_le (F : CertFamily D Θ'') (d : D) (t : Θ'')
    (h : fully_certified F d t) :
    canonical_spec F d ≤ t := by
  exact sInf_le h

/-- If certification is inf-closed, canonical spec is self-certifying -/
theorem canonical_spec_certified (F : CertFamily D Θ'') (d : D)
    (h_nonempty : ∃ t : Θ'', fully_certified F d t)
    (h_inf : ∀ (S : Set Θ''), S.Nonempty →
      (∀ t ∈ S, fully_certified F d t) → fully_certified F d (sInf S)) :
    fully_certified F d (canonical_spec F d) := by
  obtain ⟨t, ht⟩ := h_nonempty
  exact h_inf { t | fully_certified F d t } ⟨t, ht⟩ (fun _ h => h)

/-- Under inf-closure, canonical_spec is truly canonical -/
theorem canonical_spec_is_canonical (F : CertFamily D Θ'') (d : D)
    (h_nonempty : ∃ t : Θ'', fully_certified F d t)
    (h_inf : ∀ (S : Set Θ''), S.Nonempty →
      (∀ t ∈ S, fully_certified F d t) → fully_certified F d (sInf S)) :
    is_canonical F d (canonical_spec F d) :=
  ⟨canonical_spec_certified F d h_nonempty h_inf,
   fun t ht => canonical_spec_le F d t ht⟩

-- ═══════════════════════════════════════════════════════════════════
-- Section 7: Canonical Existence (Product-Threshold Instance)
-- ═══════════════════════════════════════════════════════════════════

/-- Concrete threshold parameter: one real value with ≥ ordering (higher = stricter) -/
structure Threshold where
  val : Real

/-- Ordering: t1 ≤ t2 means t1 is stricter, i.e., t1.val ≥ t2.val -/
instance : LE Threshold := ⟨fun a b => b.val ≤ a.val⟩

instance : Preorder Threshold where
  le := fun a b => b.val ≤ a.val
  le_refl := fun _ => le_refl _
  le_trans := fun _ _ _ hab hbc => le_trans hbc hab

instance : PartialOrder Threshold where
  le_antisymm := by
    intro a b hab hba
    have h : a.val = b.val := le_antisymm hba hab
    cases a; cases b; simp_all

/-- Observable: one measured real value -/
structure Observable where
  val : Real

/-- The standard threshold certificate: observable.val ≥ threshold.val -/
def threshold_cert (o : Observable) (t : Threshold) : Prop :=
  o.val ≥ t.val

/-- Threshold certificate is monotone -/
theorem threshold_cert_monotone (o : Observable) (t1 t2 : Threshold)
    (h_order : t1 ≤ t2) (h_cert : threshold_cert o t1) :
    threshold_cert o t2 := by
  unfold threshold_cert at *
  show o.val ≥ t2.val
  have h_le : t2.val ≤ t1.val := h_order
  linarith

/-- Canonical threshold for an observable -/
def canonical_threshold (o : Observable) : Threshold :=
  { val := o.val }

/-- Canonical threshold is self-certifying -/
theorem canonical_threshold_self_cert (o : Observable) :
    threshold_cert o (canonical_threshold o) := by
  unfold threshold_cert canonical_threshold
  linarith

/-- Canonical threshold is the tightest satisfiable level -/
theorem canonical_threshold_tightest (o : Observable) (t : Threshold)
    (h : threshold_cert o t) :
    canonical_threshold o ≤ t := by
  unfold canonical_threshold
  show t.val ≤ o.val
  unfold threshold_cert at h
  linarith

-- ═══════════════════════════════════════════════════════════════════
-- Section 8: Lattice Instance for Threshold
-- ═══════════════════════════════════════════════════════════════════

/-- Meet: max of values (stricter combination) -/
instance : Min Threshold := ⟨fun a b => { val := max a.val b.val }⟩

/-- Join: min of values (weaker combination) -/
instance : Max Threshold := ⟨fun a b => { val := min a.val b.val }⟩

instance : Lattice Threshold where
  inf := Min.min
  le_inf := by
    intro a b c hab hac
    show max b.val c.val ≤ a.val
    exact max_le hab hac
  inf_le_left := by
    intro a b
    show a.val ≤ max a.val b.val
    exact le_max_left _ _
  inf_le_right := by
    intro a b
    show b.val ≤ max a.val b.val
    exact le_max_right _ _
  sup := Max.max
  sup_le := by
    intro a b c hac hbc
    show c.val ≤ min a.val b.val
    exact le_min hac hbc
  le_sup_left := by
    intro a b
    show min a.val b.val ≤ a.val
    exact min_le_left _ _
  le_sup_right := by
    intro a b
    show min a.val b.val ≤ b.val
    exact min_le_right _ _

/-- Meet of thresholds is the stricter contract -/
theorem threshold_meet_val (a b : Threshold) :
    (a ⊓ b).val = max a.val b.val := by rfl

/-- Join of thresholds is the weaker contract -/
theorem threshold_join_val (a b : Threshold) :
    (a ⊔ b).val = min a.val b.val := by rfl

/-- Threshold cert is inf-closed: certified at both implies certified at meet -/
theorem threshold_cert_inf_closed (o : Observable) (t1 t2 : Threshold)
    (h1 : threshold_cert o t1) (h2 : threshold_cert o t2) :
    threshold_cert o (t1 ⊓ t2) := by
  unfold threshold_cert at *
  simp [Min.min]
  exact ⟨h1, h2⟩

#check @master_refinement
#check @certified_iff_above_canonical
#check @spec_edge_is_pp
#check @certified_subgraph_pp_valid
#check @certification_propagates
#check @relaxation_preserves
#check @repair_raises_canonical
#check @repair_vs_relaxation
#check @repair_canonical_below_target
#check @no_repair_below_canonical
#check @certified_meet_implies_both
#check @certified_either_implies_join_left
#check @certified_either_implies_join_right
#check @certified_both_implies_meet
#check @canonical_is_inf
#check @canonical_spec_le
#check @canonical_spec_certified
#check @canonical_spec_is_canonical
#check @threshold_cert_monotone
#check @canonical_threshold_self_cert
#check @canonical_threshold_tightest
#check @threshold_meet_val
#check @threshold_join_val
#check @threshold_cert_inf_closed
