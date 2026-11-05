/-
  Finite-read certificate expressions and checked candidate search.

  A footprint is computed from the expression that is evaluated. The locality
  theorem is proved by structural induction; arbitrary semantic predicates are
  not assigned a footprint. Candidate search checks the frame and all tracked
  predicates, so its preservation result does not assume a successful repair.
-/

module

public import PPGraph.Integration.CertificationDependency

@[expose] public section

namespace FiniteReadCertificates

inductive Comparison where
  | lt | le | eq
  deriving DecidableEq, Repr

inductive Check (V : Type) where
  | truth
  | atom (comparison : Comparison) (field : V) (bound : ℚ)
  | both (left right : Check V)
  | either (left right : Check V)
  | neg (check : Check V)
  deriving DecidableEq, Repr, Inhabited

namespace Check

variable {V : Type} [DecidableEq V]

def eval : Check V → (V → ℚ) → Bool
  | .truth, _ => true
  | .atom .lt v q, d => decide (d v < q)
  | .atom .le v q, d => decide (d v ≤ q)
  | .atom .eq v q, d => decide (d v = q)
  | .both p q, d => p.eval d && q.eval d
  | .either p q, d => p.eval d || q.eval d
  | .neg p, d => !(p.eval d)

def reads : Check V → Finset V
  | .truth => ∅
  | .atom _ v _ => {v}
  | .both p q => p.reads ∪ q.reads
  | .either p q => p.reads ∪ q.reads
  | .neg p => p.reads

theorem eval_eq_of_agree_reads (p : Check V) (before after : V → ℚ)
    (h : ∀ v ∈ p.reads, before v = after v) : p.eval before = p.eval after := by
  induction p with
  | truth => rfl
  | atom comparison v q =>
      have hv := h v (by simp [reads])
      cases comparison <;> simp [eval, hv]
  | both p q hp hq =>
      simp only [eval]
      rw [hp (fun v hv => h v (Finset.mem_union_left _ hv)),
        hq (fun v hv => h v (Finset.mem_union_right _ hv))]
  | either p q hp hq =>
      simp only [eval]
      rw [hp (fun v hv => h v (Finset.mem_union_left _ hv)),
        hq (fun v hv => h v (Finset.mem_union_right _ hv))]
  | neg p hp =>
      simp only [eval]
      rw [hp h]

end Check

variable {V : Type} [DecidableEq V]

def certificate (p : Check V) : Certificate (V → ℚ) Unit :=
  fun d _ => p.eval d = true

def family (checks : List (Check V)) : CertFamily (V → ℚ) Unit where
  certs := checks.map certificate
  all_monotone := by
    intro C hC d t₁ t₂ _ h
    cases t₁
    cases t₂
    exact h

def indexedCheck (checks : List (Check V))
    (i : CertificationDependency.Index (family checks)) : Check V :=
  checks.get ⟨i.val, by simpa [family] using i.isLt⟩

def footprints (checks : List (Check V)) :
    CertVars (CertificationDependency.Index (family checks)) V :=
  fun i => (indexedCheck checks i).reads

omit [DecidableEq V] in
theorem holds_iff_eval (checks : List (Check V))
    (i : CertificationDependency.Index (family checks)) (d : V → ℚ) :
    CertificationDependency.holds (family checks) () i d ↔
      (indexedCheck checks i).eval d = true := by
  have hi : i.val < (checks.map certificate).length := by simpa [family] using i.isLt
  change (checks.map certificate).get ⟨i.val, hi⟩ d () ↔ (indexedCheck checks i).eval d = true
  rw [List.get_eq_getElem, List.getElem_map]
  rfl

theorem family_local (checks : List (Check V)) :
    CertificationDependency.FamilyLocal (family checks) (footprints checks) () := by
  intro i before after h
  rw [holds_iff_eval, holds_iff_eval]
  rw [Check.eval_eq_of_agree_reads (indexedCheck checks i) before after h]

def allPass (checks : List (Check V)) (d : V → ℚ) : Bool :=
  checks.all (fun p => p.eval d)

omit [DecidableEq V] in
theorem allPass_iff_certified (checks : List (Check V)) (d : V → ℚ) :
    allPass checks d = true ↔ fully_certified (family checks) d () := by
  simp [allPass, fully_certified, family, certificate]

variable [Fintype V]

def frame (allowed : Finset V) (before after : V → ℚ) : Bool :=
  decide (∀ v, v ∉ allowed → before v = after v)

theorem frame_iff (allowed : Finset V) (before after : V → ℚ) :
    frame allowed before after = true ↔ ∀ v ∉ allowed, before v = after v := by
  simp [frame]

/-- The bank can contain solver proposals, re-evaluated snapshots or a finite
    enumeration. Every returned proposal passes the unchanged predicates. -/
def search (checks : List (Check V)) (allowed : Finset V) (before : V → ℚ)
    (bank : List (V → ℚ)) : Option (V → ℚ) :=
  bank.find? (fun after => frame allowed before after && allPass checks after)

theorem search_sound (checks : List (Check V)) (allowed : Finset V)
    (before after : V → ℚ) (bank : List (V → ℚ))
    (h : search checks allowed before bank = some after) :
    (∀ v ∉ allowed, before v = after v) ∧ fully_certified (family checks) after () := by
  have hp := List.find?_some h
  have hp' : frame allowed before after = true ∧ allPass checks after = true := by
    simpa only [Bool.and_eq_true] using hp
  exact ⟨(frame_iff allowed before after).mp hp'.1,
    (allPass_iff_certified checks after).mp hp'.2⟩

theorem search_mem (checks : List (Check V)) (allowed : Finset V)
    (before after : V → ℚ) (bank : List (V → ℚ))
    (h : search checks allowed before bank = some after) : after ∈ bank :=
  List.mem_of_find?_eq_some h

/-- Finite search succeeds whenever its bank contains a framed, fully checked
    proposal. This is completeness for the supplied bank, not for arbitrary
    physical actions or an infinite program space. -/
theorem search_complete (checks : List (Check V)) (allowed : Finset V)
    (before : V → ℚ) (bank : List (V → ℚ))
    (h : ∃ after ∈ bank, (∀ v ∉ allowed, before v = after v) ∧
      fully_certified (family checks) after ()) :
    ∃ after, search checks allowed before bank = some after := by
  obtain ⟨after, hmem, hframe, hall⟩ := h
  have hp : frame allowed before after && allPass checks after = true := by
    simp only [Bool.and_eq_true]
    exact ⟨(frame_iff allowed before after).mpr hframe,
      (allPass_iff_certified checks after).mpr hall⟩
  cases hs : search checks allowed before bank with
  | none =>
      exact False.elim ((List.find?_eq_none.mp hs) after hmem hp)
  | some result => exact ⟨result, rfl⟩

/-- Search obtains the component contract from actual checks. The only
    footprint used by the search is computed from its selected expression. -/
theorem search_component_checked (checks : List (Check V))
    (c : CertificationDependency.Index (family checks)) (before after : V → ℚ)
    (bank : List (V → ℚ))
    (h : search checks (footprints checks c) before bank = some after) :
    CertificationDependency.ComponentChecked (family checks) (footprints checks) () c before after := by
  obtain ⟨hframe, hall⟩ := search_sound checks (footprints checks c) before after bank h
  constructor
  · intro v hv
    apply hframe v
    intro hread
    exact hv ⟨c, Finset.mem_univ c, Relation.EqvGen.refl c, hread⟩
  · intro i _
    exact hall ((family checks).certs.get i) (List.get_mem _ i)

theorem search_preserves_and_restores (checks : List (Check V))
    (c : CertificationDependency.Index (family checks)) (before after : V → ℚ)
    (bank : List (V → ℚ))
    (h : search checks (footprints checks c) before bank = some after) :
    CertificationDependency.holds (family checks) () c after ∧
      ∀ C ∈ (family checks).certs, C before () → C after () := by
  have hc := search_component_checked checks c before after bank h
  exact ⟨hc.2 c (mem_compOf_self _ _ _ (Finset.mem_univ c)),
    CertificationDependency.component_repair_preserves (family checks)
      (footprints checks) () (family_local checks) c before after hc⟩

end FiniteReadCertificates

#check @FiniteReadCertificates.Check.eval_eq_of_agree_reads
#check @FiniteReadCertificates.holds_iff_eval
#check @FiniteReadCertificates.family_local
#check @FiniteReadCertificates.allPass_iff_certified
#check @FiniteReadCertificates.frame_iff
#check @FiniteReadCertificates.search_sound
#check @FiniteReadCertificates.search_mem
#check @FiniteReadCertificates.search_complete
#check @FiniteReadCertificates.search_component_checked
#check @FiniteReadCertificates.search_preserves_and_restores
