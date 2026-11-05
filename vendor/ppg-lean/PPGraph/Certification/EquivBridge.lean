/-
  PPGraphEquivBridge.lean
  Bridge: cert_equiv IS finest_equiv (literal instance)

  Shows that cert_equiv (from PPGraphParametricQuotient) is literally
  finest_equiv (from PPGraphSelection) instantiated with:
  - T = Prop, U = Θ
  - MorphFamily.pairs = { cert_morph_pair F d | d : D }
  - Each lens g maps Θ to Prop via fully_certified F d
  - induced_equiv under each lens = "same certification status at d"
  - finest_equiv over all lenses = cert_equiv

  This is a genuine instance, not an analogy: we construct a MorphFamily
  and show that its finest_equiv coincides with cert_equiv definitionally.
-/

module

public import Mathlib.Tactic
public import PPGraph.Certification.Parametric
public import PPGraph.Certification.ParametricQuotient
public import PPGraph.Certification.Selection

@[expose] public section

set_option linter.unusedVariables false

variable {Θ : Type} [PartialOrder Θ]
variable {D : Type}

-- ═══════════════════════════════════════════════════════════════════
-- Section 1: Constructing MorphPairs from CertFamily
-- ═══════════════════════════════════════════════════════════════════

/-- For each datum d, a lens that views Θ through certification status.
    g maps a spec level to its certification status (Prop).
    eq_T on Prop is biconditional.
    f is structurally required by MorphPair but unused by induced_equiv. -/
noncomputable def cert_lens (F : CertFamily D Θ) (d : D) (t0 : Θ) : MorphPair Prop Θ where
  f := fun _ => t0
  g := fun t => fully_certified F d t
  eq_T := fun p q => (p ↔ q)
  is_equiv := {
    refl := fun _ => Iff.rfl
    symm := fun h => h.symm
    trans := fun h1 h2 => h1.trans h2
  }

/-- The induced equivalence from cert_lens is exactly
    "same certification status at d" -/
theorem cert_lens_induced (F : CertFamily D Θ) (d : D) (t0 t1 t2 : Θ) :
    induced_equiv (cert_lens F d t0) t1 t2 ↔
    (fully_certified F d t1 ↔ fully_certified F d t2) := by
  unfold induced_equiv cert_lens
  simp

-- ═══════════════════════════════════════════════════════════════════
-- Section 2: The CertFamily gives a MorphFamily (Set-based)
-- ═══════════════════════════════════════════════════════════════════

/-- The MorphFamily induced by a CertFamily over D:
    one lens per datum, indexed by D -/
noncomputable def cert_morph_family (F : CertFamily D Θ) [Nonempty D] (t0 : Θ) :
    MorphFamily Prop Θ where
  pairs := { mp | ∃ d : D, mp = cert_lens F d t0 }
  nonempty := by
    obtain ⟨d⟩ := ‹Nonempty D›
    exact ⟨cert_lens F d t0, ⟨d, rfl⟩⟩

-- ═══════════════════════════════════════════════════════════════════
-- Section 3: Bridge Theorem (literal instance)
-- ═══════════════════════════════════════════════════════════════════

/-- cert_equiv IS finest_equiv of cert_morph_family -/
theorem cert_equiv_eq_finest [Nonempty D] (F : CertFamily D Θ) (t0 t1 t2 : Θ) :
    cert_equiv F t1 t2 ↔ finest_equiv (cert_morph_family F t0) t1 t2 := by
  unfold cert_equiv finest_equiv cert_morph_family
  simp only [Set.mem_ofPred_eq]
  constructor
  · intro h mp ⟨d, hd⟩
    subst hd
    exact (cert_lens_induced F d t0 t1 t2).mpr (h d)
  · intro h d
    exact (cert_lens_induced F d t0 t1 t2).mp (h (cert_lens F d t0) ⟨d, rfl⟩)

/-- Direction →: cert_equiv implies finest_equiv -/
theorem cert_equiv_to_finest [Nonempty D] (F : CertFamily D Θ) (t0 t1 t2 : Θ)
    (h : cert_equiv F t1 t2) :
    finest_equiv (cert_morph_family F t0) t1 t2 :=
  (cert_equiv_eq_finest F t0 t1 t2).mp h

/-- Direction ←: finest_equiv implies cert_equiv -/
theorem finest_to_cert_equiv [Nonempty D] (F : CertFamily D Θ) (t0 t1 t2 : Θ)
    (h : finest_equiv (cert_morph_family F t0) t1 t2) :
    cert_equiv F t1 t2 :=
  (cert_equiv_eq_finest F t0 t1 t2).mpr h

-- ═══════════════════════════════════════════════════════════════════
-- Verification
-- ═══════════════════════════════════════════════════════════════════

#check @cert_lens
#check @cert_lens_induced
#check @cert_morph_family
#check @cert_equiv_eq_finest
#check @cert_equiv_to_finest
#check @finest_to_cert_equiv
