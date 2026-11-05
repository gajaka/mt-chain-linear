/-
  PPGraphBlocking.lean
  Blocking Certificates - Diagnostic Layer

  Defines the set of certificates that prevent certification at a
  given level. Canonical level has no blocking; stricter levels do.

  Correspondence: (θ_c, B(d)) = (canonical level, blocking certificates)
    Canonical tells how far certification reaches.
    Blocking tells why it stops there.
-/

module

public import Mathlib.Tactic
public import PPGraph.Certification.Parametric

@[expose] public section

variable {Θ : Type} [PartialOrder Θ]
variable {D : Type}

-- ═══════════════════════════════════════════════════════════════════
-- Section 1: Blocking Certificates
-- ═══════════════════════════════════════════════════════════════════

/-- A certificate blocks at level t if it is in the family but fails -/
def blocks (F : CertFamily D Θ) (C : Certificate D Θ) (d : D) (t : Θ) : Prop :=
  C ∈ F.certs ∧ ¬ C d t

/-- The blocking set: all certificates that fail at level t -/
def blocking_set (F : CertFamily D Θ) (d : D) (t : Θ) : Set (Certificate D Θ) :=
  { C | blocks F C d t }

/-- If nothing blocks, the level is certified -/
theorem empty_blocking_means_certified (F : CertFamily D Θ) (d : D) (t : Θ)
    (h : blocking_set F d t = ∅) :
    fully_certified F d t := by
  intro C hC
  by_contra h_neg
  have h_mem : C ∈ blocking_set F d t := ⟨hC, h_neg⟩
  rw [h] at h_mem
  exact h_mem

/-- If something blocks, the level is NOT certified -/
theorem nonempty_blocking_means_not_certified (F : CertFamily D Θ) (d : D) (t : Θ)
    (C : Certificate D Θ) (h_block : blocks F C d t) :
    ¬ fully_certified F d t := by
  intro h_cert
  exact h_block.2 (h_cert C h_block.1)

/-- Blocking set at canonical is empty -/
theorem canonical_blocking_empty (F : CertFamily D Θ) (d : D) (t_c : Θ)
    (h_can : is_canonical F d t_c) :
    blocking_set F d t_c = ∅ := by
  ext C
  simp [blocking_set, blocks]
  intro hC
  exact h_can.1 C hC

/-- At any level stricter than canonical, certification fails -/
theorem stricter_than_canonical_fails (F : CertFamily D Θ) (d : D) (t_c t : Θ)
    (h_can : is_canonical F d t_c)
    (h_strict : ¬ t_c ≤ t) :
    ¬ fully_certified F d t :=
  fun h_cert => h_strict (h_can.2 t h_cert)

/-- At any level stricter than canonical, blocking is nonempty -/
theorem stricter_has_blocking (F : CertFamily D Θ) (d : D) (t_c t : Θ)
    (h_can : is_canonical F d t_c)
    (h_strict : ¬ t_c ≤ t)
    (_h_nonempty : F.certs ≠ []) :
    blocking_set F d t ≠ ∅ := by
  intro h_empty
  have h_cert := empty_blocking_means_certified F d t h_empty
  exact h_strict (h_can.2 t h_cert)

-- ═══════════════════════════════════════════════════════════════════
-- Section 2: Certification State
-- ═══════════════════════════════════════════════════════════════════

/-- Certification state: canonical level paired with blocking info -/
structure CertState (Θ : Type) where
  canonical : Θ

/-- At canonical, everything passes -/
theorem at_canonical_all_pass (F : CertFamily D Θ) (d : D) (t_c : Θ)
    (h_can : is_canonical F d t_c) (C : Certificate D Θ) (hC : C ∈ F.certs) :
    C d t_c :=
  h_can.1 C hC

/-- Above canonical (weaker), everything still passes -/
theorem above_canonical_all_pass (F : CertFamily D Θ) (d : D) (t_c t : Θ)
    (h_can : is_canonical F d t_c) (h_above : t_c ≤ t)
    (C : Certificate D Θ) (hC : C ∈ F.certs) :
    C d t :=
  F.all_monotone C hC d t_c t h_above (h_can.1 C hC)

-- ═══════════════════════════════════════════════════════════════════
-- Verification
-- ═══════════════════════════════════════════════════════════════════

#check @empty_blocking_means_certified
#check @nonempty_blocking_means_not_certified
#check @canonical_blocking_empty
#check @stricter_than_canonical_fails
#check @stricter_has_blocking
#check @at_canonical_all_pass
#check @above_canonical_all_pass
