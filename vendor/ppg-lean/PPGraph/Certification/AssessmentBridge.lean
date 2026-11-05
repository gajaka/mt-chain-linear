/-
  PPGraphAssessmentBridge.lean
  Bridge: Self-Assessment ↔ Parametric Certification

  The point: parametric certification IS an instance of the
  self-assessment repair model. We set:

    S := D        (system state = datum)
    V := Θ        (vertex = specification level)
    Spec := fully_certified F   (spec(d, θ) = all certs pass at θ)
    RepairOp := R : D → Θ → D  (repair operator on data)

  Then valid_repair from SelfAssessment directly gives:
    - target_restored: ¬Certified(d,t) → Certified(R(d,t), t)
    - core_preserved: ∀θ≠t, Certified(d,θ) → Certified(R(d,t), θ)

  And repair_strict_growth applies without re-proof:
    CertifiedLevels(d) ⊊ CertifiedLevels(R(d,t))

  The complete formal cycle:
    canonical(d) → blocking(d,t) → contain failure → valid_repair →
    strict growth → blocking cleared → canonical advances

  Author: Dragan Stosic, 2026.
-/

module

public import Mathlib.Tactic
public import PPGraph.Certification.Parametric
public import PPGraph.Certification.Blocking
public import PPGraph.Certification.SelfAssessment

@[expose] public section

set_option linter.unusedVariables false
set_option linter.unusedSectionVars false

variable {D Θ : Type} [PartialOrder Θ] [DecidableEq Θ]

-- ═══════════════════════════════════════════════════════════════════
-- Section 1: Type-Level Bridge (SelfAssessment instantiation)
-- ═══════════════════════════════════════════════════════════════════

/-- The certification spec: parametric certification viewed as a
    Spec in the self-assessment sense. S=D, V=Θ. -/
def certSpec (F : CertFamily D Θ) : Spec D Θ :=
  fun d t => fully_certified F d t

/-- broken in the certification sense = not fully certified -/
theorem certSpec_broken_iff (F : CertFamily D Θ) (d : D) (t : Θ) :
    broken (certSpec F) d t ↔ ¬ fully_certified F d t := by
  rfl

/-- A repair operator in the parametric world: D → Θ → D.
    Given a datum and a target level, produce a repaired datum. -/
def ParametricRepairOp (D Θ : Type) := D → Θ → D

/-- valid_repair from SelfAssessment instantiated on certSpec:
    target restoration + core preservation. -/
def valid_cert_repair (F : CertFamily D Θ) (R : ParametricRepairOp D Θ)
    (d : D) (t : Θ) : Prop :=
  (¬ fully_certified F d t → fully_certified F (R d t) t) ∧
  (∀ θ, θ ≠ t → fully_certified F d θ → fully_certified F (R d t) θ)

-- ═══════════════════════════════════════════════════════════════════
-- Section 2: Strict Growth of Certified Levels
-- ═══════════════════════════════════════════════════════════════════

/-- Preservation: every level certified before repair remains certified
    after. CertifiedLevels(d) ⊆ CertifiedLevels(R(d,t)). -/
theorem cert_repair_preserves (F : CertFamily D Θ)
    (R : ParametricRepairOp D Θ) (d : D) (t : Θ)
    (h_broken : ¬ fully_certified F d t)
    (h_valid : valid_cert_repair F R d t)
    (θ : Θ) (h_cert : fully_certified F d θ) :
    fully_certified F (R d t) θ := by
  by_cases h_eq : θ = t
  · subst h_eq
    exact absurd h_cert h_broken
  · exact h_valid.2 θ h_eq h_cert

/-- Strict growth: CertifiedLevels(d) ⊊ CertifiedLevels(R(d,t)).
    The repaired datum certifies everything the old one did, plus t. -/
theorem cert_repair_strict_growth (F : CertFamily D Θ)
    (R : ParametricRepairOp D Θ) (d : D) (t : Θ)
    (h_broken : ¬ fully_certified F d t)
    (h_valid : valid_cert_repair F R d t) :
    (∀ θ, fully_certified F d θ → fully_certified F (R d t) θ) ∧
    (fully_certified F (R d t) t ∧ ¬ fully_certified F d t) := by
  constructor
  · intro θ h_cert
    exact cert_repair_preserves F R d t h_broken h_valid θ h_cert
  · exact ⟨h_valid.1 h_broken, h_broken⟩

-- ═══════════════════════════════════════════════════════════════════
-- Section 3: Canonical Level After Repair
-- ═══════════════════════════════════════════════════════════════════

/-- After valid repair at level t, the new canonical is at most t. -/
theorem canonical_after_repair (F : CertFamily D Θ)
    (R : ParametricRepairOp D Θ) (d : D) (t : Θ) (t_c_new : Θ)
    (h_broken : ¬ fully_certified F d t)
    (h_valid : valid_cert_repair F R d t)
    (h_can_new : is_canonical F (R d t) t_c_new) :
    t_c_new ≤ t :=
  h_can_new.2 t (h_valid.1 h_broken)

/-- If repair target t is stricter than old canonical (t ≤ t_c_old),
    then the new canonical advances: t_c_new ≤ t ≤ t_c_old.
    Canonical frontier has genuinely improved. -/
theorem canonical_frontier_advances (F : CertFamily D Θ)
    (R : ParametricRepairOp D Θ) (d : D) (t t_c_old t_c_new : Θ)
    (h_broken : ¬ fully_certified F d t)
    (h_valid : valid_cert_repair F R d t)
    (h_target_stricter : t ≤ t_c_old)
    (h_can_old : is_canonical F d t_c_old)
    (h_can_new : is_canonical F (R d t) t_c_new) :
    t_c_new ≤ t ∧ t ≤ t_c_old :=
  ⟨h_can_new.2 t (h_valid.1 h_broken), h_target_stricter⟩

-- ═══════════════════════════════════════════════════════════════════
-- Section 4: Blocking Set Clears After Repair
-- ═══════════════════════════════════════════════════════════════════

/-- At the repaired level t, no certificate blocks anymore. -/
theorem repair_clears_blocking (F : CertFamily D Θ)
    (R : ParametricRepairOp D Θ) (d : D) (t : Θ)
    (h_broken : ¬ fully_certified F d t)
    (h_valid : valid_cert_repair F R d t)
    (C : Certificate D Θ) (h_mem : C ∈ F.certs) :
    ¬ blocks F C (R d t) t := by
  intro h_blocks
  have h_cert := (h_valid.1 h_broken) C h_mem
  exact h_blocks.2 h_cert

/-- Blocking set at t becomes empty after repair. -/
theorem repair_removes_all_blockers (F : CertFamily D Θ)
    (R : ParametricRepairOp D Θ) (d : D) (t : Θ)
    (h_broken : ¬ fully_certified F d t)
    (h_valid : valid_cert_repair F R d t) :
    blocking_set F (R d t) t = ∅ := by
  ext C
  simp [blocking_set, blocks]
  intro h_mem
  exact (h_valid.1 h_broken) C h_mem

-- ═══════════════════════════════════════════════════════════════════
-- Section 5: Complete Cycle Theorem
-- ═══════════════════════════════════════════════════════════════════

/-- The complete assess → repair → re-certify cycle.
    Given a broken target and a valid repair operator:
    1. R(d,t) is certified at t
    2. All previously certified levels preserved
    3. Blocking set at t is empty
    4. New canonical ≤ t
    5. If t ≤ t_c_old, canonical frontier advances -/
theorem complete_repair_cycle (F : CertFamily D Θ)
    (R : ParametricRepairOp D Θ) (d : D) (t t_c_new : Θ)
    (h_broken : ¬ fully_certified F d t)
    (h_valid : valid_cert_repair F R d t)
    (h_can_new : is_canonical F (R d t) t_c_new) :
    fully_certified F (R d t) t ∧
    (∀ θ, fully_certified F d θ → fully_certified F (R d t) θ) ∧
    blocking_set F (R d t) t = ∅ ∧
    t_c_new ≤ t := by
  refine ⟨h_valid.1 h_broken, ?_, ?_, ?_⟩
  · intro θ h_cert
    exact cert_repair_preserves F R d t h_broken h_valid θ h_cert
  · exact repair_removes_all_blockers F R d t h_broken h_valid
  · exact canonical_after_repair F R d t t_c_new h_broken h_valid h_can_new

-- ═══════════════════════════════════════════════════════════════════
-- Verification
-- ═══════════════════════════════════════════════════════════════════

#check @certSpec_broken_iff
#check @cert_repair_preserves
#check @cert_repair_strict_growth
#check @canonical_after_repair
#check @canonical_frontier_advances
#check @repair_clears_blocking
#check @repair_removes_all_blockers
#check @complete_repair_cycle
