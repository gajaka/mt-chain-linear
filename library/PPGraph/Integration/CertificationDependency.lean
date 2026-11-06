/-
  Finite certificate-family instances of blocking dependency decomposition.

  Indices refer to the actual entries of CertFamily.certs, including repeated
  entries. At a fixed specification level, the finite failing-index set maps
  exactly to blocking_set. Footprints range over the entire tracked family,
  so a previously passing certificate cannot disappear from protection merely
  because it is absent from the current blocking set.

  Locality is an explicit obligation for these same certificate predicates.
  A component repair must preserve data outside its full-family footprint and
  establish every predicate inside that component, including previously passing
  ones. The results prove preservation and progress from those obligations;
  they do not synthesize a repair or infer locality from a list of variable names.
-/
module

public import PPGraph.Certification.Blocking
public import PPGraph.Certification.SelfAssessment
public import PPGraph.Dependency.Decomposition

@[expose] public section

set_option autoImplicit false

namespace CertificationDependency

variable {V α Θ : Type} [PartialOrder Θ]

/-- Finite positions in the actual certificate list. -/
abbrev Index (F : CertFamily (V → α) Θ) := Fin F.certs.length

/-- The indexed predicate is the original certificate at the chosen level. -/
def holds (F : CertFamily (V → α) Θ) (θ : Θ) (i : Index F) (d : V → α) : Prop :=
  F.certs.get i d θ

noncomputable def failing (F : CertFamily (V → α) Θ) (θ : Θ) (d : V → α) :
    Finset (Index F) := by
  classical
  exact Finset.univ.filter (fun i => ¬ holds F θ i d)

/-- Local must be established for the indexed family predicates themselves. -/
def FamilyLocal [DecidableEq V] (F : CertFamily (V → α) Θ)
    (vars : CertVars (Index F) V) (θ : Θ) : Prop :=
  Local vars (holds F θ)

/-- Check all certificates in the affected full-family component. -/
def ComponentChecked [DecidableEq V] (F : CertFamily (V → α) Θ) (vars : CertVars (Index F) V)
    (θ : Θ) (c : Index F) (before after : V → α) : Prop :=
  (∀ v ∉ componentFootprint vars Finset.univ c, before v = after v) ∧
  ∀ i ∈ compOf vars Finset.univ c, holds F θ i after

theorem fully_certified_iff_all (F : CertFamily (V → α) Θ) (θ : Θ) (d : V → α) :
    fully_certified F d θ ↔ ∀ i : Index F, holds F θ i d := by
  constructor
  · intro h i
    exact h (F.certs.get i) (List.get_mem F.certs i)
  · intro h C hC
    obtain ⟨i, hi⟩ := List.mem_iff_get.mp hC
    simpa only [holds, hi] using h i

theorem mem_failing (F : CertFamily (V → α) Θ) (θ : Θ) (d : V → α) (i : Index F) :
    i ∈ failing F θ d ↔ ¬ holds F θ i d := by
  classical
  simp [failing]

/-- Indexing neither adds nor loses a blocking certificate. -/
theorem blocking_set_eq_image_failing (F : CertFamily (V → α) Θ) (θ : Θ) (d : V → α) :
    blocking_set F d θ =
      (fun i : Index F => F.certs.get i) '' (failing F θ d : Set (Index F)) := by
  classical
  ext C
  change (C ∈ F.certs ∧ ¬ C d θ) ↔
    ∃ i : Index F, i ∈ failing F θ d ∧ F.certs.get i = C
  constructor
  · rintro ⟨hC, hn⟩
    obtain ⟨i, hi⟩ := List.mem_iff_get.mp hC
    refine ⟨i, (mem_failing F θ d i).mpr ?_, hi⟩
    simpa only [holds, hi] using hn
  · rintro ⟨i, hi, rfl⟩
    exact ⟨List.get_mem F.certs i, (mem_failing F θ d i).mp hi⟩

theorem fully_certified_iff_failing_empty (F : CertFamily (V → α) Θ)
    (θ : Θ) (d : V → α) : fully_certified F d θ ↔ failing F θ d = ∅ := by
  classical
  rw [fully_certified_iff_all]
  constructor
  · intro h
    apply Finset.eq_empty_of_forall_notMem
    intro i hi
    exact (mem_failing F θ d i).mp hi (h i)
  · intro h i
    by_contra hn
    have hi := (mem_failing F θ d i).mpr hn
    simp only [h, Finset.notMem_empty] at hi

variable [DecidableEq V]

/-- Previously passing certificates in the whole family remain true.
    Inside the changed component this follows from its post-check; outside
    it follows from Local and the full-family footprint frame. -/
theorem component_repair_preserves (F : CertFamily (V → α) Θ)
    (vars : CertVars (Index F) V) (θ : Θ) (hloc : FamilyLocal F vars θ)
    (c : Index F) (before after : V → α)
    (hcheck : ComponentChecked F vars θ c before after) :
    ∀ C ∈ F.certs, C before θ → C after θ := by
  classical
  intro C hC hbefore
  obtain ⟨i, hi⟩ := List.mem_iff_get.mp hC
  have hpass : holds F θ i before := by simpa only [holds, hi] using hbefore
  have hafter : holds F θ i after := by
    by_cases hsame : SameComponent vars Finset.univ c i
    · exact hcheck.2 i (Finset.mem_filter.mpr ⟨Finset.mem_univ i, hsame⟩)
    · exact (repair_noninterference vars Finset.univ (holds F θ) hloc c i
        (Finset.mem_univ i) hsame before after hcheck.1).mp hpass
  simpa only [holds, hi] using hafter

/-- The actual indexed certificate predicates instantiate the state-repair
    contract. Target restoration comes from the component post-check, while
    core preservation is derived from locality and the full-family frame. -/
theorem component_repair_valid_repair (F : CertFamily (V → α) Θ)
    (vars : CertVars (Index F) V) (θ : Θ) (hloc : FamilyLocal F vars θ)
    (repair : Index F → (V → α) → (V → α)) (before : V → α) (c : Index F)
    (hcheck : ComponentChecked F vars θ c before (repair c before)) :
    valid_repair (fun d i => repair i d) (fun d i => holds F θ i d) before c := by
  constructor
  · intro _
    exact hcheck.2 c (mem_compOf_self vars Finset.univ c (Finset.mem_univ c))
  · intro i _ hpass
    exact component_repair_preserves F vars θ hloc c before (repair c before) hcheck
      (F.certs.get i) (List.get_mem F.certs i) hpass

theorem component_repair_failing_subset (F : CertFamily (V → α) Θ)
    (vars : CertVars (Index F) V) (θ : Θ) (hloc : FamilyLocal F vars θ)
    (c : Index F) (before after : V → α)
    (hcheck : ComponentChecked F vars θ c before after) :
    failing F θ after ⊆ failing F θ before := by
  intro i hi
  apply (mem_failing F θ before i).mpr
  intro hbefore
  exact (mem_failing F θ after i).mp hi
    (component_repair_preserves F vars θ hloc c before after hcheck
      (F.certs.get i) (List.get_mem F.certs i) hbefore)

/-- Repairing a currently failing component removes at least its chosen index
    and introduces no new blockers elsewhere in the tracked family. -/
theorem component_repair_strict_progress (F : CertFamily (V → α) Θ)
    (vars : CertVars (Index F) V) (θ : Θ) (hloc : FamilyLocal F vars θ)
    (c : Index F) (before after : V → α)
    (hcheck : ComponentChecked F vars θ c before after)
    (hfail : c ∈ failing F θ before) :
    failing F θ after ⊂ failing F θ before := by
  apply Finset.ssubset_iff_subset_ne.mpr
  refine ⟨component_repair_failing_subset F vars θ hloc c before after hcheck, ?_⟩
  intro heq
  have hc : c ∈ failing F θ after := heq.symm ▸ hfail
  exact (mem_failing F θ after c).mp hc
    (hcheck.2 c (mem_compOf_self vars Finset.univ c (Finset.mem_univ c)))

/-- If this component contains all current blockers, its checked repair
    establishes full certification at the unchanged specification level. -/
theorem component_repair_certifies (F : CertFamily (V → α) Θ)
    (vars : CertVars (Index F) V) (θ : Θ) (hloc : FamilyLocal F vars θ)
    (c : Index F) (before after : V → α)
    (hcheck : ComponentChecked F vars θ c before after)
    (hcover : ∀ i ∈ failing F θ before, SameComponent vars Finset.univ c i) :
    fully_certified F after θ := by
  classical
  apply (fully_certified_iff_all F θ after).mpr
  intro i
  by_cases hp : holds F θ i before
  · exact component_repair_preserves F vars θ hloc c before after hcheck
      (F.certs.get i) (List.get_mem F.certs i) hp
  · exact hcheck.2 i (Finset.mem_filter.mpr
      ⟨Finset.mem_univ i, hcover i ((mem_failing F θ before i).mpr hp)⟩)

/-- Apply a finite list of component repair proposals to their successive states. -/
def run (F : CertFamily (V → α) Θ)
    (repair : Index F → (V → α) → (V → α)) (before : V → α) : List (Index F) → V → α
  | [] => before
  | c :: cs => run F repair (repair c before) cs

/-- Each actual intermediate change must satisfy its own component contract. -/
def PlanChecked (F : CertFamily (V → α) Θ) (vars : CertVars (Index F) V) (θ : Θ)
    (repair : Index F → (V → α) → (V → α)) (before : V → α) : List (Index F) → Prop
  | [] => True
  | c :: cs => ComponentChecked F vars θ c before (repair c before) ∧
      PlanChecked F vars θ repair (repair c before) cs

/-- A checked finite plan covering every initially blocking component establishes
    the original full-family contract. Earlier repairs remain protected by later
    full-family component checks and frames. -/
theorem checked_plan_certifies (F : CertFamily (V → α) Θ)
    (vars : CertVars (Index F) V) (θ : Θ) (hloc : FamilyLocal F vars θ)
    (repair : Index F → (V → α) → (V → α)) (before : V → α) (plan : List (Index F))
    (hcheck : PlanChecked F vars θ repair before plan)
    (hcover : ∀ i ∈ failing F θ before,
      ∃ c ∈ plan, SameComponent vars Finset.univ c i) :
    fully_certified F (run F repair before plan) θ := by
  classical
  induction plan generalizing before with
  | nil =>
      apply (fully_certified_iff_failing_empty F θ before).mpr
      apply Finset.eq_empty_of_forall_notMem
      intro i hi
      obtain ⟨c, hc, _⟩ := hcover i hi
      exact List.not_mem_nil hc
  | cons c cs ih =>
      change ComponentChecked F vars θ c before (repair c before) ∧
        PlanChecked F vars θ repair (repair c before) cs at hcheck
      obtain ⟨hhead, htail⟩ := hcheck
      change fully_certified F (run F repair (repair c before) cs) θ
      apply ih (repair c before) htail
      intro i hi
      have hbefore := component_repair_failing_subset F vars θ hloc c before
        (repair c before) hhead hi
      obtain ⟨j, hj, hsame⟩ := hcover i hbefore
      rcases List.mem_cons.mp hj with heq | hjtail
      · subst j
        exact False.elim ((mem_failing F θ (repair c before) i).mp hi
          (hhead.2 i (Finset.mem_filter.mpr ⟨Finset.mem_univ i, hsame⟩)))
      · exact ⟨j, hjtail, hsame⟩

end CertificationDependency

#check @CertificationDependency.fully_certified_iff_all
#check @CertificationDependency.mem_failing
#check @CertificationDependency.blocking_set_eq_image_failing
#check @CertificationDependency.fully_certified_iff_failing_empty
#check @CertificationDependency.component_repair_preserves
#check @CertificationDependency.component_repair_valid_repair
#check @CertificationDependency.component_repair_failing_subset
#check @CertificationDependency.component_repair_strict_progress
#check @CertificationDependency.component_repair_certifies
#check @CertificationDependency.checked_plan_certifies
