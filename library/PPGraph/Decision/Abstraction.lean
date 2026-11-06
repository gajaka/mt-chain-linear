/-
  Complete repairability decisions for potentially infinite concrete systems
  with a supplied finite, exact abstraction.

  Standard apparatus: functional strong bisimulation, a special case of the
  simulation/bisimulation methodology for finite abstractions.
  References: Manolios--Namjoshi--Sumners, CAV 1999, pp. 369--379;
  Schmuck--Raisch, arXiv:1402.3506, Definitions 4--5 and Section VI.
  We formalize the discrete step-level rule, not asynchronous l-completeness,
  stuttering, or an algorithm that synthesizes an abstraction for every system.

  All abstraction obligations are local: step preservation, step lifting,
  and preservation/reflection of the good-state predicate. Reachability and
  decision completeness are conclusions, not fields of the abstraction.
-/
module

public import PPGraph.Decision.ReachabilityRefutation
public import Mathlib.Data.Finset.Lattice.Fold

@[expose] public section

set_option autoImplicit false

namespace RepairFeasibility

variable {State Abstract : Type}

structure StepSimulation (step : State → State → Prop) (good : State → Prop)
    (abstractStep : Abstract → Abstract → Prop) (abstractGood : Abstract → Prop) where
  project : State → Abstract
  map_step : ∀ u w, step u w → abstractStep (project u) (project w)
  map_good : ∀ w, good w → abstractGood (project w)

structure ExactAbstraction (step : State → State → Prop) (good : State → Prop)
    (abstractStep : Abstract → Abstract → Prop) (abstractGood : Abstract → Prop)
    extends StepSimulation step good abstractStep abstractGood where
  lift_step : ∀ u a, abstractStep (project u) a →
    ∃ w, step u w ∧ project w = a
  reflect_good : ∀ w, abstractGood (project w) → good w

variable {step : State → State → Prop} {good : State → Prop}
variable {abstractStep : Abstract → Abstract → Prop} {abstractGood : Abstract → Prop}

theorem simulation_maps_reachable
    (S : StepSimulation step good abstractStep abstractGood) {v w : State}
    (hr : Relation.ReflTransGen step v w) :
    Relation.ReflTransGen abstractStep (S.project v) (S.project w) :=
  Relation.ReflTransGen.lift S.project S.map_step v w hr

theorem simulation_maps_reachable_good
    (S : StepSimulation step good abstractStep abstractGood) (v : State)
    (h : ∃ w, Relation.ReflTransGen step v w ∧ good w) :
    ∃ a, Relation.ReflTransGen abstractStep (S.project v) a ∧ abstractGood a := by
  obtain ⟨w, hr, hg⟩ := h
  exact ⟨S.project w, simulation_maps_reachable S hr, S.map_good w hg⟩

/-- Negative certificates transfer even for a one-way over-approximation. -/
theorem simulation_pulls_back_refutation
    (S : StepSimulation step good abstractStep abstractGood) (v : State)
    (I : Abstract → Prop) (h : InvariantRefutation abstractStep abstractGood (S.project v) I) :
    InvariantRefutation step good v (fun w => I (S.project w)) :=
  ⟨h.1, fun u w hu hs => h.2.1 _ _ hu (S.map_step u w hs),
    fun w hw hg => h.2.2 _ hw (S.map_good w hg)⟩

theorem simulation_refutes_concrete
    (S : StepSimulation step good abstractStep abstractGood) (v : State)
    (h : ¬ ∃ a, Relation.ReflTransGen abstractStep (S.project v) a ∧ abstractGood a) :
    ¬ ∃ w, Relation.ReflTransGen step v w ∧ good w :=
  fun hw => h (simulation_maps_reachable_good S v hw)

theorem exactAbstraction_good_iff
    (E : ExactAbstraction step good abstractStep abstractGood) (w : State) :
    good w ↔ abstractGood (E.project w) :=
  ⟨E.map_good w, E.reflect_good w⟩

theorem exactAbstraction_good_constant_on_fibers
    (E : ExactAbstraction step good abstractStep abstractGood) {u w : State}
    (he : E.project u = E.project w) : good u ↔ good w := by
  rw [exactAbstraction_good_iff E u, exactAbstraction_good_iff E w, he]

theorem exactAbstraction_lifts_reachable
    (E : ExactAbstraction step good abstractStep abstractGood) (v : State) {a : Abstract}
    (hr : Relation.ReflTransGen abstractStep (E.project v) a) :
    ∃ w, Relation.ReflTransGen step v w ∧ E.project w = a := by
  induction hr with
  | refl => exact ⟨v, Relation.ReflTransGen.refl, rfl⟩
  | tail _ hs ih =>
    obtain ⟨u, hu, he⟩ := ih
    obtain ⟨w, hw, ha⟩ := E.lift_step u _ (by rwa [he])
    exact ⟨w, hu.tail hw, ha⟩

theorem exactAbstraction_reachable_good_iff
    (E : ExactAbstraction step good abstractStep abstractGood) (v : State) :
    (∃ w, Relation.ReflTransGen step v w ∧ good w) ↔
      ∃ a, Relation.ReflTransGen abstractStep (E.project v) a ∧ abstractGood a := by
  constructor
  · exact simulation_maps_reachable_good E.toStepSimulation v
  · rintro ⟨a, hr, hg⟩
    obtain ⟨w, hw, he⟩ := exactAbstraction_lifts_reachable E v hr
    exact ⟨w, hw, E.reflect_good w (by rwa [he])⟩

theorem exactAbstraction_unreachable_iff
    (E : ExactAbstraction step good abstractStep abstractGood) (v : State) :
    (¬ ∃ w, Relation.ReflTransGen step v w ∧ good w) ↔
      ¬ ∃ a, Relation.ReflTransGen abstractStep (E.project v) a ∧ abstractGood a :=
  not_congr (exactAbstraction_reachable_good_iff E v)

/-- The repair relation in this bridge is actual finite-step reachability. -/
def stepRepairGraph (step : State → State → Prop) (good : State → Prop) : RepairGraph State where
  edges := step
  reach_rel := Relation.ReflTransGen step
  invariant_holds := good

theorem exactAbstraction_noReachableGood_iff
    (E : ExactAbstraction step good abstractStep abstractGood) (v : State) :
    NoReachableGood (stepRepairGraph step good) v ↔
      NoReachableGood (stepRepairGraph abstractStep abstractGood) (E.project v) :=
  exactAbstraction_unreachable_iff E v

theorem exactAbstraction_repair_possible_iff
    (E : ExactAbstraction step good abstractStep abstractGood) (v : State)
    (hv : isolated (stepRepairGraph step good) v) :
    repair_possible (stepRepairGraph step good) v ↔
      repair_possible (stepRepairGraph abstractStep abstractGood) (E.project v) := by
  have ha : isolated (stepRepairGraph abstractStep abstractGood) (E.project v) :=
    fun hg => hv (E.reflect_good v hg)
  rw [← reachable_good_iff_repair_possible (stepRepairGraph step good) v hv,
    ← reachable_good_iff_repair_possible (stepRepairGraph abstractStep abstractGood) (E.project v) ha]
  exact exactAbstraction_reachable_good_iff E v

section FiniteAbstract

variable [Fintype Abstract] [DecidableEq Abstract]
variable [DecidableRel abstractStep] [DecidablePred abstractGood]

def abstractImpossibleTest
    (S : StepSimulation step good abstractStep abstractGood) (v : State) : Bool :=
  unreachableTest abstractStep abstractGood (S.project v)

theorem abstractImpossibleTest_sound
    (S : StepSimulation step good abstractStep abstractGood) (v : State)
    (h : abstractImpossibleTest S v = true) :
    NoReachableGood (stepRepairGraph step good) v :=
  simulation_refutes_concrete S v
    ((unreachableTest_eq_true_iff abstractStep abstractGood (S.project v)).mp h)

theorem abstractImpossibleTest_exact_iff
    (E : ExactAbstraction step good abstractStep abstractGood) (v : State) :
    abstractImpossibleTest E.toStepSimulation v = true ↔
      NoReachableGood (stepRepairGraph step good) v := by
  exact (unreachableTest_eq_true_iff abstractStep abstractGood (E.project v)).trans
    (exactAbstraction_unreachable_iff E v).symm

theorem abstractImpossibleTest_false_iff
    (E : ExactAbstraction step good abstractStep abstractGood) (v : State) :
    abstractImpossibleTest E.toStepSimulation v = false ↔
      ∃ w, Relation.ReflTransGen step v w ∧ good w := by
  classical
  rw [← Bool.not_eq_true, abstractImpossibleTest_exact_iff]
  exact not_not

theorem abstractImpossibleTest_false_iff_repair
    (E : ExactAbstraction step good abstractStep abstractGood) (v : State)
    (hv : isolated (stepRepairGraph step good) v) :
    abstractImpossibleTest E.toStepSimulation v = false ↔
      repair_possible (stepRepairGraph step good) v :=
  (abstractImpossibleTest_false_iff E v).trans
    (reachable_good_iff_repair_possible (stepRepairGraph step good) v hv)

/-- A nonempty intersection of checked invariants is itself a checked invariant. -/
theorem invariantCheck_inf (v : Abstract) (family : Finset (Finset Abstract))
    (hne : family.Nonempty)
    (hall : ∀ K ∈ family, invariantCheck abstractStep abstractGood v K = true) :
    invariantCheck abstractStep abstractGood v (family.inf' hne id) = true := by
  apply (invariantCheck_eq_true_iff abstractStep abstractGood v _).mpr
  refine ⟨?_, ?_, ?_⟩
  · apply (Finset.mem_inf' hne).mpr
    intro K hK
    exact ((invariantCheck_eq_true_iff abstractStep abstractGood v K).mp (hall K hK)).1
  · intro u w hu hs
    apply (Finset.mem_inf' hne).mpr
    intro K hK
    have hI := (invariantCheck_eq_true_iff abstractStep abstractGood v K).mp (hall K hK)
    exact hI.2.1 u w ((Finset.mem_inf' hne).mp hu K hK) hs
  · intro w hw hg
    have hmem := (Finset.mem_inf' hne).mp hw
    obtain ⟨K, hK⟩ := hne
    have hI := (invariantCheck_eq_true_iff abstractStep abstractGood v K).mp (hall K hK)
    exact hI.2.2 w (hmem K hK) hg

/-- Exhaustive finite checking followed by intersection returns a certificate.
    The commutative fold avoids any noncomputable choice of a list ordering. -/
def abstractRefutationSearch
    (S : StepSimulation step good abstractStep abstractGood) (v : State) : Option (Finset Abstract) :=
  if h : (refutingInvariants abstractStep abstractGood (S.project v)).Nonempty then
    some ((refutingInvariants abstractStep abstractGood (S.project v)).inf' h id)
  else none

theorem abstractRefutationSearch_some_checked
    (S : StepSimulation step good abstractStep abstractGood) (v : State) (K : Finset Abstract)
    (h : abstractRefutationSearch S v = some K) :
    invariantCheck abstractStep abstractGood (S.project v) K = true := by
  unfold abstractRefutationSearch at h
  split at h
  next hne =>
    have he := Option.some.inj h
    rw [← he]
    apply invariantCheck_inf (S.project v) _ hne
    intro J hJ
    exact (Finset.mem_filter.mp hJ).2
  next => cases h

theorem abstractRefutationSearch_some_refutes
    (S : StepSimulation step good abstractStep abstractGood) (v : State) (K : Finset Abstract)
    (h : abstractRefutationSearch S v = some K) :
    InvariantRefutation step good v (fun w => S.project w ∈ K) :=
  simulation_pulls_back_refutation S v (· ∈ K)
    ((invariantCheck_eq_true_iff abstractStep abstractGood (S.project v) K).mp
      (abstractRefutationSearch_some_checked S v K h))

theorem abstractRefutationSearch_none_iff
    (S : StepSimulation step good abstractStep abstractGood) (v : State) :
    abstractRefutationSearch S v = none ↔
      ∀ K, invariantCheck abstractStep abstractGood (S.project v) K = false := by
  have hs : abstractRefutationSearch S v = none ↔
      ¬ (refutingInvariants abstractStep abstractGood (S.project v)).Nonempty := by
    unfold abstractRefutationSearch
    split <;> simp_all
  rw [hs]
  constructor
  · intro h K
    apply Bool.eq_false_of_not_eq_true
    intro hk
    exact h ⟨K, Finset.mem_filter.mpr
      ⟨Finset.mem_powerset.mpr (Finset.subset_univ K), hk⟩⟩
  · rintro h ⟨K, hK⟩
    have hk := (Finset.mem_filter.mp hK).2
    rw [h K] at hk
    cases hk

theorem abstractRefutationSearch_complete
    (E : ExactAbstraction step good abstractStep abstractGood) (v : State)
    (h : NoReachableGood (stepRepairGraph step good) v) :
    ∃ K, abstractRefutationSearch E.toStepSimulation v = some K := by
  obtain ⟨K, hk⟩ := invariantCheck_complete abstractStep abstractGood (E.project v)
    ((exactAbstraction_unreachable_iff E v).mp h)
  cases hs : abstractRefutationSearch E.toStepSimulation v with
  | none =>
    have hn := (abstractRefutationSearch_none_iff E.toStepSimulation v).mp hs K
    simp [hk] at hn
  | some J => exact ⟨J, rfl⟩

theorem abstractRefutationSearch_none_iff_reachable_good
    (E : ExactAbstraction step good abstractStep abstractGood) (v : State) :
    abstractRefutationSearch E.toStepSimulation v = none ↔
      ∃ w, Relation.ReflTransGen step v w ∧ good w := by
  classical
  constructor
  · intro hn
    by_contra hg
    obtain ⟨K, hk⟩ := abstractRefutationSearch_complete E v hg
    rw [hn] at hk
    cases hk
  · intro hg
    cases hs : abstractRefutationSearch E.toStepSimulation v with
    | none => rfl
    | some K =>
      exact False.elim
        (invariantRefutation_sound step good v (fun w => E.project w ∈ K)
          (abstractRefutationSearch_some_refutes E.toStepSimulation v K hs) hg)

/-- The negative branch carries the finite certificate; the positive branch
    carries existence. Effective concrete path execution requires a data-level
    lifting operation in addition to the existential bisimulation obligations. -/
inductive AbstractDecision
    (S : StepSimulation step good abstractStep abstractGood) (v : State) : Type
  | reachable (proof : ∃ w, Relation.ReflTransGen step v w ∧ good w)
  | impossible (K : Finset Abstract)
      (checked : invariantCheck abstractStep abstractGood (S.project v) K = true)

def decideByAbstraction
    (E : ExactAbstraction step good abstractStep abstractGood) (v : State) :
    AbstractDecision E.toStepSimulation v :=
  match hs : abstractRefutationSearch E.toStepSimulation v with
  | none => .reachable ((abstractRefutationSearch_none_iff_reachable_good E v).mp hs)
  | some K => .impossible K (abstractRefutationSearch_some_checked E.toStepSimulation v K hs)

theorem abstractDecision_impossible_sound
    (S : StepSimulation step good abstractStep abstractGood) (v : State) (K : Finset Abstract)
    (h : invariantCheck abstractStep abstractGood (S.project v) K = true) :
    NoReachableGood (stepRepairGraph step good) v :=
  invariantRefutation_sound step good v (fun w => S.project w ∈ K)
    (simulation_pulls_back_refutation S v (· ∈ K)
      ((invariantCheck_eq_true_iff abstractStep abstractGood (S.project v) K).mp h))

end FiniteAbstract
end RepairFeasibility

#check @RepairFeasibility.simulation_maps_reachable
#check @RepairFeasibility.simulation_maps_reachable_good
#check @RepairFeasibility.simulation_pulls_back_refutation
#check @RepairFeasibility.simulation_refutes_concrete
#check @RepairFeasibility.exactAbstraction_good_iff
#check @RepairFeasibility.exactAbstraction_good_constant_on_fibers
#check @RepairFeasibility.exactAbstraction_lifts_reachable
#check @RepairFeasibility.exactAbstraction_reachable_good_iff
#check @RepairFeasibility.exactAbstraction_unreachable_iff
#check @RepairFeasibility.exactAbstraction_noReachableGood_iff
#check @RepairFeasibility.exactAbstraction_repair_possible_iff
#check @RepairFeasibility.abstractImpossibleTest_sound
#check @RepairFeasibility.abstractImpossibleTest_exact_iff
#check @RepairFeasibility.abstractImpossibleTest_false_iff
#check @RepairFeasibility.abstractImpossibleTest_false_iff_repair
#check @RepairFeasibility.invariantCheck_inf
#check @RepairFeasibility.abstractRefutationSearch_some_checked
#check @RepairFeasibility.abstractRefutationSearch_some_refutes
#check @RepairFeasibility.abstractRefutationSearch_none_iff
#check @RepairFeasibility.abstractRefutationSearch_complete
#check @RepairFeasibility.abstractRefutationSearch_none_iff_reachable_good
#check @RepairFeasibility.abstractDecision_impossible_sound
