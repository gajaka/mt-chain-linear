/-
  Constructive finite-abstraction repair, using the standard bisimulation
  apparatus of PPGraphFiniteAbstraction. The concrete state space may be infinite.
  A supplied executable state enumeration and local step-realization function
  turn the semantic path-lifting theorem into a returned concrete repair trace.
  No concrete target is extracted using Classical.choose.
  Enumeration is exhaustive, not a polynomial-time algorithm.
-/
module

public import PPGraph.Decision.Abstraction
public import Mathlib.Data.Nat.Find

@[expose] public section

set_option autoImplicit false

namespace RepairFeasibility

variable {State Abstract : Type}

def GoodPath (step : State → State → Prop) (good : State → Prop) :
    State → List State → Prop
  | v, [] => good v
  | v, w :: rest => step v w ∧ GoodPath step good w rest

def pathTarget : State → List State → State
  | v, [] => v
  | _, w :: rest => pathTarget w rest

theorem goodPath_target (step : State → State → Prop) (good : State → Prop)
    (v : State) (trace : List State) (h : GoodPath step good v trace) :
    Relation.ReflTransGen step v (pathTarget v trace) ∧ good (pathTarget v trace) := by
  induction trace generalizing v with
  | nil => exact ⟨Relation.ReflTransGen.refl, h⟩
  | cons w rest ih =>
    obtain ⟨hr, hg⟩ := ih w h.2
    exact ⟨hr.head h.1, hg⟩

theorem reachable_good_iff_goodPath (step : State → State → Prop)
    (good : State → Prop) (v : State) :
    (∃ w, Relation.ReflTransGen step v w ∧ good w) ↔
      ∃ trace, GoodPath step good v trace := by
  constructor
  · rintro ⟨w, hr, hg⟩
    refine hr.head_induction_on ⟨[], hg⟩ ?_
    intro u z hs _ ih
    obtain ⟨rest, hrest⟩ := ih
    exact ⟨z :: rest, hs, hrest⟩
  · rintro ⟨trace, ht⟩
    exact ⟨pathTarget v trace, goodPath_target step good v trace ht⟩

section PathSearch

variable [DecidableEq Abstract]
variable (abstractStep : Abstract → Abstract → Prop) (abstractGood : Abstract → Prop)
variable [DecidableRel abstractStep] [DecidablePred abstractGood]
variable (enumeration : List Abstract)

/-- List-based enumeration is executable; no ordering is chosen from a quotient. -/
def boundedPaths : ℕ → Abstract → List (List Abstract)
  | 0, v => if abstractGood v then [[]] else []
  | n + 1, v => (if abstractGood v then [[]] else []) ++
      enumeration.flatMap (fun w => if abstractStep v w then
        (boundedPaths n w).map (w :: ·) else [])

omit [DecidableEq Abstract] in
theorem mem_boundedPaths_iff (hcover : ∀ a, a ∈ enumeration)
    (budget : ℕ) (v : Abstract) (trace : List Abstract) :
    trace ∈ boundedPaths abstractStep abstractGood enumeration budget v ↔
      GoodPath abstractStep abstractGood v trace ∧ trace.length ≤ budget := by
  induction budget generalizing v trace with
  | zero =>
    cases trace <;> simp [boundedPaths, GoodPath]
  | succ n ih =>
    cases trace with
    | nil => simp [boundedPaths, GoodPath]
    | cons w rest =>
      simp [boundedPaths, GoodPath, ih, hcover, and_assoc, and_left_comm, and_comm]

omit [DecidableEq Abstract] in
theorem boundedPaths_eventually_nonempty (hcover : ∀ a, a ∈ enumeration)
    (v : Abstract) (h : ∃ w, Relation.ReflTransGen abstractStep v w ∧ abstractGood w) :
    ∃ budget, boundedPaths abstractStep abstractGood enumeration budget v ≠ [] := by
  obtain ⟨trace, ht⟩ := (reachable_good_iff_goodPath abstractStep abstractGood v).mp h
  refine ⟨trace.length, ?_⟩
  have hm := (mem_boundedPaths_iff abstractStep abstractGood enumeration hcover
    trace.length v trace).mpr ⟨ht, le_rfl⟩
  intro he
  rw [he] at hm
  cases hm

/-- Nat.find executes increasing finite searches; the preceding theorem proves
    termination whenever this positive branch is entered. -/
def findGoodPath (hcover : ∀ a, a ∈ enumeration) (v : Abstract)
    (h : ∃ w, Relation.ReflTransGen abstractStep v w ∧ abstractGood w) :
    {trace : List Abstract // GoodPath abstractStep abstractGood v trace} :=
  let budget := Nat.find (boundedPaths_eventually_nonempty abstractStep abstractGood enumeration hcover v h)
  let candidates := boundedPaths abstractStep abstractGood enumeration budget v
  have hn : candidates ≠ [] := Nat.find_spec
    (boundedPaths_eventually_nonempty abstractStep abstractGood enumeration hcover v h)
  ⟨candidates.head hn,
    ((mem_boundedPaths_iff abstractStep abstractGood enumeration hcover budget v _).mp
      (List.head_mem hn)).1⟩

omit [DecidableEq Abstract] in
theorem findGoodPath_valid (hcover : ∀ a, a ∈ enumeration) (v : Abstract)
    (h : ∃ w, Relation.ReflTransGen abstractStep v w ∧ abstractGood w) :
    GoodPath abstractStep abstractGood v
      (findGoodPath abstractStep abstractGood enumeration hcover v h).val :=
  (findGoodPath abstractStep abstractGood enumeration hcover v h).property

end PathSearch

variable {step : State → State → Prop} {good : State → Prop}
variable {abstractStep : Abstract → Abstract → Prop} {abstractGood : Abstract → Prop}

structure ExecutableAbstraction (step : State → State → Prop) (good : State → Prop)
    (abstractStep : Abstract → Abstract → Prop) (abstractGood : Abstract → Prop)
    extends StepSimulation step good abstractStep abstractGood where
  realize : State → Abstract → State
  realize_step : ∀ u a, abstractStep (project u) a →
    step u (realize u a) ∧ project (realize u a) = a
  reflect_good : ∀ w, abstractGood (project w) → good w

def ExecutableAbstraction.toExact
    (E : ExecutableAbstraction step good abstractStep abstractGood) :
    ExactAbstraction step good abstractStep abstractGood where
  toStepSimulation := E.toStepSimulation
  lift_step := fun u a hs => ⟨E.realize u a, E.realize_step u a hs⟩
  reflect_good := E.reflect_good

def executeAbstractPath
    (E : ExecutableAbstraction step good abstractStep abstractGood) :
    State → List Abstract → List State
  | _, [] => []
  | v, a :: rest => E.realize v a :: executeAbstractPath E (E.realize v a) rest

theorem executeAbstractPath_valid
    (E : ExecutableAbstraction step good abstractStep abstractGood)
    (v : State) (trace : List Abstract)
    (h : GoodPath abstractStep abstractGood (E.project v) trace) :
    GoodPath step good v (executeAbstractPath E v trace) := by
  induction trace generalizing v with
  | nil => exact E.reflect_good v h
  | cons a rest ih =>
    obtain ⟨hs, he⟩ := E.realize_step v a h.1
    exact ⟨hs, ih _ (by simpa only [he] using h.2)⟩

theorem executeAbstractPath_length
    (E : ExecutableAbstraction step good abstractStep abstractGood)
    (v : State) (trace : List Abstract) :
    (executeAbstractPath E v trace).length = trace.length := by
  induction trace generalizing v with
  | nil => rfl
  | cons a rest ih => simpa only [executeAbstractPath, List.length_cons] using congrArg Nat.succ (ih _)

section FiniteAbstract

variable [Fintype Abstract] [DecidableEq Abstract]
variable [DecidableRel abstractStep] [DecidablePred abstractGood]

inductive ConstructiveRepairDecision
    (E : ExecutableAbstraction step good abstractStep abstractGood) (v : State) : Type
  | repaired (trace : List State) (valid : GoodPath step good v trace)
  | impossible (K : Finset Abstract)
      (checked : invariantCheck abstractStep abstractGood (E.project v) K = true)

def repairByFiniteAbstraction
    (E : ExecutableAbstraction step good abstractStep abstractGood)
    (enumeration : List Abstract) (hcover : ∀ a, a ∈ enumeration) (v : State) :
    ConstructiveRepairDecision E v :=
  match hs : abstractRefutationSearch E.toStepSimulation v with
  | none =>
    let hg := (abstractRefutationSearch_none_iff_reachable_good E.toExact v).mp hs
    let ha := (exactAbstraction_reachable_good_iff E.toExact v).mp hg
    let trace := findGoodPath abstractStep abstractGood enumeration hcover (E.project v) ha
    .repaired (executeAbstractPath E v trace.val)
      (executeAbstractPath_valid E v trace.val trace.property)
  | some K => .impossible K (abstractRefutationSearch_some_checked E.toStepSimulation v K hs)

omit [Fintype Abstract] [DecidableEq Abstract]
  [DecidableRel abstractStep] [DecidablePred abstractGood] in
theorem goodPath_repair_candidates
    (v : State) (trace : List State) (h : GoodPath step good v trace)
    (hv : isolated (stepRepairGraph step good) v) :
    repair_candidates (stepRepairGraph step good) v (pathTarget v trace) := by
  obtain ⟨hr, hg⟩ := goodPath_target step good v trace h
  refine ⟨?_, hr, hg⟩
  intro he
  rw [he] at hg
  exact hv hg

theorem constructiveDecision_impossible_sound
    (E : ExecutableAbstraction step good abstractStep abstractGood)
    (v : State) (K : Finset Abstract)
    (h : invariantCheck abstractStep abstractGood (E.project v) K = true) :
    NoReachableGood (stepRepairGraph step good) v :=
  abstractDecision_impossible_sound E.toStepSimulation v K h

def ConstructiveRepairDecision.isRepaired
    {E : ExecutableAbstraction step good abstractStep abstractGood} {v : State} :
    ConstructiveRepairDecision E v → Bool
  | .repaired _ _ => true
  | .impossible _ _ => false

theorem constructiveDecision_isRepaired_iff
    (E : ExecutableAbstraction step good abstractStep abstractGood) (v : State)
    (result : ConstructiveRepairDecision E v) :
    result.isRepaired = true ↔ ∃ w, Relation.ReflTransGen step v w ∧ good w := by
  cases result with
  | repaired trace ht =>
    exact ⟨fun _ => ⟨pathTarget v trace, goodPath_target step good v trace ht⟩, fun _ => rfl⟩
  | impossible K hc =>
    simp only [ConstructiveRepairDecision.isRepaired, Bool.false_eq_true, false_iff]
    exact constructiveDecision_impossible_sound E v K hc

theorem constructiveDecision_isImpossible_iff
    (E : ExecutableAbstraction step good abstractStep abstractGood) (v : State)
    (result : ConstructiveRepairDecision E v) :
    result.isRepaired = false ↔ NoReachableGood (stepRepairGraph step good) v := by
  rw [← Bool.not_eq_true, constructiveDecision_isRepaired_iff]
  rfl

theorem repairByFiniteAbstraction_spec
    (E : ExecutableAbstraction step good abstractStep abstractGood)
    (enumeration : List Abstract) (hcover : ∀ a, a ∈ enumeration) (v : State) :
    (repairByFiniteAbstraction E enumeration hcover v).isRepaired = true ↔
      ∃ w, Relation.ReflTransGen step v w ∧ good w :=
  constructiveDecision_isRepaired_iff E v _

end FiniteAbstract
end RepairFeasibility

#check @RepairFeasibility.goodPath_target
#check @RepairFeasibility.reachable_good_iff_goodPath
#check @RepairFeasibility.mem_boundedPaths_iff
#check @RepairFeasibility.boundedPaths_eventually_nonempty
#check @RepairFeasibility.findGoodPath_valid
#check @RepairFeasibility.executeAbstractPath_valid
#check @RepairFeasibility.executeAbstractPath_length
#check @RepairFeasibility.goodPath_repair_candidates
#check @RepairFeasibility.constructiveDecision_impossible_sound
#check @RepairFeasibility.constructiveDecision_isRepaired_iff
#check @RepairFeasibility.constructiveDecision_isImpossible_iff
#check @RepairFeasibility.repairByFiniteAbstraction_spec
