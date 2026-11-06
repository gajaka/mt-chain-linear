/-
  Inductive invariant/barrier certificates for unreachable good states.
  Murali--Trivedi--Zamani, Closure Certificates, arXiv:2305.17519,
  Section 2, Definition 2.1 (barriers and inductive state invariants).
  This is the state-invariant rule, not their stronger closure-certificate theorem.
  Finite certificate checking is complete by enumerating finite invariant sets.
  Semantic completeness for arbitrary sets is not an effective synthesis algorithm.
-/
module

public import PPGraph.Decision.Infeasibility
public import Mathlib.Logic.Relation

@[expose] public section

set_option autoImplicit false

namespace RepairFeasibility

variable {State : Type}

def InductiveSet (step : State → State → Prop) (I : State → Prop) : Prop :=
  ∀ u w, I u → step u w → I w

def InvariantRefutation (step : State → State → Prop) (good : State → Prop)
    (v : State) (I : State → Prop) : Prop :=
  I v ∧ InductiveSet step I ∧ ∀ w, I w → ¬ good w

theorem inductiveSet_reachable (step : State → State → Prop) (I : State → Prop)
    (hc : InductiveSet step I) {v w : State} (hv : I v)
    (hr : Relation.ReflTransGen step v w) : I w := by
  induction hr with
  | refl => exact hv
  | tail _ hs ih => exact hc _ _ ih hs

theorem invariantRefutation_sound (step : State → State → Prop) (good : State → Prop)
    (v : State) (I : State → Prop) (h : InvariantRefutation step good v I) :
    ¬ ∃ w, Relation.ReflTransGen step v w ∧ good w := by
  rintro ⟨w, hr, hg⟩
  exact h.2.2 w (inductiveSet_reachable step I h.2.1 h.1 hr) hg

theorem no_reachable_good_iff_invariantRefutation (step : State → State → Prop)
    (good : State → Prop) (v : State) :
    (¬ ∃ w, Relation.ReflTransGen step v w ∧ good w) ↔
      ∃ I, InvariantRefutation step good v I := by
  constructor
  · intro h
    refine ⟨Relation.ReflTransGen step v, Relation.ReflTransGen.refl, ?_, ?_⟩
    · intro u w hu hs
      exact hu.tail hs
    · intro w hr hg
      exact h ⟨w, hr, hg⟩
  · rintro ⟨I, hI⟩
    exact invariantRefutation_sound step good v I hI

theorem invariantRefutation_noReachableGood (G : RepairGraph State)
    (step : State → State → Prop)
    (hreach : ∀ u w, G.reach_rel u w → Relation.ReflTransGen step u w)
    (v : State) (I : State → Prop)
    (h : InvariantRefutation step G.invariant_holds v I) : NoReachableGood G v := by
  rintro ⟨w, hr, hg⟩
  exact invariantRefutation_sound step G.invariant_holds v I h ⟨w, hreach v w hr, hg⟩

/-- Conserved quantities may obstruct repair even when good states exist elsewhere. -/
theorem conserved_quantity_refutes {Value : Type} (step : State → State → Prop)
    (good : State → Prop) (quantity : State → Value) (target : Value)
    (hkeep : ∀ u w, step u w → quantity w = quantity u)
    (hgood : ∀ w, good w → quantity w = target) (v : State)
    (hstart : quantity v ≠ target) :
    ¬ ∃ w, Relation.ReflTransGen step v w ∧ good w := by
  apply invariantRefutation_sound step good v (fun z => quantity z = quantity v)
  refine ⟨rfl, ?_, ?_⟩
  · intro u w hu hs
    exact (hkeep u w hs).trans hu
  · intro w hw hg
    exact hstart (hw.symm.trans (hgood w hg))

theorem nonincreasing_barrier_refutes (step : State → State → Prop)
    (good : State → Prop) (barrier : State → ℝ) (bound : ℝ)
    (hkeep : ∀ u w, step u w → barrier w ≤ barrier u)
    (hgood : ∀ w, good w → bound < barrier w) (v : State)
    (hstart : barrier v ≤ bound) :
    ¬ ∃ w, Relation.ReflTransGen step v w ∧ good w := by
  apply invariantRefutation_sound step good v (fun z => barrier z ≤ bound)
  refine ⟨hstart, ?_, ?_⟩
  · intro u w hu hs
    exact (hkeep u w hs).trans hu
  · intro w hw hg
    exact (not_lt_of_ge hw) (hgood w hg)

/-- The sublevel-set condition in the standard barrier-certificate definition. -/
theorem barrier_sublevel_refutes (step : State → State → Prop)
    (good : State → Prop) (barrier : State → ℝ) (bound : ℝ)
    (hkeep : ∀ u w, barrier u ≤ bound → step u w → barrier w ≤ bound)
    (hgood : ∀ w, good w → bound < barrier w) (v : State)
    (hstart : barrier v ≤ bound) :
    ¬ ∃ w, Relation.ReflTransGen step v w ∧ good w := by
  exact invariantRefutation_sound step good v (fun z => barrier z ≤ bound)
    ⟨hstart, hkeep, fun w hw hg => (not_lt_of_ge hw) (hgood w hg)⟩

section Finite

variable [Fintype State] [DecidableEq State]
variable (step : State → State → Prop) (good : State → Prop)
variable [DecidableRel step] [DecidablePred good]

def invariantCheck (v : State) (K : Finset State) : Bool :=
  decide (v ∈ K ∧ (∀ u ∈ K, ∀ w, step u w → w ∈ K) ∧ ∀ w ∈ K, ¬ good w)

theorem invariantCheck_eq_true_iff (v : State) (K : Finset State) :
    invariantCheck step good v K = true ↔ InvariantRefutation step good v (· ∈ K) := by
  simp only [invariantCheck, decide_eq_true_eq, InvariantRefutation, InductiveSet]
  constructor
  · rintro ⟨hv, hs, hg⟩
    exact ⟨hv, fun u w hu hstep => hs u hu w hstep, hg⟩
  · rintro ⟨hv, hs, hg⟩
    exact ⟨hv, fun u hu w hstep => hs u w hu hstep, hg⟩

theorem invariantCheck_sound (v : State) (K : Finset State)
    (h : invariantCheck step good v K = true) :
    ¬ ∃ w, Relation.ReflTransGen step v w ∧ good w :=
  invariantRefutation_sound step good v (· ∈ K) ((invariantCheck_eq_true_iff step good v K).mp h)

theorem invariantCheck_complete (v : State)
    (h : ¬ ∃ w, Relation.ReflTransGen step v w ∧ good w) :
    ∃ K, invariantCheck step good v K = true := by
  classical
  let K := Finset.univ.filter (Relation.ReflTransGen step v)
  refine ⟨K, (invariantCheck_eq_true_iff step good v K).mpr ?_⟩
  refine ⟨?_, ?_, ?_⟩
  · simp only [K, Finset.mem_filter, Finset.mem_univ, true_and]
    exact Relation.ReflTransGen.refl
  · intro u w hu hs
    have hr : Relation.ReflTransGen step v u := (Finset.mem_filter.mp hu).2
    simp only [K, Finset.mem_filter, Finset.mem_univ, true_and]
    exact hr.tail hs
  · intro w hw hg
    exact h ⟨w, (Finset.mem_filter.mp hw).2, hg⟩

def refutingInvariants (v : State) : Finset (Finset State) :=
  Finset.univ.powerset.filter fun K => invariantCheck step good v K = true

theorem refutingInvariants_nonempty_iff (v : State) :
    (refutingInvariants step good v).Nonempty ↔
      ¬ ∃ w, Relation.ReflTransGen step v w ∧ good w := by
  constructor
  · rintro ⟨K, hK⟩
    exact invariantCheck_sound step good v K (Finset.mem_filter.mp hK).2
  · intro h
    obtain ⟨K, hK⟩ := invariantCheck_complete step good v h
    exact ⟨K, Finset.mem_filter.mpr ⟨Finset.mem_powerset.mpr (Finset.subset_univ K), hK⟩⟩

def unreachableTest (v : State) : Bool := decide ((refutingInvariants step good v).Nonempty)

theorem unreachableTest_eq_true_iff (v : State) :
    unreachableTest step good v = true ↔
      ¬ ∃ w, Relation.ReflTransGen step v w ∧ good w := by
  simp only [unreachableTest, decide_eq_true_eq, refutingInvariants_nonempty_iff]

end Finite

end RepairFeasibility

#check @RepairFeasibility.inductiveSet_reachable
#check @RepairFeasibility.invariantRefutation_sound
#check @RepairFeasibility.no_reachable_good_iff_invariantRefutation
#check @RepairFeasibility.invariantRefutation_noReachableGood
#check @RepairFeasibility.conserved_quantity_refutes
#check @RepairFeasibility.nonincreasing_barrier_refutes
#check @RepairFeasibility.barrier_sublevel_refutes
#check @RepairFeasibility.invariantCheck_eq_true_iff
#check @RepairFeasibility.invariantCheck_sound
#check @RepairFeasibility.invariantCheck_complete
#check @RepairFeasibility.refutingInvariants_nonempty_iff
#check @RepairFeasibility.unreachableTest_eq_true_iff
