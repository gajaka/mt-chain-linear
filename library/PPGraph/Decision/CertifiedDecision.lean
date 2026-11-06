/-
  A finite decision actually returns either a state with its proof or a
  refutation with its proof. A complete admissible-state enumeration is an
  explicit input obligation; a sample cannot be substituted for it.
  Proof fields erase at execution, while state witnesses remain available.
-/
module

public import PPGraph.Decision.RepairDecision

@[expose] public section

set_option autoImplicit false

namespace RepairFeasibility

variable {State C : Type} [DecidableEq C]

inductive FeasibilityResult (allowed : State → Prop) (sat : C → State → Prop)
    (B : Finset C) where
  | witness (z : State) (admissible : allowed z) (satisfies : ∀ c ∈ B, sat c z)
  | refuted (proof : Infeasible allowed sat B)

def FeasibilityResult.isWitness {allowed : State → Prop} {sat : C → State → Prop}
    {B : Finset C} : FeasibilityResult allowed sat B → Bool
  | .witness _ _ _ => true
  | .refuted _ => false

variable (allowed : State → Prop) (sat : C → State → Prop) (B : Finset C)
variable [DecidablePred allowed] [∀ c, DecidablePred (sat c)]

def solve (states : List State) (hcover : ∀ z, allowed z → z ∈ states) :
    FeasibilityResult allowed sat B :=
  match h : search allowed sat B states with
  | some z => .witness z (search_sound allowed sat B states z h).1
      (search_sound allowed sat B states z h).2
  | none => .refuted ((search_none_iff_infeasible allowed sat B states hcover).mp h)

omit [DecidableEq C] [DecidablePred allowed] [∀ c, DecidablePred (sat c)] in
theorem feasibilityResult_isWitness_iff (result : FeasibilityResult allowed sat B) :
    result.isWitness = true ↔ Satisfiable allowed sat B := by
  cases result with
  | witness z ha hs => exact ⟨fun _ => ⟨z, ha, hs⟩, fun _ => rfl⟩
  | refuted hn => simp only [FeasibilityResult.isWitness, Bool.false_eq_true, false_iff]
                  exact hn

theorem solve_isWitness_iff (states : List State)
    (hcover : ∀ z, allowed z → z ∈ states) :
    (solve allowed sat B states hcover).isWitness = true ↔ Satisfiable allowed sat B :=
  feasibilityResult_isWitness_iff allowed sat B _

theorem solve_isRefuted_iff (states : List State)
    (hcover : ∀ z, allowed z → z ∈ states) :
    (solve allowed sat B states hcover).isWitness = false ↔ Infeasible allowed sat B := by
  have h := not_congr (solve_isWitness_iff allowed sat B states hcover)
  simpa only [Bool.not_eq_true, Infeasible] using h

inductive AssessmentResult (allowed : State → Prop) (sat : C → State → Prop)
    (B : Finset C) (criterion : Bool) where
  | certified (accepted : criterion = true) (z : State)
      (admissible : allowed z) (satisfies : ∀ c ∈ B, sat c z)
  | gap (unaccepted : criterion ≠ true) (z : State)
      (admissible : allowed z) (satisfies : ∀ c ∈ B, sat c z)
  | impossible (proof : Infeasible allowed sat B)

def AssessmentResult.region {allowed : State → Prop} {sat : C → State → Prop}
    {B : Finset C} {criterion : Bool} : AssessmentResult allowed sat B criterion → RepairRegion
  | .certified _ _ _ _ => .certified
  | .gap _ _ _ _ => .gap
  | .impossible _ => .impossible

def assess (criterion : Bool) (states : List State)
    (hcover : ∀ z, allowed z → z ∈ states) : AssessmentResult allowed sat B criterion :=
  match solve allowed sat B states hcover with
  | .witness z ha hs => if hc : criterion = true then .certified hc z ha hs else .gap hc z ha hs
  | .refuted hn => .impossible hn

omit [DecidableEq C] [DecidablePred allowed] [∀ c, DecidablePred (sat c)] in
theorem assessmentResult_gap_sound (criterion : Bool)
    (result : AssessmentResult allowed sat B criterion) (h : result.region = .gap) :
    Gap allowed sat B (criterion = true) := by
  cases result with
  | certified _ _ _ _ => cases h
  | gap hc z ha hs => exact ⟨⟨z, ha, hs⟩, hc⟩
  | impossible _ => cases h

omit [DecidableEq C] [DecidablePred allowed] [∀ c, DecidablePred (sat c)] in
theorem assessmentResult_impossible_sound (criterion : Bool)
    (result : AssessmentResult allowed sat B criterion) (h : result.region = .impossible) :
    Infeasible allowed sat B := by
  cases result with
  | certified _ _ _ _ => cases h
  | gap _ _ _ _ => cases h
  | impossible hn => exact hn

omit [DecidableEq C] [DecidablePred allowed] [∀ c, DecidablePred (sat c)] in
theorem assessmentResult_certified_sound (criterion : Bool)
    (result : AssessmentResult allowed sat B criterion) (h : result.region = .certified) :
    criterion = true ∧ Satisfiable allowed sat B := by
  cases result with
  | certified hc z ha hs => exact ⟨hc, z, ha, hs⟩
  | gap _ _ _ _ => cases h
  | impossible _ => cases h

end RepairFeasibility

#check @RepairFeasibility.feasibilityResult_isWitness_iff
#check @RepairFeasibility.solve_isWitness_iff
#check @RepairFeasibility.solve_isRefuted_iff
#check @RepairFeasibility.assessmentResult_gap_sound
#check @RepairFeasibility.assessmentResult_impossible_sound
#check @RepairFeasibility.assessmentResult_certified_sound
