/-
  The exact certified / repairable gap / impossible partition.
  "Uncertified" alone is not a semantic region: it includes both the gap and
  impossible instances. For finite decidable models exact counting separates
  them, independently of a supplied sufficient probabilistic criterion.
-/
module

public import PPGraph.Decision.FiniteFeasibility

@[expose] public section

set_option autoImplicit false
set_option linter.unusedSectionVars false

namespace RepairFeasibility

variable {State C : Type} [DecidableEq C]
variable (allowed : State → Prop) (sat : C → State → Prop) (B : Finset C)

def Gap (certified : Prop) : Prop := Satisfiable allowed sat B ∧ ¬ certified

theorem refutation_excludes_certification (certified : Prop)
    (hsound : certified → Satisfiable allowed sat B) (h : Infeasible allowed sat B) :
    ¬ certified := fun hc => h (hsound hc)

theorem certified_or_gap_iff_satisfiable (certified : Prop)
    (hsound : certified → Satisfiable allowed sat B) :
    certified ∨ Gap allowed sat B certified ↔ Satisfiable allowed sat B := by
  classical
  constructor
  · rintro (h | h)
    · exact hsound h
    · exact h.1
  · intro h
    by_cases hc : certified
    · exact Or.inl hc
    · exact Or.inr ⟨h, hc⟩

theorem uncertified_iff_gap_or_impossible (certified : Prop)
    (hsound : certified → Satisfiable allowed sat B) :
    ¬ certified ↔ Gap allowed sat B certified ∨ Infeasible allowed sat B := by
  classical
  constructor
  · intro hc
    by_cases hs : Satisfiable allowed sat B
    · exact Or.inl ⟨hs, hc⟩
    · exact Or.inr hs
  · rintro (h | h)
    · exact h.2
    · exact refutation_excludes_certification allowed sat B certified hsound h

theorem three_regions_exhaustive (certified : Prop) :
    certified ∨ Gap allowed sat B certified ∨ Infeasible allowed sat B := by
  classical
  by_cases hc : certified
  · exact Or.inl hc
  · by_cases hs : Satisfiable allowed sat B
    · exact Or.inr (Or.inl ⟨hs, hc⟩)
    · exact Or.inr (Or.inr hs)

theorem gap_excludes_certification (certified : Prop)
    (h : Gap allowed sat B certified) : ¬ certified := h.2

theorem gap_excludes_impossibility (certified : Prop)
    (h : Gap allowed sat B certified) : ¬ Infeasible allowed sat B :=
  fun hn => hn h.1

theorem extended_certification_sound (first second : Prop)
    (hfirst : first → Satisfiable allowed sat B)
    (hsecond : second → Satisfiable allowed sat B) :
    (first ∨ second) → Satisfiable allowed sat B :=
  fun h => h.elim hfirst hsecond

theorem gap_after_extension_iff (first second : Prop) :
    Gap allowed sat B (first ∨ second) ↔ Gap allowed sat B first ∧ ¬ second := by
  simp only [Gap, not_or, and_assoc]

theorem gap_shrinks_under_extension (first second : Prop) :
    Gap allowed sat B (first ∨ second) → Gap allowed sat B first :=
  fun h => (gap_after_extension_iff allowed sat B first second).mp h |>.1

inductive RepairRegion where
  | certified
  | gap
  | impossible
  deriving DecidableEq

section Finite

variable [Fintype State] [DecidableEq State]
variable [DecidablePred allowed] [∀ c, DecidablePred (sat c)]

def classify (criterion : Bool) : RepairRegion :=
  if criterion = true then .certified
  else if goodCount allowed sat B = 0 then .impossible else .gap

theorem classify_certified_iff (criterion : Bool) :
    classify allowed sat B criterion = .certified ↔ criterion = true := by
  by_cases hc : criterion = true
  · simp [classify, hc]
  · by_cases hn : goodCount allowed sat B = 0 <;> simp [classify, hc, hn]

theorem classify_gap_iff (criterion : Bool) :
    classify allowed sat B criterion = .gap ↔ Gap allowed sat B (criterion = true) := by
  classical
  by_cases hc : criterion = true
  · simp [classify, hc, Gap]
  · simp [classify, hc, goodCount_zero_iff, Gap, Infeasible]

theorem classify_impossible_iff (criterion : Bool)
    (hsound : criterion = true → Satisfiable allowed sat B) :
    classify allowed sat B criterion = .impossible ↔ Infeasible allowed sat B := by
  by_cases hc : criterion = true
  · have hn := satisfiable_not_infeasible allowed sat B (hsound hc)
    simp [classify, hc, hn]
  · simp [classify, hc, goodCount_zero_iff]

theorem classify_certified_sound (criterion : Bool)
    (hsound : criterion = true → Satisfiable allowed sat B)
    (h : classify allowed sat B criterion = .certified) : Satisfiable allowed sat B :=
  hsound ((classify_certified_iff allowed sat B criterion).mp h)

end Finite

end RepairFeasibility

#check @RepairFeasibility.refutation_excludes_certification
#check @RepairFeasibility.certified_or_gap_iff_satisfiable
#check @RepairFeasibility.uncertified_iff_gap_or_impossible
#check @RepairFeasibility.three_regions_exhaustive
#check @RepairFeasibility.gap_excludes_certification
#check @RepairFeasibility.gap_excludes_impossibility
#check @RepairFeasibility.extended_certification_sound
#check @RepairFeasibility.gap_after_extension_iff
#check @RepairFeasibility.gap_shrinks_under_extension
#check @RepairFeasibility.classify_certified_iff
#check @RepairFeasibility.classify_gap_iff
#check @RepairFeasibility.classify_impossible_iff
#check @RepairFeasibility.classify_certified_sound
