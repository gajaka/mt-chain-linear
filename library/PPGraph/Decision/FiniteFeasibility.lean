/-
  Exact finite-state feasibility and an executable witness search.
  Completeness requires a proved enumeration covering every admissible state.
  Exhausting a partial sample alone is not an impossibility certificate.
-/
module

public import PPGraph.Decision.Infeasibility

@[expose] public section

set_option autoImplicit false
set_option linter.unusedSectionVars false

namespace RepairFeasibility

variable {State C : Type} [DecidableEq C]
variable (allowed : State → Prop) (sat : C → State → Prop) (B : Finset C)
variable [DecidablePred allowed] [∀ c, DecidablePred (sat c)]

def goodTest (z : State) : Bool := decide (allowed z ∧ ∀ c ∈ B, sat c z)

def search (states : List State) : Option State := states.find? (goodTest allowed sat B)

theorem goodTest_eq_true (z : State) :
    goodTest allowed sat B z = true ↔ allowed z ∧ ∀ c ∈ B, sat c z := by
  simp [goodTest]

theorem search_none_iff (states : List State) :
    search allowed sat B states = none ↔
      ∀ z ∈ states, ¬ (allowed z ∧ ∀ c ∈ B, sat c z) := by
  simp [search, goodTest]

theorem search_sound (states : List State) (z : State)
    (h : search allowed sat B states = some z) :
    allowed z ∧ ∀ c ∈ B, sat c z := by
  apply (goodTest_eq_true allowed sat B z).mp
  exact List.find?_some h

theorem search_witness_mem (states : List State) (z : State)
    (h : search allowed sat B states = some z) : z ∈ states :=
  List.mem_of_find?_eq_some h

theorem search_none_iff_infeasible (states : List State)
    (hcover : ∀ z, allowed z → z ∈ states) :
    search allowed sat B states = none ↔ Infeasible allowed sat B := by
  rw [search_none_iff]
  constructor
  · intro h ⟨z, hz, hs⟩
    exact h z (hcover z hz) ⟨hz, hs⟩
  · intro h z _ hs
    exact h ⟨z, hs⟩

theorem search_complete (states : List State)
    (hcover : ∀ z, allowed z → z ∈ states) (h : Satisfiable allowed sat B) :
    ∃ z, search allowed sat B states = some z := by
  cases he : search allowed sat B states with
  | none => exact False.elim (((search_none_iff_infeasible allowed sat B states hcover).mp he) h)
  | some z => exact ⟨z, rfl⟩

section Finite

variable [Fintype State] [DecidableEq State]

def goodStates : Finset State := Finset.univ.filter fun z => allowed z ∧ ∀ c ∈ B, sat c z

def goodCount : ℕ := (goodStates allowed sat B).card

theorem mem_goodStates (z : State) :
    z ∈ goodStates allowed sat B ↔ allowed z ∧ ∀ c ∈ B, sat c z := by
  simp [goodStates]

theorem goodStates_nonempty_iff :
    (goodStates allowed sat B).Nonempty ↔ Satisfiable allowed sat B := by
  simp only [Finset.Nonempty, mem_goodStates, Satisfiable]

theorem goodCount_pos_iff : 0 < goodCount allowed sat B ↔ Satisfiable allowed sat B := by
  rw [goodCount, Finset.card_pos, goodStates_nonempty_iff]

theorem goodCount_zero_iff : goodCount allowed sat B = 0 ↔ Infeasible allowed sat B := by
  have h := not_congr (goodCount_pos_iff allowed sat B)
  simpa only [Nat.not_lt, Nat.le_zero, Infeasible] using h

theorem goodStates_mono_obligations {A D : Finset C} (hAD : A ⊆ D) :
    goodStates allowed sat D ⊆ goodStates allowed sat A := by
  intro z hz
  obtain ⟨ha, hs⟩ := (mem_goodStates allowed sat D z).mp hz
  exact (mem_goodStates allowed sat A z).mpr ⟨ha, fun c hc => hs c (hAD hc)⟩

theorem goodCount_antitone_obligations {A D : Finset C} (hAD : A ⊆ D) :
    goodCount allowed sat D ≤ goodCount allowed sat A :=
  Finset.card_le_card (goodStates_mono_obligations allowed sat hAD)

/-- A finite row-by-row cover is an independently checkable negative certificate. -/
def coverCheck (reject : State → C) : Bool :=
  decide (∀ z, allowed z → reject z ∈ B ∧ ¬ sat (reject z) z)

theorem coverCheck_sound (reject : State → C)
    (h : coverCheck allowed sat B reject = true) : Infeasible allowed sat B := by
  have hc : ∀ z, allowed z → reject z ∈ B ∧ ¬ sat (reject z) z := by
    simpa only [coverCheck, decide_eq_true_eq] using h
  apply (infeasible_iff_unavoidable allowed sat B).mpr
  intro z hz
  exact ⟨reject z, hc z hz⟩

end Finite

end RepairFeasibility

#check @RepairFeasibility.goodTest_eq_true
#check @RepairFeasibility.search_none_iff
#check @RepairFeasibility.search_sound
#check @RepairFeasibility.search_witness_mem
#check @RepairFeasibility.search_none_iff_infeasible
#check @RepairFeasibility.search_complete
#check @RepairFeasibility.mem_goodStates
#check @RepairFeasibility.goodStates_nonempty_iff
#check @RepairFeasibility.goodCount_pos_iff
#check @RepairFeasibility.goodCount_zero_iff
#check @RepairFeasibility.goodStates_mono_obligations
#check @RepairFeasibility.goodCount_antitone_obligations
#check @RepairFeasibility.coverCheck_sound
