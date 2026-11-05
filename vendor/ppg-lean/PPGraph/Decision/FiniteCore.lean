/- Exact finite checking and enumeration of minimal conflict cores. -/
module

public import PPGraph.Decision.FiniteFeasibility
public import PPGraph.Decision.UnsatisfiableCore

@[expose] public section

set_option autoImplicit false

namespace RepairFeasibility

variable {State C : Type} [Fintype State] [DecidableEq State] [DecidableEq C]
variable (allowed : State → Prop) (sat : C → State → Prop)
variable [DecidablePred allowed] [∀ c, DecidablePred (sat c)]

def coreCheck (K : Finset C) : Bool :=
  decide (goodCount allowed sat K = 0 ∧ ∀ c ∈ K, 0 < goodCount allowed sat (K.erase c))

theorem coreCheck_eq_true_iff (K : Finset C) :
    coreCheck allowed sat K = true ↔ MinimalCore allowed sat K := by
  simp only [coreCheck, decide_eq_true_eq, MinimalCore, goodCount_zero_iff,
    goodCount_pos_iff]

def minimalCores (B : Finset C) : Finset (Finset C) :=
  B.powerset.filter fun K => coreCheck allowed sat K = true

theorem mem_minimalCores_iff (B K : Finset C) :
    K ∈ minimalCores allowed sat B ↔ K ⊆ B ∧ MinimalCore allowed sat K := by
  simp only [minimalCores, Finset.mem_filter, Finset.mem_powerset, coreCheck_eq_true_iff]

theorem minimalCores_nonempty_iff (B : Finset C) :
    (minimalCores allowed sat B).Nonempty ↔ Infeasible allowed sat B := by
  constructor
  · rintro ⟨K, hK⟩
    obtain ⟨hKB, hKU⟩ := (mem_minimalCores_iff allowed sat B K).mp hK
    exact minimalCore_blocks_superset allowed sat hKB hKU
  · intro h
    obtain ⟨K, hKB, hKU⟩ := minimalCore_exists allowed sat B h
    exact ⟨K, (mem_minimalCores_iff allowed sat B K).mpr ⟨hKB, hKU⟩⟩

end RepairFeasibility

#check @RepairFeasibility.coreCheck_eq_true_iff
#check @RepairFeasibility.mem_minimalCores_iff
#check @RepairFeasibility.minimalCores_nonempty_iff
