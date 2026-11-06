/-
  Exact inclusion-exclusion counts and positive-weight infeasibility.
  Probability and Computing, Lemma 1.3 (inclusion-exclusion); uses the
  established mathlib theorem Finset.inclusion_exclusion_card_biUnion.
  All intersections are actual event intersections, not graph-only bounds.
  Zero mass implies emptiness only with explicitly positive atom weights.
-/
module

public import PPGraph.Decision.FiniteFeasibility
public import Mathlib.Combinatorics.Enumerative.InclusionExclusion

@[expose] public section

set_option autoImplicit false
set_option linter.unusedSectionVars false

namespace RepairFeasibility

variable {State C : Type} [Fintype State] [DecidableEq State] [DecidableEq C]
variable (allowed : State → Prop) (sat : C → State → Prop) (B : Finset C)
variable [DecidablePred allowed] [∀ c, DecidablePred (sat c)]

def admissibleStates : Finset State := Finset.univ.filter allowed

def rejectedStates (c : C) : Finset State :=
  Finset.univ.filter fun z => allowed z ∧ ¬ sat c z

theorem rejected_union_subset_admissible :
    B.biUnion (rejectedStates allowed sat) ⊆ admissibleStates allowed := by
  intro z hz
  obtain ⟨c, _, hc⟩ := Finset.mem_biUnion.mp hz
  simp only [rejectedStates, Finset.mem_filter, Finset.mem_univ, true_and] at hc
  simpa only [admissibleStates, Finset.mem_filter, Finset.mem_univ, true_and] using hc.1

theorem goodStates_eq_admissible_sdiff_rejected :
    goodStates allowed sat B = admissibleStates allowed \ B.biUnion (rejectedStates allowed sat) := by
  classical
  ext z
  simp [goodStates, admissibleStates, rejectedStates]
  tauto

/-- Signed cardinality formula, with the empty intersection supplied by all admissible states. -/
def exactGoodCount : ℤ :=
  (admissibleStates allowed).card -
    ∑ T : B.powerset.filter (·.Nonempty),
      (-1 : ℤ) ^ (T.val.card + 1) *
        (T.val.inf' (Finset.mem_filter.mp T.property).2 (rejectedStates allowed sat)).card

theorem exactGoodCount_eq_goodCount :
    exactGoodCount allowed sat B = (goodCount allowed sat B : ℤ) := by
  unfold exactGoodCount goodCount
  rw [← Finset.inclusion_exclusion_card_biUnion]
  rw [goodStates_eq_admissible_sdiff_rejected]
  rw [Finset.card_sdiff_of_subset (rejected_union_subset_admissible allowed sat B)]
  exact (Int.ofNat_sub (Finset.card_le_card (rejected_union_subset_admissible allowed sat B))).symm

theorem exactGoodCount_nonneg : 0 ≤ exactGoodCount allowed sat B := by
  rw [exactGoodCount_eq_goodCount]
  exact Int.natCast_nonneg _

theorem exactGoodCount_zero_iff :
    exactGoodCount allowed sat B = 0 ↔ Infeasible allowed sat B := by
  rw [exactGoodCount_eq_goodCount, Int.natCast_eq_zero, goodCount_zero_iff]

theorem exactGoodCount_pos_iff :
    0 < exactGoodCount allowed sat B ↔ Satisfiable allowed sat B := by
  rw [exactGoodCount_eq_goodCount, Int.natCast_pos, goodCount_pos_iff]

def goodMass (weight : State → ℝ) : ℝ := ∑ z ∈ goodStates allowed sat B, weight z

theorem goodMass_zero_of_infeasible (weight : State → ℝ)
    (h : Infeasible allowed sat B) : goodMass allowed sat B weight = 0 := by
  have hc := (goodCount_zero_iff allowed sat B).mpr h
  have he : goodStates allowed sat B = ∅ := Finset.card_eq_zero.mp hc
  simp [goodMass, he]

theorem goodMass_pos_of_satisfiable (weight : State → ℝ)
    (hw : ∀ z, allowed z → 0 < weight z) (h : Satisfiable allowed sat B) :
    0 < goodMass allowed sat B weight := by
  apply Finset.sum_pos
  · intro z hz
    exact hw z ((mem_goodStates allowed sat B z).mp hz).1
  · exact (goodStates_nonempty_iff allowed sat B).mpr h

theorem goodMass_zero_iff_infeasible (weight : State → ℝ)
    (hw : ∀ z, allowed z → 0 < weight z) :
    goodMass allowed sat B weight = 0 ↔ Infeasible allowed sat B := by
  constructor
  · intro hz hs
    have hp := goodMass_pos_of_satisfiable allowed sat B weight hw hs
    linarith
  · exact goodMass_zero_of_infeasible allowed sat B weight

theorem goodMass_pos_iff_satisfiable (weight : State → ℝ)
    (hw : ∀ z, allowed z → 0 < weight z) :
    0 < goodMass allowed sat B weight ↔ Satisfiable allowed sat B := by
  classical
  constructor
  · intro hp
    by_contra hn
    have hz := goodMass_zero_of_infeasible allowed sat B weight hn
    linarith
  · exact goodMass_pos_of_satisfiable allowed sat B weight hw

end RepairFeasibility

#check @RepairFeasibility.rejected_union_subset_admissible
#check @RepairFeasibility.goodStates_eq_admissible_sdiff_rejected
#check @RepairFeasibility.exactGoodCount_eq_goodCount
#check @RepairFeasibility.exactGoodCount_nonneg
#check @RepairFeasibility.exactGoodCount_zero_iff
#check @RepairFeasibility.exactGoodCount_pos_iff
#check @RepairFeasibility.goodMass_zero_of_infeasible
#check @RepairFeasibility.goodMass_pos_of_satisfiable
#check @RepairFeasibility.goodMass_zero_iff_infeasible
#check @RepairFeasibility.goodMass_pos_iff_satisfiable
