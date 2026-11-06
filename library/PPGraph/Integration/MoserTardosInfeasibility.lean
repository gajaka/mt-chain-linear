/-
  The negative side for the existing MT reachability relation.
  With finite variables and unrestricted existential logs, one good state
  is reachable from every start (the existing constant-log descent theorem).
  Consequently absence of a repair target is exactly global infeasibility.
  Restrictions on permitted logs or updates would define a different relation.
-/
module

public import PPGraph.Integration.MoserTardosRepair
public import PPGraph.Decision.UnsatisfiableCore
public import PPGraph.Decision.FiniteFeasibility

@[expose] public section

set_option autoImplicit false
set_option linter.unusedSectionVars false

namespace RepairFeasibility

variable {V : Type} [DecidableEq V] [Fintype V] {S : VarSpaces V}
  {ι : Type} [Fintype ι] [DecidableEq ι] [Nonempty ι]

def mtSat (P : MTProcess S ι) (i : ι) (z : MTState S) : Prop := z ∉ P.bad i

theorem mt_satisfiable_iff_good_exists (P : MTProcess S ι) :
    Satisfiable (fun _ => True) (mtSat P) Finset.univ ↔ ∃ z, MTGood P z := by
  simp [Satisfiable, mtSat, MTGood]

theorem mt_reachable_good_iff_good_exists (P : MTProcess S ι) (v : MTState S) :
    (∃ w, mtReach P v w ∧ MTGood P w) ↔ ∃ z, MTGood P z := by
  constructor
  · rintro ⟨w, _, hw⟩
    exact ⟨w, hw⟩
  · rintro ⟨z, hz⟩
    exact exists_mtReach_good_of_good_target P z hz v

theorem mt_noReachableGood_iff_infeasible (P : MTProcess S ι)
    (edges : MTState S → MTState S → Prop) (v : MTState S) :
    NoReachableGood (mtRepairGraph P edges) v ↔
      Infeasible (fun _ => True) (mtSat P) Finset.univ := by
  change (¬ ∃ w, mtReach P v w ∧ MTGood P w) ↔ ¬ Satisfiable (fun _ => True) (mtSat P) Finset.univ
  rw [mt_reachable_good_iff_good_exists, mt_satisfiable_iff_good_exists]

theorem mt_no_repair_iff_infeasible (P : MTProcess S ι)
    (edges : MTState S → MTState S → Prop) (v : MTState S)
    (hiso : isolated (mtRepairGraph P edges) v) :
    (¬ repair_possible (mtRepairGraph P edges) v) ↔
      Infeasible (fun _ => True) (mtSat P) Finset.univ := by
  rw [← noReachableGood_iff_no_repair _ v hiso, mt_noReachableGood_iff_infeasible]

theorem mt_infeasible_iff_minimalCore_exists (P : MTProcess S ι) :
    Infeasible (fun _ => True) (mtSat P) Finset.univ ↔
      ∃ K : Finset ι, MinimalCore (fun _ => True) (mtSat P) K := by
  constructor
  · intro h
    obtain ⟨K, _, hK⟩ := minimalCore_exists (fun _ => True) (mtSat P) Finset.univ h
    exact ⟨K, hK⟩
  · rintro ⟨K, hK⟩
    exact minimalCore_blocks_superset (fun _ => True) (mtSat P) (Finset.subset_univ K) hK

theorem mt_core_noReachableGood (P : MTProcess S ι)
    (edges : MTState S → MTState S → Prop) (K : Finset ι)
    (hK : MinimalCore (fun _ => True) (mtSat P) K) (v : MTState S) :
    NoReachableGood (mtRepairGraph P edges) v :=
  (mt_noReachableGood_iff_infeasible P edges v).mpr
    ((mt_infeasible_iff_minimalCore_exists P).mpr ⟨K, hK⟩)

theorem mt_good_exists_excludes_all_cores (P : MTProcess S ι)
    (h : ∃ z, MTGood P z) (K : Finset ι) : ¬ MinimalCore (fun _ => True) (mtSat P) K := by
  intro hK
  exact ((mt_infeasible_iff_minimalCore_exists P).mpr ⟨K, hK⟩)
    ((mt_satisfiable_iff_good_exists P).mpr h)

section FiniteStates

variable [Fintype (MTState S)] [DecidableEq (MTState S)]
variable (P : MTProcess S ι) [∀ i, DecidablePred (mtSat P i)]

theorem mt_goodCount_zero_iff_noReachableGood
    (edges : MTState S → MTState S → Prop) (v : MTState S) :
    goodCount (fun _ => True) (mtSat P) Finset.univ = 0 ↔
      NoReachableGood (mtRepairGraph P edges) v := by
  rw [goodCount_zero_iff, mt_noReachableGood_iff_infeasible]

theorem mt_goodCount_pos_supplies_repair (v : MTState S)
    (h : 0 < goodCount (fun _ => True) (mtSat P) Finset.univ) :
    ∃ w, mtReach P v w ∧ MTGood P w := by
  apply (mt_reachable_good_iff_good_exists P v).mpr
  exact (mt_satisfiable_iff_good_exists P).mp
    ((goodCount_pos_iff (fun _ => True) (mtSat P) Finset.univ).mp h)

end FiniteStates

end RepairFeasibility

#check @RepairFeasibility.mt_satisfiable_iff_good_exists
#check @RepairFeasibility.mt_reachable_good_iff_good_exists
#check @RepairFeasibility.mt_noReachableGood_iff_infeasible
#check @RepairFeasibility.mt_no_repair_iff_infeasible
#check @RepairFeasibility.mt_infeasible_iff_minimalCore_exists
#check @RepairFeasibility.mt_core_noReachableGood
#check @RepairFeasibility.mt_good_exists_excludes_all_cores
#check @RepairFeasibility.mt_goodCount_zero_iff_noReachableGood
#check @RepairFeasibility.mt_goodCount_pos_supplies_repair
