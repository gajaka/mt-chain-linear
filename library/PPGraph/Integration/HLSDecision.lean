/-
  Evidence compatibility: the established HLS positive guarantee cannot
  coexist with a genuine infeasibility/refutation certificate.
  HLSCertified bundles only its actual probability/intersection hypotheses;
  repairability and the runtime bound are conclusions, never certificate fields.
-/
module

public import PPGraph.Integration.HLSRepair
public import PPGraph.Integration.MoserTardosInfeasibility
public import PPGraph.Decision.RepairDecision

@[expose] public section

set_option autoImplicit false
set_option linter.unusedSectionVars false

open MeasureTheory

namespace RepairFeasibility

variable {V : Type} [DecidableEq V] [Fintype V] {S : VarSpaces V}
  {ι : Type} [Fintype ι] [DecidableEq ι] [Nonempty ι]

def HLSCertified (P : MTProcess S ι) : Prop :=
  (∀ i, MeasurableSet (P.bad i)) ∧
  ∃ p : ι → ℝ,
    (∀ i, (Measure.pi (fun a => S.measure a)).real (P.bad i) = p i) ∧
    (∀ i, 0 < p i) ∧
    ∃ O : HLS.OverlapBounds (Shearer.dependencyGraph P.footprint) p,
      (∀ i, O.delta i ≤ (Measure.pi (fun a => S.measure a)).real
        (P.bad i ∩ P.bad (O.matching.mate i))) ∧
      Shearer.StrictCriterion (Shearer.dependencyGraph P.footprint) O.reduced Finset.univ

theorem hlsCertified_good_exists (P : MTProcess S ι) (h : HLSCertified P) :
    ∃ z, MTGood P z := by
  obtain ⟨hm, p, hp, hpos, O, hInt, hc⟩ := h
  exact HLS.good_state_exists P hm p hp hpos O hInt hc

theorem hlsCertified_satisfiable (P : MTProcess S ι) (h : HLSCertified P) :
    Satisfiable (fun _ => True) (mtSat P) Finset.univ :=
  (mt_satisfiable_iff_good_exists P).mpr (hlsCertified_good_exists P h)

theorem hlsCertified_repair_reachable (P : MTProcess S ι) (h : HLSCertified P)
    (v : MTState S) : ∃ w, mtReach P v w ∧ MTGood P w :=
  (mt_reachable_good_iff_good_exists P v).mpr (hlsCertified_good_exists P h)

theorem infeasible_excludes_hlsCertified (P : MTProcess S ι)
    (h : Infeasible (fun _ => True) (mtSat P) Finset.univ) : ¬ HLSCertified P :=
  fun hc => h (hlsCertified_satisfiable P hc)

theorem hlsCertified_excludes_all_cores (P : MTProcess S ι) (h : HLSCertified P)
    (K : Finset ι) : ¬ MinimalCore (fun _ => True) (mtSat P) K :=
  mt_good_exists_excludes_all_cores P (hlsCertified_good_exists P h) K

theorem hlsCertified_excludes_noReachableGood (P : MTProcess S ι)
    (h : HLSCertified P) (edges : MTState S → MTState S → Prop) (v : MTState S) :
    ¬ NoReachableGood (mtRepairGraph P edges) v := by
  intro hn
  exact ((mt_noReachableGood_iff_infeasible P edges v).mp hn) (hlsCertified_satisfiable P h)

theorem hls_extension_gap_iff (P : MTProcess S ι) (earlier : Prop) :
    Gap (fun _ => True) (mtSat P) Finset.univ (earlier ∨ HLSCertified P) ↔
      Gap (fun _ => True) (mtSat P) Finset.univ earlier ∧ ¬ HLSCertified P :=
  gap_after_extension_iff (fun _ => True) (mtSat P) Finset.univ earlier (HLSCertified P)

section FiniteStates

variable [Fintype (MTState S)] [DecidableEq (MTState S)]
variable (P : MTProcess S ι) [∀ i, DecidablePred (mtSat P i)]

/-- A passed HLS check and exact finite search give a complete, sound assessment. -/
theorem finite_mt_classify_impossible_iff (criterion : Bool)
    (hcheck : criterion = true → HLSCertified P)
    (edges : MTState S → MTState S → Prop) (v : MTState S) :
    classify (fun _ => True) (mtSat P) Finset.univ criterion = .impossible ↔
      NoReachableGood (mtRepairGraph P edges) v := by
  rw [classify_impossible_iff _ _ _ criterion (fun hc => hlsCertified_satisfiable P (hcheck hc)),
    mt_noReachableGood_iff_infeasible]

theorem finite_mt_classify_gap_supplies_repair (criterion : Bool) (v : MTState S)
    (h : classify (fun _ => True) (mtSat P) Finset.univ criterion = .gap) :
    criterion ≠ true ∧ ∃ w, mtReach P v w ∧ MTGood P w := by
  have hg := (classify_gap_iff (fun _ => True) (mtSat P) Finset.univ criterion).mp h
  exact ⟨hg.2, (mt_reachable_good_iff_good_exists P v).mpr
    ((mt_satisfiable_iff_good_exists P).mp hg.1)⟩

end FiniteStates

end RepairFeasibility

#check @RepairFeasibility.hlsCertified_good_exists
#check @RepairFeasibility.hlsCertified_satisfiable
#check @RepairFeasibility.hlsCertified_repair_reachable
#check @RepairFeasibility.infeasible_excludes_hlsCertified
#check @RepairFeasibility.hlsCertified_excludes_all_cores
#check @RepairFeasibility.hlsCertified_excludes_noReachableGood
#check @RepairFeasibility.hls_extension_gap_iff
#check @RepairFeasibility.finite_mt_classify_impossible_iff
#check @RepairFeasibility.finite_mt_classify_gap_supplies_repair
