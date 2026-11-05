/- The intersection-sensitive convergence theorem supplies PPG repair witnesses. -/
module

public import PPGraph.HLS.Bounds.Expectation
public import PPGraph.Integration.MoserTardosRepair

@[expose] public section

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option backward.isDefEq.respectTransparency false

open Classical MeasureTheory

namespace HLS

variable {V : Type} [DecidableEq V] [Fintype V] {S : VarSpaces V}
  {ι : Type} [Fintype ι] [DecidableEq ι] [Nonempty ι]

theorem good_state_exists
    (P : MTProcess S ι) (hbad : ∀ i, MeasurableSet (P.bad i)) (p : ι → ℝ)
    (hprob : ∀ i, (Measure.pi (fun a => S.measure a)).real (P.bad i) = p i)
    (hp : ∀ i, 0 < p i) (O : OverlapBounds (Shearer.dependencyGraph P.footprint) p)
    (hInt : ∀ i, O.delta i ≤ (Measure.pi (fun a => S.measure a)).real
      (P.bad i ∩ P.bad (O.matching.mate i)))
    (hc : Shearer.StrictCriterion (Shearer.dependencyGraph P.footprint) O.reduced Finset.univ) :
    ∃ z : MTState S, MTGood P z :=
  exists_MTGood_of_randomInitETLog_lt_top P hbad (randomInitETLog_lt_top P hbad p hprob hp O hInt hc)

theorem good_repair_reachable
    (P : MTProcess S ι) (hbad : ∀ i, MeasurableSet (P.bad i)) (p : ι → ℝ)
    (hprob : ∀ i, (Measure.pi (fun a => S.measure a)).real (P.bad i) = p i)
    (hp : ∀ i, 0 < p i) (O : OverlapBounds (Shearer.dependencyGraph P.footprint) p)
    (hInt : ∀ i, O.delta i ≤ (Measure.pi (fun a => S.measure a)).real
      (P.bad i ∩ P.bad (O.matching.mate i)))
    (hc : Shearer.StrictCriterion (Shearer.dependencyGraph P.footprint) O.reduced Finset.univ)
    (v : MTState S) : ∃ w : MTState S, mtReach P v w ∧ MTGood P w := by
  obtain ⟨z, hz⟩ := good_state_exists P hbad p hprob hp O hInt hc
  exact exists_mtReach_good_of_good_target P z hz v

theorem mtRepairGraph_globally_repairable
    (P : MTProcess S ι) (edges : MTState S → MTState S → Prop)
    (hbad : ∀ i, MeasurableSet (P.bad i)) (p : ι → ℝ)
    (hprob : ∀ i, (Measure.pi (fun a => S.measure a)).real (P.bad i) = p i)
    (hp : ∀ i, 0 < p i) (O : OverlapBounds (Shearer.dependencyGraph P.footprint) p)
    (hInt : ∀ i, O.delta i ≤ (Measure.pi (fun a => S.measure a)).real
      (P.bad i ∩ P.bad (O.matching.mate i)))
    (hc : Shearer.StrictCriterion (Shearer.dependencyGraph P.footprint) O.reduced Finset.univ) :
    globally_repairable (mtRepairGraph P edges) :=
  mtRepairGraph_globally_repairable_of_randomInitETLog_lt_top P edges hbad
    (randomInitETLog_lt_top P hbad p hprob hp O hInt hc)

end HLS

#check @HLS.good_state_exists
#check @HLS.good_repair_reachable
#check @HLS.mtRepairGraph_globally_repairable
