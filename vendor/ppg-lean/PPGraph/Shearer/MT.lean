/-
  PPGraphShearerMT.lean

  Shearer's strict existence criterion for the existing Moser-Tardos state
  model. The dependency hypothesis is derived from the product measure and
  each bad event's footprint; it is not an extra assumption on the process.

  Positive probability supplies a good target. The existing constant-log
  argument then supplies existential MT reachability from arbitrary starts.
  This file does not assert almost-sure termination or an expected resampling
  bound under Shearer's criterion, or preservation of a separate certified core.
-/

module

public import PPGraph.Shearer.Basic
public import PPGraph.Integration.MoserTardosRepair
public import PPGraph.MoserTardos.Probability.Probability

@[expose] public section

set_option autoImplicit false
set_option linter.unusedSectionVars false
-- MTState and its measurable-space instance are definitions of the underlying
-- Pi space; allow elaboration to unfold those aliases when matching measures.
set_option backward.isDefEq.respectTransparency false

open MeasureTheory Classical

namespace Shearer

variable {V : Type} [DecidableEq V] [Fintype V] {S : VarSpaces V}
    {ι : Type} [Fintype ι] [DecidableEq ι]

/-- Avoiding a finite collection of bad events depends only on the union
of their footprints. -/
theorem mt_all_pass_depends_on (P : MTProcess S ι) (J : Finset ι) :
    depends_only_on (all_pass P.bad J) (J.biUnion P.footprint) := by
  intro ω ω' hagree
  simp only [all_pass, pass_event, Set.mem_iInter, Set.mem_compl_iff]
  apply forall_congr'
  intro i
  apply forall_congr'
  intro hi
  apply not_congr
  exact P.dep i ω ω' (fun v hv => hagree v (Finset.mem_biUnion.mpr ⟨i, hi, hv⟩))

#check @mt_all_pass_depends_on

/-- Disjoint footprints give the ordinary dependency hypothesis automatically
under the product law on MT states, for any chosen finite event set. -/
theorem mt_lll_independence (P : MTProcess S ι)
    (hbad : ∀ i, MeasurableSet (P.bad i)) (B : Finset ι) :
    lll_independence P.bad (Measure.pi (fun v => S.measure v)) P.footprint B := by
  have : ∀ v, IsProbabilityMeasure (S.measure v) := S.isProb
  intro c _ J hJ
  have hdisj : Disjoint (P.footprint c) (J.biUnion P.footprint) := by
    apply Finset.disjoint_left.mpr
    intro v hvc hvJ
    obtain ⟨j, hj, hvj⟩ := Finset.mem_biUnion.mp hvJ
    have hjdisj : Disjoint (P.footprint c) (P.footprint j) :=
      Finset.disjoint_iff_inter_eq_empty.mpr (hJ j hj).2.2
    exact Finset.disjoint_left.mp hjdisj hvc hvj
  have h := infinitePi_inter_eq_mul_of_dependsOn (fun v => S.measure v) hdisj
    (P.dep c) (hbad c) (mt_all_pass_depends_on P J) (all_pass_measurable P.bad J hbad)
  simpa only [Measure.infinitePi_eq_pi, MTState, instMeasurableSpaceMTState] using h

#check @mt_lll_independence

/-- The event that every modelled bad event is absent is exactly MTGood. -/
theorem mt_good_event_univ_eq (P : MTProcess S ι) :
    good_event P.bad Finset.univ = {z | MTGood P z} := by
  ext z
  simp [good_event, all_pass, pass_event, MTGood]

#check @mt_good_event_univ_eq

/-- Shearer's signed polynomial lower-bounds the actual probability of a good
MT state. The only probability hypotheses are measurable events and upper bounds. -/
theorem mt_good_event_lower_bound (P : MTProcess S ι)
    (hbad : ∀ i, MeasurableSet (P.bad i)) (p : ι → ℝ)
    (hp : ∀ i, event_prob P.bad (Measure.pi (fun v => S.measure v)) i ≤ p i)
    (hcriterion : StrictCriterion (dependencyGraph P.footprint) p Finset.univ) :
    polynomial (dependencyGraph P.footprint) p Finset.univ ≤
      (Measure.pi (fun v => S.measure v) {z | MTGood P z}).toReal := by
  have : ∀ v, IsProbabilityMeasure (S.measure v) := S.isProb
  have : IsProbabilityMeasure (Measure.pi (fun v => S.measure v) : Measure (MTState S)) :=
    Measure.pi.instIsProbabilityMeasure _
  have hindep := mt_lll_independence P hbad Finset.univ
  have hlop := independence_implies_lopsidependence P.bad
    (Measure.pi (fun v => S.measure v)) P.footprint Finset.univ hindep
  have h := ppg_good_event_lower_bound P.bad (Measure.pi (fun v => S.measure v))
    P.footprint p Finset.univ hbad hlop (fun i _ => hp i) hcriterion
  rw [mt_good_event_univ_eq] at h
  exact h

#check @mt_good_event_lower_bound

/-- A strict Shearer certificate supplies an actual good MT state. -/
theorem exists_MTGood (P : MTProcess S ι)
    (hbad : ∀ i, MeasurableSet (P.bad i)) (p : ι → ℝ)
    (hp : ∀ i, event_prob P.bad (Measure.pi (fun v => S.measure v)) i ≤ p i)
    (hcriterion : StrictCriterion (dependencyGraph P.footprint) p Finset.univ) :
    ∃ z : MTState S, MTGood P z := by
  have : ∀ v, IsProbabilityMeasure (S.measure v) := S.isProb
  have : IsProbabilityMeasure (Measure.pi (fun v => S.measure v) : Measure (MTState S)) :=
    Measure.pi.instIsProbabilityMeasure _
  have h := ppg_good_state_exists P.bad (Measure.pi (fun v => S.measure v))
    P.footprint p Finset.univ hbad (mt_lll_independence P hbad Finset.univ)
    (fun i _ => hp i) hcriterion
  rw [mt_good_event_univ_eq] at h
  exact h

#check @exists_MTGood

variable [Nonempty ι]

/-- The good target gives an existential MT path from every starting state.
The realizing log is not claimed to have positive probability. -/
theorem exists_mtReach_good (P : MTProcess S ι)
    (hbad : ∀ i, MeasurableSet (P.bad i)) (p : ι → ℝ)
    (hp : ∀ i, event_prob P.bad (Measure.pi (fun v => S.measure v)) i ≤ p i)
    (hcriterion : StrictCriterion (dependencyGraph P.footprint) p Finset.univ)
    (v : MTState S) : ∃ w : MTState S, mtReach P v w ∧ MTGood P w := by
  obtain ⟨z, hz⟩ := exists_MTGood P hbad p hp hcriterion
  exact exists_mtReach_good_of_good_target P z hz v

#check @exists_mtReach_good

/-- Shearer supplies the good target required by the existing abstract repair
bridge. This is existential reachability, not a randomized runtime conclusion. -/
theorem mtRepairGraph_globally_repairable (P : MTProcess S ι)
    (edges : MTState S → MTState S → Prop)
    (hbad : ∀ i, MeasurableSet (P.bad i)) (p : ι → ℝ)
    (hp : ∀ i, event_prob P.bad (Measure.pi (fun v => S.measure v)) i ≤ p i)
    (hcriterion : StrictCriterion (dependencyGraph P.footprint) p Finset.univ) :
    globally_repairable (mtRepairGraph P edges) := by
  obtain ⟨z, hz⟩ := exists_MTGood P hbad p hp hcriterion
  exact mtRepairGraph_globally_repairable_of_good_target P edges z hz

#check @mtRepairGraph_globally_repairable

end Shearer
