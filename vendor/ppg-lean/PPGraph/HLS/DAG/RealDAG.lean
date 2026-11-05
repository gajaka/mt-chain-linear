/-
  Witness DAGs from the existing counter-driven MT process. They pass
  their own table check on every genuine active prefix. Random
  initialization is the same slot-zero law used by randomInitETLog.
-/
module

public import PPGraph.HLS.DAG.TimeDAG
public import PPGraph.HLS.Encoding.PrefixCheck
public import PPGraph.HLS.Bounds.WitnessBudget
public import PPGraph.MoserTardos.Probability.RandomInitExpectation

@[expose] public section

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option backward.isDefEq.respectTransparency false

open Classical

namespace HLS.WitnessDAG

variable {V : Type} [DecidableEq V] {S : VarSpaces V}
    {ι : Type} [Fintype ι] [DecidableEq ι] [Nonempty ι]

noncomputable def realSchedule (P : MTProcess S ι) (ω : LogSpace S) : ℕ → ι :=
  realC P (initialStateFromLog ω) ω

noncomputable def executionDAG (P : MTProcess S ι) (ω : LogSpace S) (t : ℕ) :
    HLS.WitnessDAG ι :=
  (timeDAG (Shearer.dependencyGraph P.footprint) (realSchedule P ω) (t + 1)).ancestorPrefix
    (timeNode (realSchedule P ω) t)

noncomputable def realDAG (P : MTProcess S ι) (ω : LogSpace S) (t : ℕ) :
    HLS.WitnessDAG ι := (executionDAG P ω t).normalize

theorem executionDAG_valid (P : MTProcess S ι) (ω : LogSpace S) (t : ℕ) :
    (executionDAG P ω t).Valid (Shearer.dependencyGraph P.footprint) :=
  prefix_valid _ _ (timeDAG_valid _ _ _) _

theorem executionDAG_proper (P : MTProcess S ι) (ω : LogSpace S) (t : ℕ) :
    (executionDAG P ω t).Proper :=
  prefix_proper _ _ (timeDAG_timeNode_mem _ _ _ _ (Nat.lt_succ_self t))

theorem realDAG_valid (P : MTProcess S ι) (ω : LogSpace S) (t : ℕ) :
    (realDAG P ω t).Valid (Shearer.dependencyGraph P.footprint) :=
  normalize_valid _ _ (executionDAG_valid P ω t)

theorem realDAG_canonical (P : MTProcess S ι) (ω : LogSpace S) (t : ℕ) :
    (realDAG P ω t).Canonical :=
  normalize_canonical _ _ (executionDAG_valid P ω t)

theorem realDAG_proper (P : MTProcess S ι) (ω : LogSpace S) (t : ℕ) :
    (realDAG P ω t).Proper := normalize_proper _ (executionDAG_proper P ω t)

theorem timeDAG_tableState_agrees (P : MTProcess S ι) (ω : LogSpace S) (n t : ℕ)
    (ht : t < n) (a : V) (ha : a ∈ P.footprint (realSchedule P ω t)) :
    tableState P (timeDAG (Shearer.dependencyGraph P.footprint) (realSchedule P ω) n)
      ω (timeNode (realSchedule P ω) t) a =
        (randStep P (initialStateFromLog ω) ω t).1 a := by
  change atIdx ω a (localIndex P _ _ a) = _
  rw [localIndex_timeDAG P _ n t ht a ha]
  unfold realSchedule
  rw [← randStep_count_eq_filter_card P (initialStateFromLog ω) ω a t]
  exact (randStep_state_eq_atIdx P (initialStateFromLog ω) ω
    (initialStateFromLog_eq_atIdx ω) t a).symm

theorem timeDAG_tableCheck_of_running (P : MTProcess S ι) (ω : LogSpace S) (n : ℕ)
    (hrun : RunningUntil P (initialStateFromLog ω) ω n) :
    ω ∈ tableCheck P (timeDAG (Shearer.dependencyGraph P.footprint) (realSchedule P ω) n) := by
  simp only [tableCheck, Set.mem_iInter]
  intro u hu
  obtain ⟨hut, hulabel⟩ := (timeDAG_node_iff _ _ n u).mp hu
  have huname : timeNode (realSchedule P ω) u.2 = u := Prod.ext hulabel.symm rfl
  rw [← huname]
  change tableState P _ ω (timeNode (realSchedule P ω) u.2) ∈
    P.bad (realSchedule P ω u.2)
  exact (P.dep _ _ _ (fun a ha => timeDAG_tableState_agrees P ω n u.2 hut a ha)).mpr
    (hrun u.2 hut)

theorem executionDAG_tableCheck_of_running (P : MTProcess S ι) (ω : LogSpace S) (t : ℕ)
    (hrun : RunningUntil P (initialStateFromLog ω) ω (t + 1)) :
    ω ∈ tableCheck P (executionDAG P ω t) :=
  tableCheck_subset_prefix P _ _ (timeDAG_tableCheck_of_running P ω (t + 1) hrun)

theorem realDAG_tableCheck_of_running (P : MTProcess S ι) (ω : LogSpace S) (t : ℕ)
    (hrun : RunningUntil P (initialStateFromLog ω) ω (t + 1)) :
    ω ∈ tableCheck P (realDAG P ω t) := by
  rw [realDAG, tableCheck_normalize P _ (executionDAG_valid P ω t)]
  exact executionDAG_tableCheck_of_running P ω t hrun

theorem realDAG_isProperCanonical (P : MTProcess S ι) (ω : LogSpace S) (t : ℕ) :
    IsProperCanonical (Shearer.dependencyGraph P.footprint) Finset.univ
      (realSchedule P ω t) (realDAG P ω t) := by
  refine ⟨realDAG_valid P ω t, realDAG_canonical P ω t, fun _ _ => Finset.mem_univ _, ?_⟩
  let D := executionDAG P ω t
  let r := timeNode (realSchedule P ω) t
  have hr : r ∈ D.nodes :=
    (prefix_node_iff _ r r).mpr
      ⟨timeDAG_timeNode_mem _ _ _ _ (Nat.lt_succ_self t), .refl⟩
  refine ⟨D.canonicalName r, (normalize_node_iff D _).mpr ⟨r, hr, rfl⟩, rfl, ?_⟩
  intro x hx
  obtain ⟨u, hu, hux⟩ := (normalize_node_iff D x).mp hx
  have hur : D.Reach u r := reach_prefix _ r u ((prefix_node_iff _ r u).mp hu).2
  change D.normalize.Reach x (D.canonicalName r)
  rw [← hux]
  exact normalize_reach_forward D u r hur

end HLS.WitnessDAG

#check @HLS.WitnessDAG.executionDAG_valid
#check @HLS.WitnessDAG.executionDAG_proper
#check @HLS.WitnessDAG.realDAG_valid
#check @HLS.WitnessDAG.realDAG_canonical
#check @HLS.WitnessDAG.realDAG_proper
#check @HLS.WitnessDAG.timeDAG_tableState_agrees
#check @HLS.WitnessDAG.timeDAG_tableCheck_of_running
#check @HLS.WitnessDAG.executionDAG_tableCheck_of_running
#check @HLS.WitnessDAG.realDAG_tableCheck_of_running
#check @HLS.WitnessDAG.realDAG_isProperCanonical
