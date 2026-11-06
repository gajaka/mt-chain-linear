/-
  The root rank remembers the number of earlier resamplings of its label.
  Consequently, two different occurrences of one label produce different
  canonical witness DAGs. No termination assumption is needed.
-/
module

public import PPGraph.HLS.DAG.RealDAG

@[expose] public section

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option backward.isDefEq.respectTransparency false

open Classical

namespace HLS.WitnessDAG

variable {V : Type} [DecidableEq V] {S : VarSpaces V}
    {ι : Type} [Fintype ι] [DecidableEq ι] [Nonempty ι]

noncomputable def earlierLabelCount (C : ℕ → ι) (t : ℕ) : ℕ :=
  ((Finset.range t).filter (fun s => C s = C t)).card

theorem labelPrior_execution_root (P : MTProcess S ι) (ω : LogSpace S) (t : ℕ) :
    (executionDAG P ω t).labelPrior (timeNode (realSchedule P ω) t) =
      ((Finset.range t).filter (fun s => realSchedule P ω s = realSchedule P ω t)).image
        (timeNode (realSchedule P ω)) := by
  let C := realSchedule P ω
  let D := timeDAG (Shearer.dependencyGraph P.footprint) C (t + 1)
  ext u
  constructor
  · intro hu
    obtain ⟨humem, hulabel, hue⟩ := Finset.mem_filter.mp hu
    obtain ⟨hue, _⟩ := (prefix_edge_iff D _ u _).mp hue
    obtain ⟨_, _, hut, _⟩ := (timeDAG_edge_iff _ C _ u _).mp hue
    have humem' := ((prefix_node_iff D _ u).mp humem).1
    have hulabel' := ((timeDAG_node_iff _ C _ u).mp humem').2
    refine Finset.mem_image.mpr ⟨u.2, Finset.mem_filter.mpr ⟨Finset.mem_range.mpr hut, ?_⟩,
      Prod.ext hulabel'.symm rfl⟩
    exact hulabel'.symm.trans hulabel
  · intro hu
    obtain ⟨s, hs, hsu⟩ := Finset.mem_image.mp hu
    obtain ⟨hst, hlabel⟩ := Finset.mem_filter.mp hs
    have hst' := Finset.mem_range.mp hst
    subst u
    have hsmem := timeDAG_timeNode_mem (Shearer.dependencyGraph P.footprint) C (t + 1) s
      (by omega)
    have hroot := timeDAG_timeNode_mem (Shearer.dependencyGraph P.footprint) C (t + 1) t
      (Nat.lt_succ_self t)
    have hedge : D.Edge (timeNode C s) (timeNode C t) :=
      (timeDAG_edge_iff _ C _ _ _).mpr ⟨hsmem, hroot, hst', Or.inl hlabel⟩
    exact Finset.mem_filter.mpr ⟨
      (prefix_node_iff D _ _).mpr ⟨hsmem, (Relation.ReflTransGen.refl).head hedge⟩,
      hlabel, (prefix_edge_iff D _ _ _).mpr ⟨hedge, .refl⟩⟩

theorem labelRank_execution_root (P : MTProcess S ι) (ω : LogSpace S) (t : ℕ) :
    (executionDAG P ω t).labelRank (timeNode (realSchedule P ω) t) =
      earlierLabelCount (realSchedule P ω) t := by
  rw [labelRank, labelPrior_execution_root]
  exact Finset.card_image_of_injOn (fun _ _ _ _ h => congrArg Prod.snd h)

noncomputable def realRoot (P : MTProcess S ι) (ω : LogSpace S) (t : ℕ) : WNode ι :=
  (realSchedule P ω t, earlierLabelCount (realSchedule P ω) t)

theorem realRoot_eq_canonicalName (P : MTProcess S ι) (ω : LogSpace S) (t : ℕ) :
    realRoot P ω t = (executionDAG P ω t).canonicalName
      (timeNode (realSchedule P ω) t) := by
  exact Prod.ext rfl (labelRank_execution_root P ω t).symm

theorem realRoot_mem (P : MTProcess S ι) (ω : LogSpace S) (t : ℕ) :
    realRoot P ω t ∈ (realDAG P ω t).nodes := by
  rw [realRoot_eq_canonicalName P ω t]
  apply (normalize_node_iff _ _).mpr
  exact ⟨_, (prefix_node_iff _ _ _).mpr
    ⟨timeDAG_timeNode_mem _ _ _ _ (Nat.lt_succ_self t), .refl⟩, rfl⟩

theorem realDAG_reach_root (P : MTProcess S ι) (ω : LogSpace S) (t : ℕ)
    (u : WNode ι) (hu : u ∈ (realDAG P ω t).nodes) :
    (realDAG P ω t).Reach u (realRoot P ω t) := by
  rw [realRoot_eq_canonicalName P ω t]
  obtain ⟨w, hw, hwu⟩ := (normalize_node_iff _ u).mp hu
  rw [← hwu]
  apply normalize_reach_forward
  exact reach_prefix _ _ w ((prefix_node_iff _ _ w).mp hw).2

theorem realRoot_sink (P : MTProcess S ι) (ω : LogSpace S) (t : ℕ) :
    (realDAG P ω t).Sink (realRoot P ω t) :=
  proper_root_sink _ _ (realDAG_valid P ω t) _ (realRoot_mem P ω t)
    (realDAG_reach_root P ω t)

theorem earlierLabelCount_lt (C : ℕ → ι) (s t : ℕ) (hst : s < t) (hlabel : C s = C t) :
    earlierLabelCount C s < earlierLabelCount C t := by
  apply Finset.card_lt_card
  apply lt_of_le_of_ne
  · intro k hk
    obtain ⟨hks, hklabel⟩ := Finset.mem_filter.mp hk
    exact Finset.mem_filter.mpr
      ⟨Finset.mem_range.mpr ((Finset.mem_range.mp hks).trans hst), hklabel.trans hlabel⟩
  · intro heq
    have hs : s ∈ (Finset.range t).filter (fun k => C k = C t) :=
      Finset.mem_filter.mpr ⟨Finset.mem_range.mpr hst, hlabel⟩
    have hself := (Finset.mem_filter.mp (heq.symm ▸ hs)).1
    exact Nat.lt_irrefl s (Finset.mem_range.mp hself)

theorem realDAG_ne_of_lt (P : MTProcess S ι) (ω : LogSpace S) (s t : ℕ)
    (hst : s < t) (hlabel : realSchedule P ω s = realSchedule P ω t) :
    realDAG P ω s ≠ realDAG P ω t := by
  intro heq
  have hsink : (realDAG P ω t).Sink (realRoot P ω s) := heq ▸ realRoot_sink P ω s
  have hroot := sink_eq_root (realDAG P ω t) (realRoot P ω t) (realRoot P ω s)
    (realDAG_reach_root P ω t) hsink
  have hcount : earlierLabelCount (realSchedule P ω) s =
      earlierLabelCount (realSchedule P ω) t := congrArg Prod.snd hroot
  exact (Nat.ne_of_lt (earlierLabelCount_lt _ s t hst hlabel)) hcount

end HLS.WitnessDAG

#check @HLS.WitnessDAG.labelPrior_execution_root
#check @HLS.WitnessDAG.labelRank_execution_root
#check @HLS.WitnessDAG.realRoot_eq_canonicalName
#check @HLS.WitnessDAG.realRoot_mem
#check @HLS.WitnessDAG.realDAG_reach_root
#check @HLS.WitnessDAG.realRoot_sink
#check @HLS.WitnessDAG.earlierLabelCount_lt
#check @HLS.WitnessDAG.realDAG_ne_of_lt
