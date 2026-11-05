/- Witness DAG correspondence for arbitrary MT selection sequences.
   Every active prefix passes its table check; no first-event selector
   appears in this construction and no convergence is assumed. -/
module

public import PPGraph.Integration.Policy.MoserTardos

@[expose] public section

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option backward.isDefEq.respectTransparency false

open Classical HLS HLS.WitnessDAG

namespace MTPolicy.DAG

variable {V : Type} [DecidableEq V] {S : VarSpaces V}
    {ι : Type} [Fintype ι] [DecidableEq ι] [Nonempty ι]

noncomputable def executionDAG (P : MTProcess S ι) (C : ℕ → ι) (_ω : LogSpace S) (t : ℕ) :
    HLS.WitnessDAG ι :=
  (timeDAG (Shearer.dependencyGraph P.footprint) C (t + 1)).ancestorPrefix
    (timeNode C t)

noncomputable def realDAG (P : MTProcess S ι) (C : ℕ → ι) (ω : LogSpace S) (t : ℕ) :
    HLS.WitnessDAG ι := (executionDAG P C ω t).normalize

theorem executionDAG_valid (P : MTProcess S ι) (C : ℕ → ι) (ω : LogSpace S) (t : ℕ) :
    (executionDAG P C ω t).Valid (Shearer.dependencyGraph P.footprint) :=
  prefix_valid _ _ (timeDAG_valid _ _ _) _

theorem executionDAG_proper (P : MTProcess S ι) (C : ℕ → ι) (ω : LogSpace S) (t : ℕ) :
    (executionDAG P C ω t).Proper :=
  prefix_proper _ _ (timeDAG_timeNode_mem _ _ _ _ (Nat.lt_succ_self t))

theorem realDAG_valid (P : MTProcess S ι) (C : ℕ → ι) (ω : LogSpace S) (t : ℕ) :
    (realDAG P C ω t).Valid (Shearer.dependencyGraph P.footprint) :=
  normalize_valid _ _ (executionDAG_valid P C ω t)

theorem realDAG_canonical (P : MTProcess S ι) (C : ℕ → ι) (ω : LogSpace S) (t : ℕ) :
    (realDAG P C ω t).Canonical :=
  normalize_canonical _ _ (executionDAG_valid P C ω t)

theorem realDAG_proper (P : MTProcess S ι) (C : ℕ → ι) (ω : LogSpace S) (t : ℕ) :
    (realDAG P C ω t).Proper := normalize_proper _ (executionDAG_proper P C ω t)

theorem timeDAG_tableState_agrees (P : MTProcess S ι) (C : ℕ → ι) (ω : LogSpace S) (n t : ℕ)
    (ht : t < n) (a : V) (ha : a ∈ P.footprint (C t)) :
    tableState P (timeDAG (Shearer.dependencyGraph P.footprint) C n)
      ω (timeNode C t) a =
        state P C ω t a := by
  change atIdx ω a (localIndex P _ _ a) = _
  rw [localIndex_timeDAG P _ n t ht a ha]
  rfl

theorem timeDAG_tableCheck_of_running (P : MTProcess S ι) (C : ℕ → ι) (ω : LogSpace S) (n : ℕ)
    (hrun : Running P C ω n) :
    ω ∈ tableCheck P (timeDAG (Shearer.dependencyGraph P.footprint) C n) := by
  simp only [tableCheck, Set.mem_iInter]
  intro u hu
  obtain ⟨hut, hulabel⟩ := (timeDAG_node_iff _ _ n u).mp hu
  have huname : timeNode C u.2 = u := Prod.ext hulabel.symm rfl
  rw [← huname]
  change tableState P _ ω (timeNode C u.2) ∈
    P.bad (C u.2)
  exact (P.dep _ _ _ (fun a ha => timeDAG_tableState_agrees P C ω n u.2 hut a ha)).mpr
    (hrun u.2 hut)

theorem executionDAG_tableCheck_of_running (P : MTProcess S ι) (C : ℕ → ι) (ω : LogSpace S) (t : ℕ)
    (hrun : Running P C ω (t + 1)) :
    ω ∈ tableCheck P (executionDAG P C ω t) :=
  tableCheck_subset_prefix P _ _ (timeDAG_tableCheck_of_running P C ω (t + 1) hrun)

theorem realDAG_tableCheck_of_running (P : MTProcess S ι) (C : ℕ → ι) (ω : LogSpace S) (t : ℕ)
    (hrun : Running P C ω (t + 1)) :
    ω ∈ tableCheck P (realDAG P C ω t) := by
  rw [realDAG, tableCheck_normalize P _ (executionDAG_valid P C ω t)]
  exact executionDAG_tableCheck_of_running P C ω t hrun

theorem realDAG_isProperCanonical (P : MTProcess S ι) (C : ℕ → ι) (ω : LogSpace S) (t : ℕ) :
    IsProperCanonical (Shearer.dependencyGraph P.footprint) Finset.univ
      (C t) (realDAG P C ω t) := by
  refine ⟨realDAG_valid P C ω t, realDAG_canonical P C ω t, fun _ _ => Finset.mem_univ _, ?_⟩
  let D := executionDAG P C ω t
  let r := timeNode C t
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

theorem labelPrior_execution_root (P : MTProcess S ι) (C : ℕ → ι) (ω : LogSpace S) (t : ℕ) :
    (executionDAG P C ω t).labelPrior (timeNode C t) =
      ((Finset.range t).filter (fun s => C s = C t)).image
        (timeNode C) := by
  let C := C
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

theorem labelRank_execution_root (P : MTProcess S ι) (C : ℕ → ι) (ω : LogSpace S) (t : ℕ) :
    (executionDAG P C ω t).labelRank (timeNode C t) =
      earlierLabelCount C t := by
  rw [labelRank, labelPrior_execution_root]
  exact Finset.card_image_of_injOn (fun _ _ _ _ h => congrArg Prod.snd h)

noncomputable def realRoot (_P : MTProcess S ι) (C : ℕ → ι) (_ω : LogSpace S) (t : ℕ) : WNode ι :=
  (C t, earlierLabelCount C t)

theorem realRoot_eq_canonicalName (P : MTProcess S ι) (C : ℕ → ι) (ω : LogSpace S) (t : ℕ) :
    realRoot P C ω t = (executionDAG P C ω t).canonicalName
      (timeNode C t) := by
  exact Prod.ext rfl (labelRank_execution_root P C ω t).symm

theorem realRoot_mem (P : MTProcess S ι) (C : ℕ → ι) (ω : LogSpace S) (t : ℕ) :
    realRoot P C ω t ∈ (realDAG P C ω t).nodes := by
  rw [realRoot_eq_canonicalName P C ω t]
  apply (normalize_node_iff _ _).mpr
  exact ⟨_, (prefix_node_iff _ _ _).mpr
    ⟨timeDAG_timeNode_mem _ _ _ _ (Nat.lt_succ_self t), .refl⟩, rfl⟩

theorem realDAG_reach_root (P : MTProcess S ι) (C : ℕ → ι) (ω : LogSpace S) (t : ℕ)
    (u : WNode ι) (hu : u ∈ (realDAG P C ω t).nodes) :
    (realDAG P C ω t).Reach u (realRoot P C ω t) := by
  rw [realRoot_eq_canonicalName P C ω t]
  obtain ⟨w, hw, hwu⟩ := (normalize_node_iff _ u).mp hu
  rw [← hwu]
  apply normalize_reach_forward
  exact reach_prefix _ _ w ((prefix_node_iff _ _ w).mp hw).2

theorem realRoot_sink (P : MTProcess S ι) (C : ℕ → ι) (ω : LogSpace S) (t : ℕ) :
    (realDAG P C ω t).Sink (realRoot P C ω t) :=
  proper_root_sink _ _ (realDAG_valid P C ω t) _ (realRoot_mem P C ω t)
    (realDAG_reach_root P C ω t)

end MTPolicy.DAG

#check @MTPolicy.DAG.executionDAG_valid
#check @MTPolicy.DAG.executionDAG_proper
#check @MTPolicy.DAG.realDAG_valid
#check @MTPolicy.DAG.realDAG_canonical
#check @MTPolicy.DAG.realDAG_proper
#check @MTPolicy.DAG.timeDAG_tableState_agrees
#check @MTPolicy.DAG.timeDAG_tableCheck_of_running
#check @MTPolicy.DAG.executionDAG_tableCheck_of_running
#check @MTPolicy.DAG.realDAG_tableCheck_of_running
#check @MTPolicy.DAG.realDAG_isProperCanonical
#check @MTPolicy.DAG.labelPrior_execution_root
#check @MTPolicy.DAG.labelRank_execution_root
#check @MTPolicy.DAG.realRoot_eq_canonicalName
#check @MTPolicy.DAG.realRoot_mem
#check @MTPolicy.DAG.realDAG_reach_root
#check @MTPolicy.DAG.realRoot_sink
