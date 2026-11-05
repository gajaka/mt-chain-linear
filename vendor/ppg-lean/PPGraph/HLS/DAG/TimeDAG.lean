/-
  A resampling log gives a witness DAG by orienting dependent occurrences
  in chronological order. The construction is valid for every finite log.
  He--Li--Sun, Section 2.1 (the full witness DAG of an execution).
-/
module

public import PPGraph.HLS.Encoding.NormalizationCheck

@[expose] public section

set_option autoImplicit false
set_option linter.unusedSectionVars false

open Classical

namespace HLS.WitnessDAG

variable {ι : Type} [DecidableEq ι]

def timeNode (C : ℕ → ι) (t : ℕ) : WNode ι := (C t, t)

noncomputable def timeDAG (G : SimpleGraph ι) (C : ℕ → ι) (n : ℕ) : HLS.WitnessDAG ι where
  nodes := (Finset.range n).image (timeNode C)
  arcs := (((Finset.range n).image (timeNode C)) ×ˢ
    ((Finset.range n).image (timeNode C))).filter
      (fun e => e.1.2 < e.2.2 ∧ (e.1.1 = e.2.1 ∨ G.Adj e.1.1 e.2.1))

theorem timeDAG_node_iff (G : SimpleGraph ι) (C : ℕ → ι) (n : ℕ) (u : WNode ι) :
    u ∈ (timeDAG G C n).nodes ↔ u.2 < n ∧ u.1 = C u.2 := by
  simp only [timeDAG, Finset.mem_image]
  constructor
  · rintro ⟨t, ht, rfl⟩
    exact ⟨Finset.mem_range.mp ht, rfl⟩
  · rintro ⟨ht, hlabel⟩
    exact ⟨u.2, Finset.mem_range.mpr ht, Prod.ext hlabel.symm rfl⟩

theorem timeDAG_timeNode_mem (G : SimpleGraph ι) (C : ℕ → ι) (n t : ℕ) (ht : t < n) :
    timeNode C t ∈ (timeDAG G C n).nodes :=
  (timeDAG_node_iff G C n _).mpr ⟨ht, rfl⟩

theorem timeDAG_edge_iff (G : SimpleGraph ι) (C : ℕ → ι) (n : ℕ) (u v : WNode ι) :
    (timeDAG G C n).Edge u v ↔
      u ∈ (timeDAG G C n).nodes ∧ v ∈ (timeDAG G C n).nodes ∧
      u.2 < v.2 ∧ (u.1 = v.1 ∨ G.Adj u.1 v.1) := by
  simp only [Edge, timeDAG, Finset.mem_filter, Finset.mem_product]
  tauto

theorem timeDAG_transGen_lt (G : SimpleGraph ι) (C : ℕ → ι) (n : ℕ)
    (u v : WNode ι) (h : Relation.TransGen (timeDAG G C n).Edge u v) : u.2 < v.2 := by
  induction h with
  | single h => exact ((timeDAG_edge_iff G C n _ _).mp h).2.2.1
  | tail _ h ih => exact ih.trans ((timeDAG_edge_iff G C n _ _).mp h).2.2.1

theorem timeDAG_valid (G : SimpleGraph ι) (C : ℕ → ι) (n : ℕ) :
    (timeDAG G C n).Valid G := by
  refine ⟨?_, ?_, ?_⟩
  · intro u v h
    exact ⟨((timeDAG_edge_iff G C n u v).mp h).1,
      ((timeDAG_edge_iff G C n u v).mp h).2.1⟩
  · intro u h
    exact (Nat.lt_irrefl _) (timeDAG_transGen_lt G C n u u h)
  · intro u hu v hv hne
    constructor
    · intro h
      rcases h with h | h
      · exact ((timeDAG_edge_iff G C n u v).mp h).2.2.2
      · exact (((timeDAG_edge_iff G C n v u).mp h).2.2.2).imp Eq.symm
          (fun h => G.adj_symm h)
    · intro hdep
      have hindex : u.2 ≠ v.2 := by
        intro heq
        have hlabel := ((timeDAG_node_iff G C n u).mp hu).2.trans
          ((congrArg C heq).trans ((timeDAG_node_iff G C n v).mp hv).2.symm)
        exact hne (Prod.ext hlabel heq)
      rcases lt_or_gt_of_ne hindex with hlt | hlt
      · exact Or.inl ((timeDAG_edge_iff G C n u v).mpr ⟨hu, hv, hlt, hdep⟩)
      · exact Or.inr ((timeDAG_edge_iff G C n v u).mpr
          ⟨hv, hu, hlt, hdep.imp Eq.symm (fun h => G.adj_symm h)⟩)

variable {V : Type} [DecidableEq V] {S : VarSpaces V}

theorem priorReaders_timeDAG (P : MTProcess S ι) (C : ℕ → ι) (n t : ℕ)
    (ht : t < n) (a : V) (ha : a ∈ P.footprint (C t)) :
    priorReaders P (timeDAG (Shearer.dependencyGraph P.footprint) C n) (timeNode C t) a =
      ((Finset.range t).filter (fun s => a ∈ P.footprint (C s))).image (timeNode C) := by
  ext u
  constructor
  · intro hu
    obtain ⟨humem, hue, hua⟩ := Finset.mem_filter.mp hu
    obtain ⟨_, _, hut, _⟩ := (timeDAG_edge_iff _ C n u (timeNode C t)).mp hue
    have hulabel := ((timeDAG_node_iff _ C n u).mp humem).2
    exact Finset.mem_image.mpr ⟨u.2,
      Finset.mem_filter.mpr ⟨Finset.mem_range.mpr hut, hulabel ▸ hua⟩,
      Prod.ext hulabel.symm rfl⟩
  · intro hu
    obtain ⟨s, hs, hsu⟩ := Finset.mem_image.mp hu
    obtain ⟨hst, hsa⟩ := Finset.mem_filter.mp hs
    have hst' := Finset.mem_range.mp hst
    subst u
    have hsmem := timeDAG_timeNode_mem (Shearer.dependencyGraph P.footprint) C n s
      (hst'.trans ht)
    exact Finset.mem_filter.mpr ⟨hsmem,
      (timeDAG_edge_iff _ C n _ _).mpr ⟨hsmem, timeDAG_timeNode_mem _ C n t ht,
        hst', dependent_of_shared_variable P _ _ a hsa ha⟩, hsa⟩

theorem localIndex_timeDAG (P : MTProcess S ι) (C : ℕ → ι) (n t : ℕ)
    (ht : t < n) (a : V) (ha : a ∈ P.footprint (C t)) :
    localIndex P (timeDAG (Shearer.dependencyGraph P.footprint) C n) (timeNode C t) a =
      ((Finset.range t).filter (fun s => a ∈ P.footprint (C s))).card := by
  unfold localIndex
  rw [priorReaders_timeDAG P C n t ht a ha]
  exact Finset.card_image_of_injOn (fun _ _ _ _ h => congrArg Prod.snd h)

end HLS.WitnessDAG

#check @HLS.WitnessDAG.timeDAG_node_iff
#check @HLS.WitnessDAG.timeDAG_timeNode_mem
#check @HLS.WitnessDAG.timeDAG_edge_iff
#check @HLS.WitnessDAG.timeDAG_transGen_lt
#check @HLS.WitnessDAG.timeDAG_valid
#check @HLS.WitnessDAG.priorReaders_timeDAG
#check @HLS.WitnessDAG.localIndex_timeDAG
