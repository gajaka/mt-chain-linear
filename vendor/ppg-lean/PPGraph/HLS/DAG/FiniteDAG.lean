/- Finite enumeration of canonical witness DAGs with bounded node count. -/
module

public import PPGraph.HLS.Encoding.Normalization
public import Mathlib.Data.Finset.Max

@[expose] public section

set_option autoImplicit false
set_option linter.unusedSectionVars false

open Classical

namespace HLS.WitnessDAG

variable {ι : Type} [Fintype ι] [DecidableEq ι]

theorem canonical_index_lt_card (G : SimpleGraph ι) (D : HLS.WitnessDAG ι)
    (hD : D.Valid G) (hc : D.Canonical) (u : WNode ι) (hu : u ∈ D.nodes) :
    u.2 < D.nodes.card := by
  rw [← labelRank_eq_index_of_canonical G D hD hc u hu]
  exact (labelRank_lt_card G D hD u hu).trans_le
    (Finset.card_le_card (Finset.filter_subset _ _))

noncomputable def nodeUniverse (N : ℕ) : Finset (WNode ι) := Finset.univ ×ˢ Finset.range N

noncomputable def boundedDAGs (N : ℕ) : Finset (HLS.WitnessDAG ι) :=
  (nodeUniverse (ι := ι) N).powerset.biUnion (fun ns =>
    (ns ×ˢ ns).powerset.image (fun es => ⟨ns, es⟩))

theorem mem_boundedDAGs_iff (N : ℕ) (D : HLS.WitnessDAG ι) :
    D ∈ boundedDAGs N ↔ D.nodes ⊆ nodeUniverse N ∧ D.arcs ⊆ D.nodes ×ˢ D.nodes := by
  simp only [boundedDAGs, Finset.mem_biUnion, Finset.mem_powerset, Finset.mem_image]
  constructor
  · rintro ⟨ns, hns, es, hes, hD⟩
    cases hD
    exact ⟨hns, hes⟩
  · rintro ⟨hn, he⟩
    exact ⟨D.nodes, hn, D.arcs, he, by cases D; rfl⟩

theorem mem_boundedDAGs_of_canonical (G : SimpleGraph ι) (D : HLS.WitnessDAG ι)
    (hD : D.Valid G) (hc : D.Canonical) (N : ℕ) (hN : D.nodes.card ≤ N) :
    D ∈ boundedDAGs N := by
  apply (mem_boundedDAGs_iff N D).mpr
  constructor
  · intro u hu
    exact Finset.mem_product.mpr ⟨Finset.mem_univ _,
      Finset.mem_range.mpr ((canonical_index_lt_card G D hD hc u hu).trans_le hN)⟩
  · intro e he
    exact Finset.mem_product.mpr (hD.supported e.1 e.2 he)

def RootedCanonical (G : SimpleGraph ι) (r : WNode ι) (D : HLS.WitnessDAG ι) : Prop :=
  D.Valid G ∧ D.Canonical ∧ r ∈ D.nodes ∧ ∀ u ∈ D.nodes, D.Reach u r

theorem RootedCanonical.proper {G : SimpleGraph ι} {r : WNode ι} {D : HLS.WitnessDAG ι}
    (h : RootedCanonical G r D) : D.Proper := ⟨r, h.2.2.1, h.2.2.2⟩

theorem RootedCanonical.flippedPrefix {G : SimpleGraph ι} {r : WNode ι}
    {D : HLS.WitnessDAG ι} (h : RootedCanonical G r D) (u v : WNode ι)
    (he : D.Edge u v) (hrev : Acyclic (reverseArc D.Edge u v)) (hl : u.1 ≠ v.1) :
    RootedCanonical G r ((D.reverse u v).ancestorPrefix r) := by
  let E := D.reverse u v
  refine ⟨prefix_valid G E (reverse_valid G D h.1 u v he hrev) r,
    prefix_canonical E (reverse_canonical D h.2.1 u v hl) r,
    (prefix_node_iff E r r).mpr ⟨h.2.2.1, .refl⟩, ?_⟩
  intro w hw
  exact reach_prefix E r w ((prefix_node_iff E r w).mp hw).2

theorem prefix_eq_of_nodes_eq (G : SimpleGraph ι) (D : HLS.WitnessDAG ι) (hD : D.Valid G)
    (r : WNode ι) (hnode : (D.ancestorPrefix r).nodes = D.nodes) :
    D.ancestorPrefix r = D := by
  have harc : (D.ancestorPrefix r).arcs = D.arcs := by
    ext e
    simp only [ancestorPrefix, Finset.mem_filter]
    constructor
    · exact And.left
    · intro he
      have hv := (hD.supported e.1 e.2 he).2
      have hvprefix := hnode.symm ▸ hv
      exact ⟨he, ((prefix_node_iff D r e.2).mp hvprefix).2⟩
  have heta : D.ancestorPrefix r =
      ⟨(D.ancestorPrefix r).nodes, (D.ancestorPrefix r).arcs⟩ := rfl
  rw [heta, hnode, harc]

end HLS.WitnessDAG

#check @HLS.WitnessDAG.canonical_index_lt_card
#check @HLS.WitnessDAG.mem_boundedDAGs_iff
#check @HLS.WitnessDAG.mem_boundedDAGs_of_canonical
#check @HLS.WitnessDAG.RootedCanonical.proper
#check @HLS.WitnessDAG.RootedCanonical.flippedPrefix
#check @HLS.WitnessDAG.prefix_eq_of_nodes_eq
