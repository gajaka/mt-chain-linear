/-
  Canonical renaming of arbitrary finite witness DAGs. A label's node
  name is its predecessor rank in that label's complete chain. The
  construction preserves arcs, paths, properness and label weights.
-/
module

public import PPGraph.HLS.Encoding.LabelRanks

@[expose] public section

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option backward.isDefEq.respectTransparency false

open Classical

namespace HLS.WitnessDAG

variable {ι : Type} [DecidableEq ι]

noncomputable def normalize (D : HLS.WitnessDAG ι) : HLS.WitnessDAG ι where
  nodes := D.nodes.image D.canonicalName
  arcs := D.arcs.image (fun e => (D.canonicalName e.1, D.canonicalName e.2))

theorem normalize_node_iff (D : HLS.WitnessDAG ι) (x : WNode ι) :
    x ∈ D.normalize.nodes ↔ ∃ u ∈ D.nodes, D.canonicalName u = x := by
  exact Finset.mem_image

theorem normalize_edge_forward (D : HLS.WitnessDAG ι) (u v : WNode ι)
    (h : D.Edge u v) : D.normalize.Edge (D.canonicalName u) (D.canonicalName v) :=
  Finset.mem_image.mpr ⟨(u, v), h, rfl⟩

theorem normalize_edge_witness (G : SimpleGraph ι) (D : HLS.WitnessDAG ι)
    (hD : D.Valid G) (x y : WNode ι) :
    D.normalize.Edge x y ↔ ∃ u ∈ D.nodes, ∃ v ∈ D.nodes,
      D.Edge u v ∧ D.canonicalName u = x ∧ D.canonicalName v = y := by
  constructor
  · intro h
    obtain ⟨e, he, hname⟩ := Finset.mem_image.mp h
    exact ⟨e.1, (hD.supported _ _ he).1, e.2, (hD.supported _ _ he).2,
      he, congrArg Prod.fst hname, congrArg Prod.snd hname⟩
  · rintro ⟨u, _, v, _, h, hx, hy⟩
    exact Finset.mem_image.mpr ⟨(u, v), h, Prod.ext hx hy⟩

noncomputable def sourceNode (D : HLS.WitnessDAG ι) (x : WNode ι) : WNode ι :=
  if h : ∃ u ∈ D.nodes, D.canonicalName u = x then h.choose else x

theorem sourceNode_of_mem_normalize (D : HLS.WitnessDAG ι) (x : WNode ι)
    (hx : x ∈ D.normalize.nodes) :
    D.sourceNode x ∈ D.nodes ∧ D.canonicalName (D.sourceNode x) = x := by
  have h := (normalize_node_iff D x).mp hx
  simp only [sourceNode, dite_eq_left h]
  exact h.choose_spec

theorem sourceNode_name (G : SimpleGraph ι) (D : HLS.WitnessDAG ι)
    (hD : D.Valid G) (u : WNode ι) (hu : u ∈ D.nodes) :
    D.sourceNode (D.canonicalName u) = u := by
  have h : ∃ w ∈ D.nodes, D.canonicalName w = D.canonicalName u := ⟨u, hu, rfl⟩
  simp only [sourceNode, dite_eq_left h]
  exact canonicalName_injective G D hD h.choose_spec.1 hu h.choose_spec.2

theorem normalize_edge_backward (G : SimpleGraph ι) (D : HLS.WitnessDAG ι)
    (hD : D.Valid G) (x y : WNode ι) (he : D.normalize.Edge x y) :
    D.Edge (D.sourceNode x) (D.sourceNode y) := by
  obtain ⟨u, hu, v, hv, huv, hx, hy⟩ := (normalize_edge_witness G D hD x y).mp he
  rw [← hx, ← hy, sourceNode_name G D hD u hu, sourceNode_name G D hD v hv]
  exact huv

theorem normalize_edge_iff (G : SimpleGraph ι) (D : HLS.WitnessDAG ι)
    (hD : D.Valid G) (u v : WNode ι) (hu : u ∈ D.nodes) (hv : v ∈ D.nodes) :
    D.normalize.Edge (D.canonicalName u) (D.canonicalName v) ↔ D.Edge u v := by
  constructor
  · intro h
    have hback := normalize_edge_backward G D hD _ _ h
    simpa only [sourceNode_name G D hD u hu, sourceNode_name G D hD v hv] using hback
  · exact normalize_edge_forward D u v

theorem normalize_reach_forward (D : HLS.WitnessDAG ι) (u v : WNode ι)
    (h : D.Reach u v) : D.normalize.Reach (D.canonicalName u) (D.canonicalName v) :=
  Relation.ReflTransGen.lift D.canonicalName
    (fun a b hab => normalize_edge_forward D a b hab) _ _ h

theorem normalize_valid (G : SimpleGraph ι) (D : HLS.WitnessDAG ι) (hD : D.Valid G) :
    D.normalize.Valid G := by
  refine ⟨?_, ?_, ?_⟩
  · intro x y h
    obtain ⟨u, hu, v, hv, _, hx, hy⟩ := (normalize_edge_witness G D hD x y).mp h
    exact ⟨(normalize_node_iff D x).mpr ⟨u, hu, hx⟩,
      (normalize_node_iff D y).mpr ⟨v, hv, hy⟩⟩
  · intro x hx
    have hback := Relation.TransGen.lift D.sourceNode
      (fun a b h => normalize_edge_backward G D hD a b h) _ _ hx
    exact hD.acyclic _ hback
  · intro x hx y hy hxy
    obtain ⟨hxmem, hxname⟩ := sourceNode_of_mem_normalize D x hx
    obtain ⟨hymem, hyname⟩ := sourceNode_of_mem_normalize D y hy
    have hlabelx : (D.sourceNode x).1 = x.1 := by
      simpa only [canonicalName] using congrArg (fun z : WNode ι => z.1) hxname
    have hlabely : (D.sourceNode y).1 = y.1 := by
      simpa only [canonicalName] using congrArg (fun z : WNode ι => z.1) hyname
    have hsrc : D.sourceNode x ≠ D.sourceNode y := by
      intro heq
      exact hxy (hxname.symm.trans ((congrArg D.canonicalName heq).trans hyname))
    constructor
    · intro he
      have hdep : (D.sourceNode x).1 = (D.sourceNode y).1 ∨
          G.Adj (D.sourceNode x).1 (D.sourceNode y).1 :=
        (hD.oriented _ hxmem _ hymem hsrc).mp
          (he.imp (normalize_edge_backward G D hD x y) (normalize_edge_backward G D hD y x))
      simpa only [hlabelx, hlabely] using hdep
    · intro hdep
      have hdepsrc : (D.sourceNode x).1 = (D.sourceNode y).1 ∨
          G.Adj (D.sourceNode x).1 (D.sourceNode y).1 := by
        simpa only [hlabelx, hlabely] using hdep
      rcases (hD.oriented _ hxmem _ hymem hsrc).mpr hdepsrc with h | h
      · exact Or.inl (by simpa only [hxname, hyname] using normalize_edge_forward D _ _ h)
      · exact Or.inr (by simpa only [hxname, hyname] using normalize_edge_forward D _ _ h)

theorem normalize_canonical (G : SimpleGraph ι) (D : HLS.WitnessDAG ι)
    (hD : D.Valid G) : D.normalize.Canonical := by
  constructor
  · intro i n hn
    obtain ⟨u, hu, hname⟩ := (normalize_node_iff D (i, n + 1)).mp hn
    have hui : u.1 = i := congrArg Prod.fst hname
    have hurank : D.labelRank u = n + 1 := congrArg Prod.snd hname
    have hnlt : n < (D.labelNodes i).card := by
      have h := labelRank_lt_card G D hD u hu
      rw [hui, hurank] at h
      omega
    obtain ⟨v, hv, hvi, hvn⟩ := exists_node_of_labelRank_lt G D hD i n hnlt
    exact (normalize_node_iff D (i, n)).mpr ⟨v, hv, Prod.ext hvi hvn⟩
  · intro i m n hm hn hmn
    obtain ⟨u, hu, huname⟩ := (normalize_node_iff D (i, m)).mp hm
    obtain ⟨v, hv, hvname⟩ := (normalize_node_iff D (i, n)).mp hn
    have hulabel : u.1 = i := congrArg Prod.fst huname
    have hvlabel : v.1 = i := congrArg Prod.fst hvname
    have hum : D.labelRank u = m := congrArg Prod.snd huname
    have hvn : D.labelRank v = n := congrArg Prod.snd hvname
    have huv : u ≠ v := by
      intro heq
      have hrank := congrArg D.labelRank heq
      omega
    have hedge : D.Edge u v := by
      rcases (hD.oriented u hu v hv huv).mpr (Or.inl (hulabel.trans hvlabel.symm)) with h | h
      · exact h
      · have hlt := labelRank_lt_of_edge G D hD v u h (hvlabel.trans hulabel.symm)
        omega
    simpa only [huname, hvname] using normalize_edge_forward D u v hedge

theorem normalize_proper (D : HLS.WitnessDAG ι) (hproper : D.Proper) : D.normalize.Proper := by
  obtain ⟨r, hr, hroot⟩ := hproper
  refine ⟨D.canonicalName r, (normalize_node_iff D _).mpr ⟨r, hr, rfl⟩, ?_⟩
  intro x hx
  obtain ⟨u, hu, hname⟩ := (normalize_node_iff D x).mp hx
  simpa only [hname] using normalize_reach_forward D u r (hroot u hu)

theorem prod_normalize_nodes {M : Type*} [CommMonoid M]
    (G : SimpleGraph ι) (D : HLS.WitnessDAG ι) (hD : D.Valid G) (p : ι → M) :
    (∏ u ∈ D.normalize.nodes, p u.1) = ∏ u ∈ D.nodes, p u.1 := by
  rw [normalize, Finset.prod_image (canonicalName_injective G D hD)]
  rfl

end HLS.WitnessDAG

#check @HLS.WitnessDAG.normalize_node_iff
#check @HLS.WitnessDAG.normalize_edge_forward
#check @HLS.WitnessDAG.normalize_edge_witness
#check @HLS.WitnessDAG.sourceNode_of_mem_normalize
#check @HLS.WitnessDAG.sourceNode_name
#check @HLS.WitnessDAG.normalize_edge_backward
#check @HLS.WitnessDAG.normalize_edge_iff
#check @HLS.WitnessDAG.normalize_reach_forward
#check @HLS.WitnessDAG.normalize_valid
#check @HLS.WitnessDAG.normalize_canonical
#check @HLS.WitnessDAG.normalize_proper
#check @HLS.WitnessDAG.prod_normalize_nodes
