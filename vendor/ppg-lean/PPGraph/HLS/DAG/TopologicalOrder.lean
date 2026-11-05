/- A fixed total topological order for each finite witness DAG. -/
module

public import PPGraph.HLS.DAG.WitnessLayers

@[expose] public section

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option backward.isDefEq.respectTransparency false

open Classical

namespace HLS.WitnessDAG

variable {ι : Type} [Fintype ι] [DecidableEq ι]

noncomputable def labelNumber (i : ι) : ℕ := (Fintype.equivFin ι i).val

theorem labelNumber_injective : Function.Injective (labelNumber (ι := ι)) := by
  intro i j h
  exact (Fintype.equivFin ι).injective (Fin.ext h)

noncomputable def topoBefore (G : SimpleGraph ι) (D : HLS.WitnessDAG ι) (hD : D.Valid G)
    (u v : WNode ι) : Prop :=
  height G D hD v < height G D hD u ∨
    (height G D hD v = height G D hD u ∧ labelNumber u.1 < labelNumber v.1)

theorem topoBefore_irrefl (G : SimpleGraph ι) (D : HLS.WitnessDAG ι) (hD : D.Valid G)
    (u : WNode ι) : ¬ topoBefore G D hD u u := by
  unfold topoBefore
  omega

theorem topoBefore_trans (G : SimpleGraph ι) (D : HLS.WitnessDAG ι) (hD : D.Valid G)
    (u v w : WNode ι) (huv : topoBefore G D hD u v) (hvw : topoBefore G D hD v w) :
    topoBefore G D hD u w := by
  unfold topoBefore at *
  omega

theorem topoBefore_asymm (G : SimpleGraph ι) (D : HLS.WitnessDAG ι) (hD : D.Valid G)
    (u v : WNode ι) (h : topoBefore G D hD u v) : ¬ topoBefore G D hD v u := by
  intro hback
  exact topoBefore_irrefl G D hD u (topoBefore_trans G D hD u v u h hback)

theorem topoBefore_total (G : SimpleGraph ι) (D : HLS.WitnessDAG ι) (hD : D.Valid G)
    (u v : WNode ι) (hu : u ∈ D.nodes) (hv : v ∈ D.nodes) (hne : u ≠ v) :
    topoBefore G D hD u v ∨ topoBefore G D hD v u := by
  by_cases he : height G D hD u = height G D hD v
  · have hlabel : u.1 ≠ v.1 := by
      intro h
      have huLayer : u ∈ layerNodes G D hD (height G D hD u) :=
        (mem_layerNodes G D hD u _).mpr ⟨hu, rfl⟩
      have hvLayer : v ∈ layerNodes G D hD (height G D hD u) :=
        (mem_layerNodes G D hD v _).mpr ⟨hv, he.symm⟩
      exact hne (layer_label_injective G D hD _ huLayer hvLayer h)
    have hnum : labelNumber u.1 ≠ labelNumber v.1 := fun h =>
      hlabel (labelNumber_injective h)
    unfold topoBefore
    omega
  · unfold topoBefore
    omega

theorem topoBefore_of_edge (G : SimpleGraph ι) (D : HLS.WitnessDAG ι) (hD : D.Valid G)
    (u v : WNode ι) (he : D.Edge u v) : topoBefore G D hD u v :=
  Or.inl (height_lt_of_edge G D hD u v he)

theorem edge_of_topoBefore_dependent (G : SimpleGraph ι) (D : HLS.WitnessDAG ι) (hD : D.Valid G)
    (u v : WNode ι) (hu : u ∈ D.nodes) (hv : v ∈ D.nodes)
    (h : topoBefore G D hD u v) (hdep : u.1 = v.1 ∨ G.Adj u.1 v.1) : D.Edge u v := by
  have hne : u ≠ v := by intro heq; exact topoBefore_irrefl G D hD u (heq.symm ▸ h)
  rcases (hD.oriented u hu v hv hne).mpr hdep with he | he
  · exact he
  · exact False.elim (topoBefore_asymm G D hD u v h (topoBefore_of_edge G D hD v u he))

end HLS.WitnessDAG

#check @HLS.WitnessDAG.labelNumber_injective
#check @HLS.WitnessDAG.topoBefore_irrefl
#check @HLS.WitnessDAG.topoBefore_trans
#check @HLS.WitnessDAG.topoBefore_asymm
#check @HLS.WitnessDAG.topoBefore_total
#check @HLS.WitnessDAG.topoBefore_of_edge
#check @HLS.WitnessDAG.edge_of_topoBefore_dependent
