/- Canonical renaming preserves reversibility and alternate paths. -/
module

public import PPGraph.HLS.Encoding.Normalization

@[expose] public section

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option backward.isDefEq.respectTransparency false

open Classical

namespace HLS.WitnessDAG

variable {ι : Type} [DecidableEq ι]

theorem normalize_eraseArc_forward (G : SimpleGraph ι) (D : HLS.WitnessDAG ι)
    (hD : D.Valid G) (u v : WNode ι) (hu : u ∈ D.nodes) (hv : v ∈ D.nodes)
    (x y : WNode ι) (he : eraseArc D.Edge u v x y) :
    eraseArc D.normalize.Edge (D.canonicalName u) (D.canonicalName v)
      (D.canonicalName x) (D.canonicalName y) := by
  refine ⟨normalize_edge_forward D x y he.1, ?_⟩
  rintro ⟨hxu, hyv⟩
  exact he.2 ⟨canonicalName_injective G D hD (hD.supported _ _ he.1).1 hu hxu,
    canonicalName_injective G D hD (hD.supported _ _ he.1).2 hv hyv⟩

theorem normalize_eraseArc_backward (G : SimpleGraph ι) (D : HLS.WitnessDAG ι)
    (hD : D.Valid G) (u v x y : WNode ι)
    (he : eraseArc D.normalize.Edge (D.canonicalName u) (D.canonicalName v) x y) :
    eraseArc D.Edge u v (D.sourceNode x) (D.sourceNode y) := by
  refine ⟨normalize_edge_backward G D hD x y he.1, ?_⟩
  rintro ⟨hxu, hyv⟩
  have hSupported := (normalize_valid G D hD).supported x y he.1
  have hx := (sourceNode_of_mem_normalize D x hSupported.1).2
  have hy := (sourceNode_of_mem_normalize D y hSupported.2).2
  exact he.2 ⟨hx.symm.trans (congrArg D.canonicalName hxu),
    hy.symm.trans (congrArg D.canonicalName hyv)⟩

theorem normalize_reversible_iff (G : SimpleGraph ι) (D : HLS.WitnessDAG ι)
    (hD : D.Valid G) (u v : WNode ι) (he : D.Edge u v) :
    Acyclic (reverseArc D.normalize.Edge (D.canonicalName u) (D.canonicalName v)) ↔
      Acyclic (reverseArc D.Edge u v) := by
  have hu := (hD.supported u v he).1
  have hv := (hD.supported u v he).2
  have he' := normalize_edge_forward D u v he
  rw [reversible_iff_no_alternate_path _ _ _ (normalize_valid G D hD).acyclic he',
    reversible_iff_no_alternate_path _ _ _ hD.acyclic he]
  constructor
  · intro hn hpath
    exact hn (Relation.TransGen.lift D.canonicalName
      (fun x y h => normalize_eraseArc_forward G D hD u v hu hv x y h) _ _ hpath)
  · intro hn hpath
    have hback := Relation.TransGen.lift D.sourceNode
      (fun x y h => normalize_eraseArc_backward G D hD u v x y h) _ _ hpath
    change Relation.TransGen (eraseArc D.Edge u v)
      (D.sourceNode (D.canonicalName u)) (D.sourceNode (D.canonicalName v)) at hback
    rw [sourceNode_name G D hD u hu, sourceNode_name G D hD v hv] at hback
    exact hn hback

end HLS.WitnessDAG

#check @HLS.WitnessDAG.normalize_eraseArc_forward
#check @HLS.WitnessDAG.normalize_eraseArc_backward
#check @HLS.WitnessDAG.normalize_reversible_iff
