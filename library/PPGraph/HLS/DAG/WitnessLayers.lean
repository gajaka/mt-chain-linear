/-
  Longest-path layers of finite witness DAGs. Equal-height nodes have
  independent labels, and every positive-height node has a dependent
  successor in the immediately preceding layer. This connects witness
  DAGs with the stable-set sequences used by Kolipaka--Szegedy.
  Sources: He--Li--Sun, arXiv:2111.06527, Section 1.2.1 (footnote 4);
  Harvey--Vondrak, arXiv:1504.02044, Section 5.3.
-/
module

public import PPGraph.HLS.DAG.WitnessDAG
public import PPGraph.Shearer.Stable

@[expose] public section

set_option autoImplicit false
set_option linter.unusedSectionVars false

open Classical

namespace HLS.WitnessDAG

variable {ι : Type*} [DecidableEq ι]

noncomputable def descendants (D : HLS.WitnessDAG ι) (u : WNode ι) : Finset (WNode ι) :=
  D.nodes.filter (D.Reach u)

theorem descendants_strict (G : SimpleGraph ι) (D : HLS.WitnessDAG ι)
    (hD : D.Valid G) (u v : WNode ι) (hedge : D.Edge u v) :
    D.descendants v ⊂ D.descendants u := by
  have hsub : D.descendants v ⊆ D.descendants u := by
    intro w hw
    obtain ⟨hw, hvw⟩ := Finset.mem_filter.mp hw
    exact Finset.mem_filter.mpr ⟨hw, hvw.head hedge⟩
  apply lt_of_le_of_ne hsub
  intro heq
  have hu : u ∈ D.descendants u :=
    Finset.mem_filter.mpr ⟨(hD.supported u v hedge).1, .refl⟩
  have hvu := (Finset.mem_filter.mp (heq.symm ▸ hu)).2
  exact hD.acyclic u ((Relation.TransGen.single hedge).trans_left hvu)

theorem outgoing_wellFounded (G : SimpleGraph ι) (D : HLS.WitnessDAG ι)
    (hD : D.Valid G) : WellFounded (fun v u => D.Edge u v) := by
  apply Subrelation.wf (r := (measure (fun u => (D.descendants u).card)).rel)
    _ (measure (fun u => (D.descendants u).card)).wf
  intro v u huv
  exact Finset.card_lt_card (descendants_strict G D hD u v huv)

noncomputable def children (D : HLS.WitnessDAG ι) (u : WNode ι) : Finset (WNode ι) :=
  D.nodes.filter (D.Edge u)

@[simp]
theorem mem_children (D : HLS.WitnessDAG ι) (u v : WNode ι) :
    v ∈ D.children u ↔ v ∈ D.nodes ∧ D.Edge u v := by simp [children]

noncomputable def height (G : SimpleGraph ι) (D : HLS.WitnessDAG ι)
    (hD : D.Valid G) : WNode ι → ℕ :=
  (outgoing_wellFounded G D hD).fix (fun u rec =>
    (D.children u).attach.sup (fun v =>
      rec v.1 ((mem_children D u v.1).mp v.2).2 + 1))

theorem height_eq_sup (G : SimpleGraph ι) (D : HLS.WitnessDAG ι)
    (hD : D.Valid G) (u : WNode ι) :
    height G D hD u = (D.children u).sup (fun v => height G D hD v + 1) := by
  conv_lhs => rw [height, WellFounded.fix_eq]
  exact Finset.sup_attach (D.children u) (fun v => height G D hD v + 1)

theorem height_lt_of_edge (G : SimpleGraph ι) (D : HLS.WitnessDAG ι)
    (hD : D.Valid G) (u v : WNode ι) (h : D.Edge u v) :
    height G D hD v < height G D hD u := by
  have hv : v ∈ D.children u :=
    (mem_children D u v).mpr ⟨(hD.supported u v h).2, h⟩
  have hle := Finset.le_sup (f := fun w => height G D hD w + 1) hv
  rw [← height_eq_sup G D hD u] at hle
  omega

theorem height_lt_of_transGen (G : SimpleGraph ι) (D : HLS.WitnessDAG ι)
    (hD : D.Valid G) (u v : WNode ι) (h : Relation.TransGen D.Edge u v) :
    height G D hD v < height G D hD u := by
  induction h with
  | single h => exact height_lt_of_edge G D hD _ _ h
  | tail _ h ih => exact (height_lt_of_edge G D hD _ _ h).trans ih

theorem height_zero_iff_no_edge (G : SimpleGraph ι) (D : HLS.WitnessDAG ι)
    (hD : D.Valid G) (u : WNode ι) :
    height G D hD u = 0 ↔ ∀ v, ¬ D.Edge u v := by
  constructor
  · intro hu v huv
    have h := height_lt_of_edge G D hD u v huv
    omega
  · intro hu
    have hempty : D.children u = ∅ := by
      apply Finset.eq_empty_iff_forall_notMem.mpr
      intro v hv
      exact hu v ((mem_children D u v).mp hv).2
    rw [height_eq_sup G D hD u, hempty]
    rfl

theorem height_succ_has_child (G : SimpleGraph ι) (D : HLS.WitnessDAG ι)
    (hD : D.Valid G) (u : WNode ι) (k : ℕ) (hu : height G D hD u = k + 1) :
    ∃ v ∈ D.nodes, D.Edge u v ∧ height G D hD v = k := by
  have hne : (D.children u).Nonempty := by
    by_contra hn
    have he : D.children u = ∅ := Finset.not_nonempty_iff_eq_empty.mp hn
    rw [height_eq_sup G D hD u, he] at hu
    simp at hu
  obtain ⟨v, hv, hmax⟩ := Finset.exists_mem_eq_sup (D.children u) hne
    (fun v => height G D hD v + 1)
  obtain ⟨hv, huv⟩ := (mem_children D u v).mp hv
  refine ⟨v, hv, huv, ?_⟩
  rw [← height_eq_sup G D hD u, hu] at hmax
  omega

noncomputable def layerNodes (G : SimpleGraph ι) (D : HLS.WitnessDAG ι)
    (hD : D.Valid G) (k : ℕ) : Finset (WNode ι) :=
  D.nodes.filter (fun u => height G D hD u = k)

noncomputable def layerLabels (G : SimpleGraph ι) (D : HLS.WitnessDAG ι)
    (hD : D.Valid G) (k : ℕ) : Finset ι := (layerNodes G D hD k).image Prod.fst

@[simp]
theorem mem_layerNodes (G : SimpleGraph ι) (D : HLS.WitnessDAG ι)
    (hD : D.Valid G) (u : WNode ι) (k : ℕ) :
    u ∈ layerNodes G D hD k ↔ u ∈ D.nodes ∧ height G D hD u = k := by
  simp [layerNodes]

theorem layer_label_injective (G : SimpleGraph ι) (D : HLS.WitnessDAG ι)
    (hD : D.Valid G) (k : ℕ) :
    Set.InjOn Prod.fst (↑(layerNodes G D hD k) : Set (WNode ι)) := by
  intro u hu v hv hlabel
  obtain ⟨hu, huk⟩ := (mem_layerNodes G D hD u k).mp hu
  obtain ⟨hv, hvk⟩ := (mem_layerNodes G D hD v k).mp hv
  by_contra huv
  have he := (hD.oriented u hu v hv huv).mpr (Or.inl hlabel)
  rcases he with he | he
  · have h := height_lt_of_edge G D hD u v he
    omega
  · have h := height_lt_of_edge G D hD v u he
    omega

theorem layer_independent (G : SimpleGraph ι) (D : HLS.WitnessDAG ι)
    (hD : D.Valid G) (k : ℕ) : Shearer.Independent G (layerLabels G D hD k) := by
  intro a ha b hb hab
  obtain ⟨u, hu, rfl⟩ := Finset.mem_image.mp ha
  obtain ⟨v, hv, rfl⟩ := Finset.mem_image.mp hb
  obtain ⟨hu, huk⟩ := (mem_layerNodes G D hD u k).mp hu
  obtain ⟨hv, hvk⟩ := (mem_layerNodes G D hD v k).mp hv
  have huv : u ≠ v := by rintro rfl; exact G.irrefl hab
  rcases (hD.oriented u hu v hv huv).mpr (Or.inr hab) with he | he
  · have h := height_lt_of_edge G D hD u v he
    omega
  · have h := height_lt_of_edge G D hD v u he
    omega

theorem layer_successor (G : SimpleGraph ι) (D : HLS.WitnessDAG ι)
    (hD : D.Valid G) (B : Finset ι) (hB : ∀ u ∈ D.nodes, u.1 ∈ B) (k : ℕ) :
    layerLabels G D hD (k + 1) ∈ Shearer.successors G B (layerLabels G D hD k) := by
  apply (Shearer.mem_successors G B _ _).mpr
  refine ⟨?_, layer_independent G D hD (k + 1)⟩
  intro a ha
  obtain ⟨u, hu, rfl⟩ := Finset.mem_image.mp ha
  obtain ⟨hu, huk⟩ := (mem_layerNodes G D hD u (k + 1)).mp hu
  obtain ⟨v, hv, huv, hvk⟩ := height_succ_has_child G D hD u k huk
  apply Finset.mem_filter.mpr
  refine ⟨hB u hu, ?_⟩
  have hvlabel : v.1 ∈ layerLabels G D hD k := Finset.mem_image.mpr
    ⟨v, (mem_layerNodes G D hD v k).mpr ⟨hv, hvk⟩, rfl⟩
  rcases edge_dependent G D hD u v huv with h | h
  · exact Or.inl (h ▸ hvlabel)
  · exact Or.inr ⟨v.1, hvlabel, h.symm⟩

theorem edge_iff_height_dependent (G : SimpleGraph ι) (D : HLS.WitnessDAG ι)
    (hD : D.Valid G) (u v : WNode ι) (hu : u ∈ D.nodes) (hv : v ∈ D.nodes) :
    D.Edge u v ↔ height G D hD v < height G D hD u ∧
      (u.1 = v.1 ∨ G.Adj u.1 v.1) := by
  constructor
  · intro huv
    exact ⟨height_lt_of_edge G D hD u v huv, edge_dependent G D hD u v huv⟩
  · rintro ⟨hheight, hdep⟩
    have huv : u ≠ v := by rintro rfl; omega
    rcases (hD.oriented u hu v hv huv).mpr hdep with h | h
    · exact h
    · have hreverse := height_lt_of_edge G D hD v u h
      omega

theorem root_layer_zero (G : SimpleGraph ι) (D : HLS.WitnessDAG ι)
    (hD : D.Valid G) (r : WNode ι) (hr : r ∈ D.nodes)
    (hroot : ∀ u ∈ D.nodes, D.Reach u r) : layerLabels G D hD 0 = {r.1} := by
  have hrsink := proper_root_sink G D hD r hr hroot
  have hrheight := (height_zero_iff_no_edge G D hD r).mpr hrsink.2
  ext i
  constructor
  · intro hi
    obtain ⟨u, hu, rfl⟩ := Finset.mem_image.mp hi
    obtain ⟨hu, huheight⟩ := (mem_layerNodes G D hD u 0).mp hu
    have hueq := sink_eq_root D r u hroot
      ⟨hu, (height_zero_iff_no_edge G D hD u).mp huheight⟩
    simp [hueq]
  · intro hi
    have hir : i = r.1 := Finset.mem_singleton.mp hi
    exact Finset.mem_image.mpr ⟨r,
      (mem_layerNodes G D hD r 0).mpr ⟨hr, hrheight⟩, hir.symm⟩

end HLS.WitnessDAG

#check @HLS.WitnessDAG.descendants_strict
#check @HLS.WitnessDAG.outgoing_wellFounded
#check @HLS.WitnessDAG.mem_children
#check @HLS.WitnessDAG.height_eq_sup
#check @HLS.WitnessDAG.height_lt_of_edge
#check @HLS.WitnessDAG.height_lt_of_transGen
#check @HLS.WitnessDAG.height_zero_iff_no_edge
#check @HLS.WitnessDAG.height_succ_has_child
#check @HLS.WitnessDAG.mem_layerNodes
#check @HLS.WitnessDAG.layer_label_injective
#check @HLS.WitnessDAG.layer_independent
#check @HLS.WitnessDAG.layer_successor
#check @HLS.WitnessDAG.edge_iff_height_dependent
#check @HLS.WitnessDAG.root_layer_zero
