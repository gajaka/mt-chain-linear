/-
  Canonical witness DAGs are determined by their stable layer sequences.
  Occurrence indices are recovered by counting earlier occurrences of the
  same label in higher layers. Thus summing by layer sequences introduces
  no multiplicities from node names or topological enumerations.
-/
module

public import PPGraph.HLS.Encoding.StableEncoding

@[expose] public section

set_option autoImplicit false
set_option linter.unusedSectionVars false

open Classical

namespace HLS.WitnessDAG

variable {ι : Type*} [DecidableEq ι]

theorem canonical_node_mem_of_le (D : HLS.WitnessDAG ι) (hD : D.Canonical)
    (i : ι) (m n : ℕ) (hn : (i, n) ∈ D.nodes) (hmn : m ≤ n) :
    (i, m) ∈ D.nodes := by
  induction n generalizing m with
  | zero =>
    have hm : m = 0 := by omega
    simpa [hm] using hn
  | succ n ih =>
    by_cases hm : m = n + 1
    · simpa [hm] using hn
    · exact ih m (hD.1 i n hn) (by omega)

theorem same_label_height_iff_index (G : SimpleGraph ι) (D : HLS.WitnessDAG ι)
    (hD : D.Valid G) (hcanon : D.Canonical) (i : ι) (m n : ℕ)
    (hm : (i, m) ∈ D.nodes) (hn : (i, n) ∈ D.nodes) :
    height G D hD (i, n) < height G D hD (i, m) ↔ m < n := by
  constructor
  · intro hheight
    by_contra hmn
    by_cases heq : m = n
    · subst n
      omega
    · have hnm : n < m := by omega
      have hreverse := height_lt_of_edge G D hD _ _ (hcanon.2 i n m hn hm hnm)
      omega
  · intro hmn
    exact height_lt_of_edge G D hD _ _ (hcanon.2 i m n hm hn hmn)

noncomputable def earlierLabelNodes (D : HLS.WitnessDAG ι) (i : ι) (n : ℕ) :
    Finset (WNode ι) := D.nodes.filter (fun u => u.1 = i ∧ u.2 < n)

theorem earlierLabelNodes_eq_range_image (D : HLS.WitnessDAG ι) (hcanon : D.Canonical)
    (i : ι) (n : ℕ) (hn : (i, n) ∈ D.nodes) :
    earlierLabelNodes D i n = (Finset.range n).image (fun m => (i, m)) := by
  ext u
  constructor
  · intro hu
    obtain ⟨_, hui, hun⟩ := Finset.mem_filter.mp hu
    exact Finset.mem_image.mpr ⟨u.2, Finset.mem_range.mpr hun, Prod.ext hui.symm rfl⟩
  · intro hu
    obtain ⟨m, hm, rfl⟩ := Finset.mem_image.mp hu
    have hmn := Finset.mem_range.mp hm
    exact Finset.mem_filter.mpr
      ⟨canonical_node_mem_of_le D hcanon i m n hn hmn.le, rfl, hmn⟩

theorem earlierLabelNodes_card (D : HLS.WitnessDAG ι) (hcanon : D.Canonical)
    (i : ι) (n : ℕ) (hn : (i, n) ∈ D.nodes) : (earlierLabelNodes D i n).card = n := by
  rw [earlierLabelNodes_eq_range_image D hcanon i n hn,
    Finset.card_image_of_injective _ (fun _ _ h => congrArg Prod.snd h), Finset.card_range]

theorem earlierLabelNodes_height_image (G : SimpleGraph ι) (D : HLS.WitnessDAG ι)
    (hD : D.Valid G) (hcanon : D.Canonical) (i : ι) (n N : ℕ)
    (hn : (i, n) ∈ D.nodes) (hN : maxHeight G D hD < N) :
    (earlierLabelNodes D i n).image (height G D hD) =
      (Finset.range N).filter (fun k => height G D hD (i, n) < k ∧
        i ∈ layerLabels G D hD k) := by
  ext k
  constructor
  · intro hk
    obtain ⟨u, hu, rfl⟩ := Finset.mem_image.mp hk
    obtain ⟨hu, hui, hun⟩ := Finset.mem_filter.mp hu
    have hueq : u = (i, u.2) := Prod.ext hui rfl
    have hup : (i, u.2) ∈ D.nodes := hueq ▸ hu
    apply Finset.mem_filter.mpr
    refine ⟨Finset.mem_range.mpr ((height_le_maxHeight G D hD u hu).trans_lt hN), ?_, ?_⟩
    · rw [hueq]
      exact (same_label_height_iff_index G D hD hcanon i u.2 n hup hn).mpr hun
    · exact Finset.mem_image.mpr
        ⟨u, (mem_layerNodes G D hD u _).mpr ⟨hu, rfl⟩, hui⟩
  · intro hk
    obtain ⟨_, hheight, hilayer⟩ := Finset.mem_filter.mp hk
    obtain ⟨u, hu, hui⟩ := Finset.mem_image.mp hilayer
    obtain ⟨hu, huk⟩ := (mem_layerNodes G D hD u k).mp hu
    have hueq : u = (i, u.2) := Prod.ext hui rfl
    have hup : (i, u.2) ∈ D.nodes := hueq ▸ hu
    have huk' : height G D hD (i, u.2) = k := by
      rw [← hueq]
      exact huk
    have hindex : u.2 < n :=
      (same_label_height_iff_index G D hD hcanon i u.2 n hup hn).mp
        (by rw [huk']; exact hheight)
    exact Finset.mem_image.mpr ⟨u, Finset.mem_filter.mpr ⟨hu, hui, hindex⟩, huk⟩

theorem index_eq_card_higher_layers (G : SimpleGraph ι) (D : HLS.WitnessDAG ι)
    (hD : D.Valid G) (hcanon : D.Canonical) (i : ι) (n N : ℕ)
    (hn : (i, n) ∈ D.nodes) (hN : maxHeight G D hD < N) :
    n = ((Finset.range N).filter (fun k => height G D hD (i, n) < k ∧
      i ∈ layerLabels G D hD k)).card := by
  have hinj : Set.InjOn (height G D hD) (↑(earlierLabelNodes D i n) : Set (WNode ι)) := by
    intro u hu v hv hheight
    obtain ⟨hu, hui, _⟩ := Finset.mem_filter.mp hu
    obtain ⟨hv, hvi, _⟩ := Finset.mem_filter.mp hv
    apply layer_label_injective G D hD (height G D hD u)
      ((mem_layerNodes G D hD _ _).mpr ⟨hu, rfl⟩)
      ((mem_layerNodes G D hD _ _).mpr ⟨hv, hheight.symm⟩)
    exact hui.trans hvi.symm
  rw [← earlierLabelNodes_height_image G D hD hcanon i n N hn hN,
    Finset.card_image_of_injOn hinj, earlierLabelNodes_card D hcanon i n hn]

theorem transport_node_of_layerLabels_eq (G : SimpleGraph ι)
    (D E : HLS.WitnessDAG ι) (hD : D.Valid G) (hE : E.Valid G)
    (hcanonD : D.Canonical) (hcanonE : E.Canonical)
    (hlayers : ∀ k, layerLabels G D hD k = layerLabels G E hE k)
    (u : WNode ι) (hu : u ∈ D.nodes) :
    u ∈ E.nodes ∧ height G D hD u = height G E hE u := by
  have hulabel : u.1 ∈ layerLabels G E hE (height G D hD u) := by
    rw [← hlayers]
    exact Finset.mem_image.mpr ⟨u, (mem_layerNodes G D hD _ _).mpr ⟨hu, rfl⟩, rfl⟩
  obtain ⟨v, hv, hvlabel⟩ := Finset.mem_image.mp hulabel
  obtain ⟨hv, hvheight⟩ := (mem_layerNodes G E hE _ _).mp hv
  let N := maxHeight G D hD + maxHeight G E hE + 1
  have hND : maxHeight G D hD < N := by dsimp [N]; omega
  have hNE : maxHeight G E hE < N := by dsimp [N]; omega
  have huv : u.2 = v.2 := by
    have h₁ := index_eq_card_higher_layers G D hD hcanonD u.1 u.2 N hu hND
    have h₂ := index_eq_card_higher_layers G E hE hcanonE v.1 v.2 N hv hNE
    have heq : ((Finset.range N).filter (fun k => height G D hD u < k ∧
        u.1 ∈ layerLabels G D hD k)) =
        ((Finset.range N).filter (fun k => height G E hE v < k ∧
        v.1 ∈ layerLabels G E hE k)) := by
      ext k
      simp only [Finset.mem_filter, hvheight, hvlabel, hlayers]
    exact h₁.trans ((congrArg Finset.card heq).trans h₂.symm)
  have hvu : v = u := Prod.ext hvlabel huv.symm
  subst v
  exact ⟨hv, hvheight.symm⟩

/-- Canonical occurrence names make the layer encoding injective. -/
theorem eq_of_layerLabels_eq (G : SimpleGraph ι)
    (D E : HLS.WitnessDAG ι) (hD : D.Valid G) (hE : E.Valid G)
    (hcanonD : D.Canonical) (hcanonE : E.Canonical)
    (hlayers : ∀ k, layerLabels G D hD k = layerLabels G E hE k) : D = E := by
  have hDE := transport_node_of_layerLabels_eq G D E hD hE hcanonD hcanonE hlayers
  have hED := transport_node_of_layerLabels_eq G E D hE hD hcanonE hcanonD
    (fun k => (hlayers k).symm)
  have hnodes : D.nodes = E.nodes := by
    ext u
    exact ⟨fun hu => (hDE u hu).1, fun hu => (hED u hu).1⟩
  have harcs : D.arcs = E.arcs := by
    ext e
    obtain ⟨u, v⟩ := e
    change D.Edge u v ↔ E.Edge u v
    constructor
    · intro he
      obtain ⟨hu, hv⟩ := hD.supported u v he
      apply (edge_iff_height_dependent G E hE u v (hDE u hu).1 (hDE v hv).1).mpr
      rw [← (hDE u hu).2, ← (hDE v hv).2]
      exact (edge_iff_height_dependent G D hD u v hu hv).mp he
    · intro he
      obtain ⟨hu, hv⟩ := hE.supported u v he
      apply (edge_iff_height_dependent G D hD u v (hED u hu).1 (hED v hv).1).mpr
      rw [← (hED u hu).2, ← (hED v hv).2]
      exact (edge_iff_height_dependent G E hE u v hu hv).mp he
  cases D
  cases E
  cases hnodes
  cases harcs
  rfl

theorem eq_of_stableEncoding_eq (G : SimpleGraph ι)
    (D E : HLS.WitnessDAG ι) (hD : D.Valid G) (hE : E.Valid G)
    (hcanonD : D.Canonical) (hcanonE : E.Canonical)
    (h : stableEncoding G D hD = stableEncoding G E hE) : D = E :=
  eq_of_layerLabels_eq G D E hD hE hcanonD hcanonE
    (stableEncoding_eq_imp_layerLabels_eq G D E hD hE h)

end HLS.WitnessDAG

#check @HLS.WitnessDAG.canonical_node_mem_of_le
#check @HLS.WitnessDAG.same_label_height_iff_index
#check @HLS.WitnessDAG.earlierLabelNodes_eq_range_image
#check @HLS.WitnessDAG.earlierLabelNodes_card
#check @HLS.WitnessDAG.earlierLabelNodes_height_image
#check @HLS.WitnessDAG.index_eq_card_higher_layers
#check @HLS.WitnessDAG.transport_node_of_layerLabels_eq
#check @HLS.WitnessDAG.eq_of_layerLabels_eq
#check @HLS.WitnessDAG.eq_of_stableEncoding_eq
