/-
  A proper witness DAG has a proper stable-set layer sequence. This file
  constructs that sequence from its longest-path heights, without choosing
  a topological enumeration. The canonical-index injectivity bridge is
  proved separately.
-/
module

public import PPGraph.HLS.DAG.WitnessLayers

@[expose] public section

set_option autoImplicit false
set_option linter.unusedSectionVars false

open Classical

namespace HLS.WitnessDAG

variable {ι : Type*} [DecidableEq ι]

noncomputable def layerSequence (G : SimpleGraph ι) (D : HLS.WitnessDAG ι)
    (hD : D.Valid G) : ℕ → ℕ → List (Finset ι)
  | start, 0 => [layerLabels G D hD start]
  | start, d + 1 => layerLabels G D hD start :: layerSequence G D hD (start + 1) d

theorem layerSequence_stable (G : SimpleGraph ι) (D : HLS.WitnessDAG ι)
    (hD : D.Valid G) (B : Finset ι) (hB : ∀ u ∈ D.nodes, u.1 ∈ B)
    (d start : ℕ) :
    layerSequence G D hD start d ∈
      Shearer.stableSequences G B d (layerLabels G D hD start) := by
  induction d generalizing start with
  | zero => simp [layerSequence, Shearer.stableSequences]
  | succ d ih =>
    apply Finset.mem_biUnion.mpr
    refine ⟨layerLabels G D hD (start + 1), layer_successor G D hD B hB start, ?_⟩
    exact Finset.mem_image.mpr ⟨layerSequence G D hD (start + 1) d,
      ih (start + 1), rfl⟩

theorem layerSequence_mem_index (G : SimpleGraph ι) (D : HLS.WitnessDAG ι)
    (hD : D.Valid G) (start d : ℕ) (J : Finset ι)
    (hJ : J ∈ layerSequence G D hD start d) :
    ∃ k, start ≤ k ∧ k ≤ start + d ∧ J = layerLabels G D hD k := by
  induction d generalizing start with
  | zero =>
    have heq : J = layerLabels G D hD start := by simpa [layerSequence] using hJ
    exact ⟨start, le_rfl, by omega, heq⟩
  | succ d ih =>
    rcases List.mem_cons.mp hJ with h | h
    · exact ⟨start, le_rfl, by omega, h⟩
    · obtain ⟨k, hk₁, hk₂, hJ⟩ := ih (start + 1) h
      exact ⟨k, by omega, by omega, hJ⟩

noncomputable def maxHeight (G : SimpleGraph ι) (D : HLS.WitnessDAG ι)
    (hD : D.Valid G) : ℕ := D.nodes.sup (height G D hD)

theorem height_le_maxHeight (G : SimpleGraph ι) (D : HLS.WitnessDAG ι)
    (hD : D.Valid G) (u : WNode ι) (hu : u ∈ D.nodes) :
    height G D hD u ≤ maxHeight G D hD := Finset.le_sup hu

theorem exists_node_at_lower_height (G : SimpleGraph ι) (D : HLS.WitnessDAG ι)
    (hD : D.Valid G) (u : WNode ι) (hu : u ∈ D.nodes) (k : ℕ)
    (hk : k ≤ height G D hD u) : ∃ v ∈ D.nodes, height G D hD v = k := by
  induction u using (outgoing_wellFounded G D hD).induction generalizing k with
  | h u ih =>
    by_cases heq : height G D hD u = k
    · exact ⟨u, hu, heq⟩
    have hpos : 0 < height G D hD u := by omega
    obtain ⟨n, hn⟩ := Nat.exists_eq_succ_of_ne_zero hpos.ne'
    obtain ⟨v, hv, huv, hvn⟩ := height_succ_has_child G D hD u n hn
    exact ih v huv hv k (by omega)

theorem layerLabels_nonempty (G : SimpleGraph ι) (D : HLS.WitnessDAG ι)
    (hD : D.Valid G) (hne : D.nodes.Nonempty) (k : ℕ)
    (hk : k ≤ maxHeight G D hD) : (layerLabels G D hD k).Nonempty := by
  obtain ⟨u, hu, hmax⟩ := Finset.exists_mem_eq_sup D.nodes hne (height G D hD)
  obtain ⟨v, hv, hvk⟩ := exists_node_at_lower_height G D hD u hu k
    (by simpa only [maxHeight, hmax] using hk)
  exact ⟨v.1, Finset.mem_image.mpr
    ⟨v, (mem_layerNodes G D hD v k).mpr ⟨hv, hvk⟩, rfl⟩⟩

noncomputable def stableEncoding (G : SimpleGraph ι) (D : HLS.WitnessDAG ι)
    (hD : D.Valid G) : List (Finset ι) :=
  layerSequence G D hD 0 (maxHeight G D hD)

theorem stableEncoding_mem_properFamily (G : SimpleGraph ι) (D : HLS.WitnessDAG ι)
    (hD : D.Valid G) (B : Finset ι) (hB : ∀ u ∈ D.nodes, u.1 ∈ B)
    (r : WNode ι) (hr : r ∈ D.nodes) (hroot : ∀ u ∈ D.nodes, D.Reach u r) :
    stableEncoding G D hD ∈ Shearer.properFamily G B {r.1} := by
  constructor
  · refine ⟨maxHeight G D hD, ?_⟩
    rw [← root_layer_zero G D hD r hr hroot]
    exact layerSequence_stable G D hD B hB _ 0
  · intro J hJ
    obtain ⟨k, _, hk, rfl⟩ := layerSequence_mem_index G D hD 0 (maxHeight G D hD) J hJ
    exact (layerLabels_nonempty G D hD ⟨r, hr⟩ k (by simpa using hk)).ne_empty

theorem layerSequence_eq_range_map (G : SimpleGraph ι) (D : HLS.WitnessDAG ι)
    (hD : D.Valid G) (start d : ℕ) :
    layerSequence G D hD start d =
      (List.range (d + 1)).map (fun k => layerLabels G D hD (start + k)) := by
  induction d generalizing start with
  | zero => simp [layerSequence]
  | succ d ih =>
    rw [layerSequence, List.range_succ_eq_map]
    simp only [List.map_cons, List.map_map, Function.comp_def, Nat.add_zero]
    congr 1
    rw [ih]
    congr 1
    funext k
    congr 1
    omega

theorem layerSequence_getD (G : SimpleGraph ι) (D : HLS.WitnessDAG ι)
    (hD : D.Valid G) (start d k : ℕ) :
    (layerSequence G D hD start d).getD k ∅ =
      if k ≤ d then layerLabels G D hD (start + k) else ∅ := by
  induction d generalizing start k with
  | zero => cases k <;> simp [layerSequence]
  | succ d ih =>
    cases k with
    | zero => simp [layerSequence]
    | succ k =>
      simp only [layerSequence, List.getD_cons_succ, ih, Nat.succ_le_succ_iff]
      congr 1
      congr 1
      omega

theorem layerLabels_eq_empty_of_maxHeight_lt (G : SimpleGraph ι) (D : HLS.WitnessDAG ι)
    (hD : D.Valid G) (k : ℕ) (hk : maxHeight G D hD < k) :
    layerLabels G D hD k = ∅ := by
  apply Finset.eq_empty_iff_forall_notMem.mpr
  intro i hi
  obtain ⟨u, hu, _⟩ := Finset.mem_image.mp hi
  obtain ⟨hu, huk⟩ := (mem_layerNodes G D hD u k).mp hu
  have h := height_le_maxHeight G D hD u hu
  omega

theorem stableEncoding_getD (G : SimpleGraph ι) (D : HLS.WitnessDAG ι)
    (hD : D.Valid G) (k : ℕ) :
    (stableEncoding G D hD).getD k ∅ = layerLabels G D hD k := by
  rw [stableEncoding, layerSequence_getD, Nat.zero_add]
  split_ifs with hk
  · rfl
  · exact (layerLabels_eq_empty_of_maxHeight_lt G D hD k (by omega)).symm

theorem stableEncoding_eq_imp_layerLabels_eq (G : SimpleGraph ι)
    (D E : HLS.WitnessDAG ι) (hD : D.Valid G) (hE : E.Valid G)
    (h : stableEncoding G D hD = stableEncoding G E hE) (k : ℕ) :
    layerLabels G D hD k = layerLabels G E hE k := by
  rw [← stableEncoding_getD G D hD k, ← stableEncoding_getD G E hE k, h]

theorem prod_nodes_eq_prod_layers {M : Type*} [CommMonoid M]
    (G : SimpleGraph ι) (D : HLS.WitnessDAG ι) (hD : D.Valid G) (f : ℕ → ι → M) :
    (∏ u ∈ D.nodes, f (height G D hD u) u.1) =
      ∏ d ∈ Finset.range (maxHeight G D hD + 1), ∏ i ∈ layerLabels G D hD d, f d i := by
  have hb : ∀ u ∈ D.nodes, height G D hD u ∈ Finset.range (maxHeight G D hD + 1) := by
    intro u hu
    exact Finset.mem_range.mpr (Nat.lt_succ_of_le (height_le_maxHeight G D hD u hu))
  rw [← Finset.prod_fiberwise_of_maps_to hb (fun u => f (height G D hD u) u.1)]
  apply Finset.prod_congr rfl
  intro d _
  rw [layerLabels, Finset.prod_image (layer_label_injective G D hD d)]
  apply Finset.prod_congr rfl
  intro u hu
  rw [(Finset.mem_filter.mp hu).2]

theorem prod_map_stableEncoding {M : Type*} [CommMonoid M]
    (G : SimpleGraph ι) (D : HLS.WitnessDAG ι) (hD : D.Valid G) (f : Finset ι → M) :
    ((stableEncoding G D hD).map f).prod =
      ∏ d ∈ Finset.range (maxHeight G D hD + 1), f (layerLabels G D hD d) := by
  simp only [stableEncoding, layerSequence_eq_range_map, List.map_map,
    Function.comp_def, Nat.zero_add]
  have h (n : ℕ) : ((List.range n).map (fun d => f (layerLabels G D hD d))).prod =
      ∏ d ∈ Finset.range n, f (layerLabels G D hD d) := by
    induction n with
    | zero => simp
    | succ n ih => rw [List.prod_range_succ, Finset.prod_range_succ, ih]
  exact h _

theorem sequenceWeight_stableEncoding (G : SimpleGraph ι) (D : HLS.WitnessDAG ι)
    (hD : D.Valid G) (p : ι → ℝ) :
    Shearer.sequenceWeight p (stableEncoding G D hD) = ∏ u ∈ D.nodes, p u.1 := by
  rw [Shearer.sequenceWeight, prod_map_stableEncoding]
  exact (prod_nodes_eq_prod_layers G D hD (fun _ i => p i)).symm

end HLS.WitnessDAG

#check @HLS.WitnessDAG.layerSequence_stable
#check @HLS.WitnessDAG.layerSequence_mem_index
#check @HLS.WitnessDAG.height_le_maxHeight
#check @HLS.WitnessDAG.exists_node_at_lower_height
#check @HLS.WitnessDAG.layerLabels_nonempty
#check @HLS.WitnessDAG.stableEncoding_mem_properFamily
#check @HLS.WitnessDAG.layerSequence_eq_range_map
#check @HLS.WitnessDAG.layerSequence_getD
#check @HLS.WitnessDAG.layerLabels_eq_empty_of_maxHeight_lt
#check @HLS.WitnessDAG.stableEncoding_getD
#check @HLS.WitnessDAG.stableEncoding_eq_imp_layerLabels_eq
#check @HLS.WitnessDAG.prod_nodes_eq_prod_layers
#check @HLS.WitnessDAG.prod_map_stableEncoding
#check @HLS.WitnessDAG.sequenceWeight_stableEncoding
