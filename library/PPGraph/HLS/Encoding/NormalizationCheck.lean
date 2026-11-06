/- Canonical renaming preserves the resampling-table check, not only weights. -/
module

public import PPGraph.HLS.Encoding.Normalization
public import PPGraph.HLS.Encoding.TableCheck

@[expose] public section

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option backward.isDefEq.respectTransparency false

open Classical

namespace HLS.WitnessDAG

variable {V : Type} [DecidableEq V] {S : VarSpaces V}
    {ι : Type} [DecidableEq ι]

theorem priorReaders_normalize (P : MTProcess S ι) (D : HLS.WitnessDAG ι)
    (hD : D.Valid (Shearer.dependencyGraph P.footprint)) (u : WNode ι)
    (hu : u ∈ D.nodes) (a : V) :
    priorReaders P D.normalize (D.canonicalName u) a =
      (priorReaders P D u a).image D.canonicalName := by
  ext x
  constructor
  · intro hx
    obtain ⟨hxmem, hxu, hxa⟩ := Finset.mem_filter.mp hx
    obtain ⟨w, hw, hwx⟩ := (normalize_node_iff D x).mp hxmem
    have hwu : D.Edge w u :=
      (normalize_edge_iff _ D hD w u hw hu).mp (hwx.symm ▸ hxu)
    have hwa : a ∈ P.footprint w.1 := by
      simpa only [← hwx, canonicalName] using hxa
    exact Finset.mem_image.mpr ⟨w, Finset.mem_filter.mpr ⟨hw, hwu, hwa⟩, hwx⟩
  · intro hx
    obtain ⟨w, hw, hwx⟩ := Finset.mem_image.mp hx
    obtain ⟨hwmem, hwu, hwa⟩ := Finset.mem_filter.mp hw
    subst x
    exact Finset.mem_filter.mpr ⟨
      (normalize_node_iff D _).mpr ⟨w, hwmem, rfl⟩,
      normalize_edge_forward D w u hwu, hwa⟩

theorem localIndex_normalize (P : MTProcess S ι) (D : HLS.WitnessDAG ι)
    (hD : D.Valid (Shearer.dependencyGraph P.footprint)) (u : WNode ι)
    (hu : u ∈ D.nodes) (a : V) :
    localIndex P D.normalize (D.canonicalName u) a = localIndex P D u a := by
  unfold localIndex
  rw [priorReaders_normalize P D hD u hu a]
  exact Finset.card_image_of_injOn (fun x hx y hy hxy =>
    canonicalName_injective _ D hD (Finset.mem_filter.mp hx).1
      (Finset.mem_filter.mp hy).1 hxy)

theorem tableState_normalize (P : MTProcess S ι) (D : HLS.WitnessDAG ι)
    (hD : D.Valid (Shearer.dependencyGraph P.footprint)) (u : WNode ι)
    (hu : u ∈ D.nodes) (ω : LogSpace S) :
    tableState P D.normalize ω (D.canonicalName u) = tableState P D ω u := by
  funext a
  change ω (localIndex P D.normalize (D.canonicalName u) a, a) =
    ω (localIndex P D u a, a)
  rw [localIndex_normalize P D hD u hu a]

theorem tableEvent_normalize (P : MTProcess S ι) (D : HLS.WitnessDAG ι)
    (hD : D.Valid (Shearer.dependencyGraph P.footprint)) (u : WNode ι)
    (hu : u ∈ D.nodes) :
    tableEvent P D.normalize (D.canonicalName u) = tableEvent P D u := by
  ext ω
  change tableState P D.normalize ω (D.canonicalName u) ∈ P.bad u.1 ↔
    tableState P D ω u ∈ P.bad u.1
  rw [tableState_normalize P D hD u hu ω]

theorem tableCheck_normalize (P : MTProcess S ι) (D : HLS.WitnessDAG ι)
    (hD : D.Valid (Shearer.dependencyGraph P.footprint)) :
    tableCheck P D.normalize = tableCheck P D := by
  ext ω
  simp only [tableCheck, Set.mem_iInter]
  constructor
  · intro h u hu
    have hname := (normalize_node_iff D _).mpr ⟨u, hu, rfl⟩
    simpa only [tableEvent_normalize P D hD u hu] using h (D.canonicalName u) hname
  · intro h x hx
    obtain ⟨u, hu, hux⟩ := (normalize_node_iff D x).mp hx
    simpa only [← hux, tableEvent_normalize P D hD u hu] using h u hu

end HLS.WitnessDAG

#check @HLS.WitnessDAG.priorReaders_normalize
#check @HLS.WitnessDAG.localIndex_normalize
#check @HLS.WitnessDAG.tableState_normalize
#check @HLS.WitnessDAG.tableEvent_normalize
#check @HLS.WitnessDAG.tableCheck_normalize
